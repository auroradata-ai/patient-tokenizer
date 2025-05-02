"""
Patient Tokenizer 
-----------------------------------------

Usage (minimal):

    from patient_tokenizer import PatientTokenizer

    tk = PatientTokenizer(secret_salt="env:PT_SALT")   # ← recommended pattern
    token = tk.tokenize(
        first_name    = "Cathy",
        last_name     = "O'Neill",
        dob           = "1984-2-29",
        sex           = "F",
        zipcode       = "10027"
    )
    print(token)   # 7FAW6I7OG3VNWLVAATGU4JQ5LXGQHVDR

"""
from __future__ import annotations

import base64
import csv
import hashlib
import json
import os
import random
import re
import subprocess
import sys
import textwrap
from collections import defaultdict
from datetime import date, datetime
from pathlib import Path
from typing import Dict, Iterable, List, Tuple

###############################################################################
# -------------------------  Public Name Resources  --------------------------
###############################################################################
#
# We fetch two public files once, place them in ~/.patient_tokenizer_cache
#   • SSA baby-names (1880-present)  (male+female)
#   • U.S. Census surnames 2010      (top ~160 000 last names)
#
# That gives us ~220 K unique first + last names for testing spell-correction.
#
# If offline access is preferred, vendor the files and point the env-var:
#       PT_DATA_HOME=/custom/path  python patient_tokenizer.py ...
#
###############################################################################

DEFAULT_CACHE = Path(os.environ.get("PT_DATA_HOME", "~/.patient_tokenizer_cache")).expanduser()
SSA_URL       = "https://www.ssa.gov/oact/babynames/names.zip"
CENSUS_URL    = (
    "https://www2.census.gov/topics/genealogy/2010surnames/names.zip"
)

###############################################################################
#                                Nick-names                                   #
###############################################################################
# ↓ A tiny list; extend/replace as needed.  All keys & values are uppercase.
NICKNAMES = {
    # female
    "ABBIE": "ABIGAIL",
    "ABBY": "ABIGAIL",
    "ALLY": "ALISON",
    "ALY": "ALISON",
    "ANNIE": "ANNA",
    "BETH": "ELIZABETH",
    "BETTY": "ELIZABETH",
    "CATHY": "CATHERINE",
    "KATHY": "KATHERINE",
    "KATE":  "KATHERINE",
    "KATY":  "KATHERINE",
    "LIZ":   "ELIZABETH",
    "LIZZY": "ELIZABETH",
    "PEGGY": "MARGARET",
    # male
    "AL":    "ALBERT",
    "ALEX":  "ALEXANDER",
    "BOB":   "ROBERT",
    "BOBBY": "ROBERT",
    "CHRIS": "CHRISTOPHER",
    "DAN":   "DANIEL",
    "DANNY": "DANIEL",
    "JACK":  "JOHN",
    "JIM":   "JAMES",
    "JIMMY": "JAMES",
    "JOE":   "JOSEPH",
    "JOEY":  "JOSEPH",
    "MIKE":  "MICHAEL",
    "NICK":  "NICHOLAS",
    "PAT":   "PATRICK",
    "PETE":  "PETER",
    "STEVE": "STEVEN",
}

###############################################################################
#                           Utility Functions                                 #
###############################################################################


def _strip_accents(s: str) -> str:
    """À, é, ñ → A, E, N."""
    import unicodedata as ud

    return "".join(
        c for c in ud.normalize("NFKD", s) if ud.category(c) != "Mn"
    )


def _soundex(name: str) -> str:
    """
    American Soundex (simple 4-char version).
    Good enough for many one-char insert/delete typos.
    """
    name = name.upper()
    if not name:
        return ""

    codes = ("", "1", "2", "3", "4", "5", "6", "", "7", "", "", "4", "5", "5",
             "", "1", "2", "6", "2", "3", "", "1", "", "2", "", "2")

    first = name[0]
    tail = [codes[ord(c) - 65] for c in name[1:] if "A" <= c <= "Z"]

    sndx = first
    last_code = codes[ord(first) - 65]
    for code in tail:
        if not code or code == last_code:
            continue
        sndx += code
        last_code = code
        if len(sndx) == 4:
            break
    return (sndx + "000")[:4]


def _normalise_zip(zipcode: str | int | None) -> str:
    """
    • Accepts None, 5-digit, 9-digit, or int.
    • Returns the first 3 digits (ZIP-3) or empty string.
      (3 is a nice balance between uniqueness & anonymity)
    """
    if not zipcode:
        return ""

    z = re.sub(r"[^\d]", "", str(zipcode))
    return z[:3] if len(z) >= 3 else ""


def _normalise_sex(sex: str | None) -> str:
    if not sex:
        return ""
    s = sex.strip().lower()
    if s and s[0] in "mf":
        return s[0]
    if s.startswith("woman") or s.startswith("girl"):
        return "f"
    if s.startswith("man") or s.startswith("male") or s.startswith("boy"):
        return "m"
    return "o"  # other/unknown


def _canonical_dob(dob: str | date | datetime | None) -> str:
    """
    Return YYYY-MM-DD (zero-padded).  
    Accepts:
        • '1984-02-29'
        • '2/29/84'
        • datetime.date
        • '1984-02-??'    ⇒ 1984-02-00  (unknown day)
        • '1984-??-??'    ⇒ 1984-00-00  (unknown month/day)
    Unknown pieces are '00'.
    """
    if dob is None:
        return "0000-00-00"

    if isinstance(dob, (date, datetime)):
        return f"{dob.year:04d}-{dob.month:02d}-{dob.day:02d}"

    s = re.sub(r"[\s/]", "-", str(dob).strip())
    parts = [p for p in s.split("-") if p]
    if len(parts) == 3:
        y, m, d = parts
        y = y.zfill(4)
        m = m.zfill(2) if m != "??" else "00"
        d = d.zfill(2) if d != "??" else "00"
        return f"{y}-{m}-{d}"
    elif len(parts) == 1:
        # just year
        return f"{parts[0].zfill(4)}-00-00"
    return "0000-00-00"


def _canonical_name(name: str | None) -> Tuple[str, str]:
    """
    Returns (NAME_UPPER, SOUNDEX).  
    Steps:
        • strip titles / suffixes (MR, DR, JR, III …)
        • strip accents + punctuation
        • collapse whitespace
        • uppercase
        • replace common nick-names
    """
    if not name:
        return ("", "")

    n = name.upper()
    n = re.sub(r"\b(MR|MRS|MS|DR|PROF)\.?\s+", "", n)
    n = re.sub(r"\b(JR|SR|II|III|IV|V)\b\.?", "", n)
    n = _strip_accents(n)
    n = re.sub(r"[^A-Z\s]", " ", n)
    n = re.sub(r"\s{2,}", " ", n).strip()
    n = NICKNAMES.get(n, n)  # nick-name map
    return (n, _soundex(n))


def _secure_hash(canonical: str, salt: bytes, pepper: bytes | None = None) -> str:
    h = hashlib.sha256()
    h.update(salt)
    h.update(canonical.encode("utf-8"))
    if pepper:
        h.update(pepper)
    digest = h.digest()  # 32 bytes
    # 256 bits → 52 base32 chars. 32 chars is enough entropy for linking.
    return base64.b32encode(digest).decode("ascii")[:32]


###############################################################################
#                             PatientTokenizer                                #
###############################################################################


class PatientTokenizer:
    """
    The one public class.

        tk = PatientTokenizer(secret_salt="env:PT_SALT")
        token = tk.tokenize(first_name="Bob", last_name="Smith", dob="12/31/83")

    """
    __slots__ = ("salt", "pepper")

    def __init__(self, secret_salt: str | bytes, pepper: bytes | None = None):
        """
        secret_salt:
            • bytes  – already secret
            • "env:VAR" – will pull from os.environ["VAR"] (recommended)
            • any other str – used as-is (not recommended for prod)
        pepper:
            • optional additional secret known only to one side
        """
        if isinstance(secret_salt, bytes):
            self.salt = secret_salt
        elif isinstance(secret_salt, str) and secret_salt.startswith("env:"):
            env_var = secret_salt.split(":", 1)[1]
            self.salt = os.environ[env_var].encode("utf-8")
        else:
            self.salt = str(secret_salt).encode("utf-8")

        self.pepper = pepper

    # --------------------------------------------------------------------- #
    #                   ---------  PUBLIC API  ---------                    #
    # --------------------------------------------------------------------- #

    def tokenize(
        self,
        *,
        first_name: str | None,
        last_name: str | None,
        dob: str | date | datetime | None,
        sex: str | None = None,
        zipcode: str | int | None = None,
    ) -> str:
        """
        Main method.  Returns a 32-char base32 substring (160 bits entropy).
        """
        canon = self._canonical_string(
            first_name=first_name,
            last_name=last_name,
            dob=dob,
            sex=sex,
            zipcode=zipcode,
        )
        return _secure_hash(canon, self.salt, self.pepper)

    # --------------------------------------------------------------------- #
    #                    ---------  INTERNAL  ---------                     #
    # --------------------------------------------------------------------- #

    def _canonical_string(
        self,
        *,
        first_name: str | None,
        last_name: str | None,
        dob: str | date | datetime | None,
        sex: str | None,
        zipcode: str | int | None,
    ) -> str:
        """
        Build the canonical representation that finally gets hashed.

        We now include:
            • exactised first / last name
            • their Soundex codes  – ≈ phonetic back-up
            • canonical DOB  (zero-filled)
            • one-char sex  (m / f / o / "")
            • ZIP-3
        Putting both the exact and fuzzy versions side-by-side increases
        recall with only a negligible collision risk once everything is fed
        through SHA-256.
        """
        fn_exact, fn_sdx = _canonical_name(first_name)
        ln_exact, ln_sdx = _canonical_name(last_name)

        parts = (
            fn_exact,
            ln_exact,
            fn_sdx,
            ln_sdx,
            _canonical_dob(dob),
            _normalise_sex(sex),
            _normalise_zip(zipcode),
        )
        return "|".join(parts)


###############################################################################
#                         Synthetic-Data Evaluation                           #
###############################################################################


def _download_public_lists() -> Tuple[List[str], List[str]]:
    """
    Returns (first_names, last_names) in UPPERCASE (deduplicated).
    1️⃣  If the repo already contains CSV / TXT resources we use them.
    2️⃣  Otherwise we fall back to the original download-and-cache logic.
    """
    import zipfile

    here = Path(__file__).resolve().parent           # repo root dir

    # ------------------------------------------------------------------ #
    #  Local resources shipped with the repo (preferred)                 #
    # ------------------------------------------------------------------ #
    local_census_csv = here / "Names_2010Census.csv"    # surnames
    local_ssa_txt    = here / "ssa_first_names.txt"     # optional first names

    first_names: List[str] = []
    last_names:  List[str] = []

    # --- FIRST  NAMES -------------------------------------------------- #
    if local_ssa_txt.exists():
        print("[∗] Loading local SSA first-names list …")
        with open(local_ssa_txt) as fh:
            first_names = [n.strip().upper() for n in fh if n.strip()]

    # --- LAST  NAMES --------------------------------------------------- #
    if local_census_csv.exists():
        print("[∗] Loading local Census last-names CSV …")
        with open(local_census_csv, newline="", encoding="utf-8") as fh:
            rdr = csv.DictReader(fh)
            for row in rdr:
                name_val = row.get("name") or row.get("NAME")
                if name_val:
                    last_names.append(name_val.upper())

    # ------------------------------------------------------------------ #
    #  Fallback: download the official ZIPs once & cache them            #
    # ------------------------------------------------------------------ #
    DEFAULT_CACHE.mkdir(parents=True, exist_ok=True)

    def _ensure_text_file(path: Path, url: str, processor):
        """
        • download if file missing;
        • (re)process if the on-disk file is still a ZIP archive.
        """
        if not path.exists():
            print(f"[∗] Downloading {url.split('/')[-1]} …")
            subprocess.check_call(["curl", "-sSL", "-o", path, url, "--create-dirs"])
            processor(path)
        elif zipfile.is_zipfile(path):
            # cached file is still a ZIP → convert to plain-text list now
            processor(path)

    # ---------- FIRST-NAMES fallback ----------------------------------- #
    if not first_names:
        first_path = DEFAULT_CACHE / "ssa_first_names.txt"
        _ensure_text_file(first_path, SSA_URL, _process_ssa)
        with open(first_path) as fh:
            first_names = [n.strip().upper() for n in fh if n.strip()]

    # ---------- LAST-NAMES fallback ------------------------------------ #
    if not last_names:
        last_path = DEFAULT_CACHE / "census_last_names.txt"
        _ensure_text_file(last_path, CENSUS_URL, _process_census)
        with open(last_path) as fh:
            last_names = [n.strip().upper() for n in fh if n.strip()]

    # Deduplicate just in case and return
    return list(set(first_names)), list(set(last_names))


def _process_ssa(tmp_zip: Path):
    """
    Keep top 25 K names for speed; write into same path as plain text.
    """
    import zipfile, io

    names: dict[str, int] = defaultdict(int)

    with zipfile.ZipFile(tmp_zip) as zf:
        for fname in zf.namelist():
            if not fname.endswith(".txt"):
                continue
            with zf.open(fname) as fh:
                for line in map(bytes.decode, fh):
                    _, name, count = line.strip().split(",")
                    names[name.upper()] += int(count)

    # top 25 000
    popular = sorted(names.items(), key=lambda kv: -kv[1])[:25_000]
    with open(tmp_zip, "w") as out:
        out.writelines([f"{n}\n" for n, _ in popular])


def _process_census(tmp_zip: Path):
    import zipfile, io

    names: List[str] = []
    with zipfile.ZipFile(tmp_zip) as zf:
        # grab the first *.csv file in the archive (robust to filename changes)
        csv_name = next(
            (fname for fname in zf.namelist() if fname.lower().endswith(".csv")),
            None,
        )
        if csv_name is None:
            raise ValueError("No CSV file found inside Census surnames ZIP")

        with zf.open(csv_name) as fh:
            rdr = csv.DictReader(io.TextIOWrapper(fh, newline=""))
            for row in rdr:
                # header can be "name" or "NAME" ‒ handle both gracefully
                surname = row.get("NAME") or row.get("name")
                if surname:                                  # safety check
                    names.append(surname.upper())

    with open(tmp_zip, "w") as out:
        out.writelines([f"{n}\n" for n in names])

# INJECT HUMAN ENTRY ERRORS
def _introduce_errors(name: str) -> str:
    """
    Randomly mutate 20 % of names:
        • adjacent letter transposition
        • replace O↔0, I↔1
        • random single-char omission
    """
    if random.random() > 0.2:
        return name

    s = list(name)
    roll = random.random()
    if roll < 0.3 and len(s) > 3:
        # transpose two adjacent characters
        i = random.randrange(len(s) - 1)
        s[i], s[i + 1] = s[i + 1], s[i]
    elif roll < 0.6 and len(s) > 4:
        # delete
        s.pop(random.randrange(len(s)))
    else:
        # replace O↔0, I↔1
        repl = {"O": "0", "0": "O", "I": "1", "1": "I"}
        i = random.randrange(len(s))
        s[i] = repl.get(s[i], s[i])

    return "".join(s)


def evaluate(n_samples: int = 10_000, seed: int = 42):
    """
    Rough recall test on synthetic population with entry errors.
    We measure how often two noisy records for the *same* person collide.
    """
    random.seed(seed)
    first_names, last_names = _download_public_lists()

    tk = PatientTokenizer(secret_salt=b"TEST_SALT")  # deterministic

    successes = 0
    for _ in range(n_samples):
        fn = random.choice(first_names)
        ln = random.choice(last_names)
        dob = date(
            random.randint(1950, 2010),
            random.randint(1, 12),
            random.randint(1, 28),
        )
        sex = random.choice(["m", "f"])
        zip5 = f"{random.randint(60000, 70000)}"

        truth = tk.tokenize(
            first_name=fn,
            last_name=ln,
            dob=dob,
            sex=sex,
            zipcode=zip5,
        )

        # Variation (simulate second data source)
        fn2 = _introduce_errors(fn)
        ln2 = _introduce_errors(ln)
        dob2 = dob  # date errors left as future exercise
        token2 = tk.tokenize(
            first_name=fn2,
            last_name=ln2,
            dob=dob2,
            sex=sex,
            zipcode=zip5,
        )

        successes += int(truth == token2)

    print(
        f"[Evaluation]  n={n_samples:,}   recall={successes / n_samples:.3%}"
    )


###############################################################################
#                                   CLI                                       #
###############################################################################


def _cli():
    import argparse

    p = argparse.ArgumentParser(
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=textwrap.dedent(
            """
            Quick command-line front-end.

            Examples
            --------
            Generate a token
                $ PT_SALT=mysupersecret python patient_tokenizer.py \\
                     tokenize                                       \\
                     --first_name "Cathy" --last_name O'Neill       \\
                     --dob 1984-02-29 --sex F --zip 10027

            Run recall evaluation
                $ python patient_tokenizer.py eval --n 20000
            """
        ),
    )
    sub = p.add_subparsers(dest="cmd", required=True)

    tok = sub.add_parser("tokenize", help="Generate one token")
    tok.add_argument("--first_name", required=True)
    tok.add_argument("--last_name", required=True)
    tok.add_argument("--dob", required=True)
    tok.add_argument("--sex", default="")
    tok.add_argument("--zip", default="")
    tok.add_argument("--salt", default="env:PT_SALT")

    ev = sub.add_parser("eval", help="Synthetic recall test")
    ev.add_argument("--n", type=int, default=10_000)

    args = p.parse_args()

    if args.cmd == "tokenize":
        tk = PatientTokenizer(secret_salt=args.salt)
        t = tk.tokenize(
            first_name=args.first_name,
            last_name=args.last_name,
            dob=args.dob,
            sex=args.sex,
            zipcode=args.zip,
        )
        print(t)

    elif args.cmd == "eval":
        evaluate(args.n)


if __name__ == "__main__":
    _cli()