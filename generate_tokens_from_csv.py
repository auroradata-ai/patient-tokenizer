import csv
from pathlib import Path
from patient_tokenizer import PatientTokenizer

input_csv = "Names_2010Census.csv"
output_csv = "output.csv"
secret_salt = "salt123"

def process_csv(input_csv: str, output_csv: str, secret_salt: str):
    """
    Reads an input CSV, generates tokens, and writes the output to a new CSV.

    Args:
        input_csv (str): Path to the input CSV file.
        output_csv (str): Path to the output CSV file.
        secret_salt (str): Secret salt for the PatientTokenizer.
    """
    tokenizer = PatientTokenizer(secret_salt=secret_salt)

    with open(input_csv, newline='', encoding='utf-8') as infile, \
         open(output_csv, mode='w', newline='', encoding='utf-8') as outfile:
        
        reader = csv.DictReader(infile)
        fieldnames = ['first_name', 'last_name', 'dob', 'sex', 'zipcode', 'token']
        writer = csv.DictWriter(outfile, fieldnames=fieldnames)
        writer.writeheader()

        for row in reader:
            # Extract relevant fields
            if 'first_name' in row and 'last_name' in row:
                first_name = row.get('first_name', '').strip()
                last_name = row.get('last_name', '').strip()
            elif 'name' in row:
                full_name = row.get('name', '').strip().split()
                if len(full_name) > 1:
                    first_name = full_name[0]
                    last_name = full_name[1]
                else:
                    first_name = full_name[0] if full_name else ''
                    last_name = ''
            else:
                first_name = ''
                last_name = ''

            dob = row.get('dob', None)
            sex = row.get('sex', None)
            zipcode = row.get('zipcode', None)

            # Generate token
            token = tokenizer.tokenize(
                first_name=first_name,
                last_name=last_name,
                dob=dob,
                sex=sex,
                zipcode=zipcode
            )

            # Write to output CSV
            writer.writerow({
                'first_name': first_name,
                'last_name': last_name,
                'dob': dob,
                'sex': sex,
                'zipcode': zipcode,
                'token': token
            })

process_csv(input_csv, output_csv, secret_salt)
