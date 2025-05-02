# patient-tokenizer

To evaluate the recall of the tokenizer, run

```
  python patient_tokenizer.py eval --n 20000
```

To tokenize a patient, run

```
  export PT_SALT=“do-some-dumbo-string-here”
  python patient-tokenizer.py tokenize \
      --first_name "Austin" \
      --last_name "Wang" \
      --dob 2003-01-15 \
      --sex M \
      --zip 10000
```
