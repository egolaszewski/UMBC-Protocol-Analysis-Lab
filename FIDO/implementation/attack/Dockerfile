FROM python:3.9

ADD attack.py .

RUN pip install bcrypt requests cryptography

CMD ["python", "./attack.py"] 