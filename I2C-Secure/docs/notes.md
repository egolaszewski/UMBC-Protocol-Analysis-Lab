# I2CSec

## Purpose
I2C (Inter-Intergrated Circuit) Protocol for Chip-to-Chip communications. 

## I2C 
- Two wire
    - SDA ( Serial data)
    - SCL (Serial Clock)
- EAch device has a unique address
    - Microcontroller
    - LCD
    - Flash chip
- Clock generation is responsible by the master device speaking on the network

### (Video) How I2C write works
- https://youtu.be/UP0aeeuz65U?t=433

## AES-GCM
- Galois Field Multiplication can be used for authenciation
- Can be computed in parrallel
- Counter mode algorithm
    - What is encrypted is the counter, not the data
- Ecnryption and Decryption are done with the same circuit

Calculate H (factor)
- vector of 128 zeroes is encrypted using the K (key)

### (Website) AES-GCM Issues Explained:
- https://soatok.blog/2020/05/13/why-aes-gcm-sucks/

## Assumptions
- Basic I2C secure protocol
- Secrecy and Privacy of the system
- "One problem that arises when using this kind of networks is the secrecy and privacy of the system. In some critical control applications, knowing that data is coming from the sensor and not from a malicious user is critical" 
- Authenication
    - knowing that 'the sensor is really what we thing" 
    - 
- Encryption
    - Making converations secret 
- Claims that because we are using "field bus" protocols, that no matter how many security layers  we put on our Internet connections, an intruder can bypass them by gaining physical access"

- the length of the ciphertext is known by the advesary post message being sent (or intercepted)

# CPSA Simple Reference:
alg ← basic
sort ← text | data | name | tag | skey | akey
| chan | locn | mesg | id
id ← symbol
term ← id | (pubk id) | (privk id) | (invk id)
| (pubk id string) | (privk id string)
| (ltk id id) | string | (cat term+)
| (enc term+ term) | (hash term+)
| (id term+)


## States Reference:
https://github.com/mitre/cpsa/blob/master/tst/atomic-open-closed.scm

Explained Output:
    • encryption-test indicates that the critical term at the test node was an encryption.
    • nonce-test indicates that the critical term at the test node was an atom, not an
    encryption.
    • channel-test indicates that the critical term at the test node was an authenticated
    channel message.
    • generalization indicates that the skeleton was realized and the tool is trying to
    make it more general without making it unrealized.


# I2C-Secure Issues observed
Things to talk about:
- The avesary can know about the registers of a device basesd on the device schema
- The slave address is known to the world
- secondary-register-0? CPSA mentions that this value can me manipuated by the network??
- I customized the make file to open the shapes file (use: make open)
- N_EXEC, P_POV, S_POV can be used as search terms in the shapes file
-