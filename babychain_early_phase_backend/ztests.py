from hashlib import sha256
import json
from collections import OrderedDict

import binascii
import Crypto.Random
from Crypto.Hash import SHA
from Crypto.PublicKey import RSA
from Crypto.Signature import PKCS1_v1_5

random_gen = Crypto.Random.new().read
private_key = RSA.generate(1024, random_gen)
public_key = private_key.publickey()
signer = PKCS1_v1_5.new(private_key)

message = 'To be signed'
h = SHA.new(message.encode())
signature = signer.sign(h)
print("signature string is:", binascii.hexlify(signature).decode('utf-8'))

public_key_encoded_string = binascii.hexlify(public_key.exportKey(format='DER')).decode('utf-8')
public_key_new_copy = RSA.import_key(binascii.unhexlify(public_key_encoded_string))
verifier = PKCS1_v1_5.new(public_key_new_copy)

if verifier.verify(h, signature):
    print("The signature is authentic.")