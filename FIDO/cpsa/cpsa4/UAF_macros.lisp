;;; Macro for creating signed UAF attestations.
(defmacro (UAF_Attestation vals key)
    (cat vals (enc vals key)))
    
;;; Macro for creating key handles.
(defmacro (UAF_KH key uname)
  (hash "key handle" key uname))

;; The following macro is a shortcut to create the TLS master secret.
(defmacro (MS exponent1 exponent2)
  (MasterSecret (HandshakeSecret (DHpublic exponent1) exponent2)))

;;; FIDO UAF Macros
;;;
;;; Role variables:
;;; appid (name): the identifier for the relying party's application.
;;; challenge (text): the cryptographic challenge for attestation.
;;; authk (akey): the authenticator's asymmetric attestation key.
;;; username (name, registration only): the identifier of the user that authenticates.
;;; auth (name, registration only): the identifier of the user's authenticator---also known as the aaid.
;;;
;;; Macro variables:
;;; cwk: the TLS client write key.
;;; swk: the TLS server write key.

(defmacro (UAF_RegChallenge username appid challenge swk)
  (enc username appid challenge swk))

(defmacro (UAF_RegResponse username appid fcp auth authk binding cwk)
  (enc 
    (UAF_KH (invk authk) username)
    (UAF_Attestation (cat auth authk (hash appid challenge binding))
  (invk authk)) cwk))

(defmacro (UAF_AuthChallenge appid challenge swk)
  (enc appid challenge swk))
  
(defmacro (UAF_AuthResponse challenge appid authk binding cwk)
  (enc (UAF_Attestation (hash appid binding challenge) (invk authk)) cwk))

(defmacro (UAF_Registration d1 d2 username appid challenge auth authk binding cwk swk)
  (^
    (d2 (UAF_RegChallenge username appid challenge swk))
    (d1 (UAF_RegResponse username appid challenge auth authk binding cwk))))

(defmacro (UAF_Authentication d1 d2 appid challenge authk binding cwk swk)
  (^
    (d2 (UAF_AuthChallenge appid challenge swk))
    (d1 (UAF_AuthResponse challenge appid authk binding cwk))))

;;; Channel binding macros.

(defmacro (UAF_ChannelID challenge client)
  (hash "uaf_channel_id" challenge (pubk client) (enc (pubk client) (privk client))))

(defmacro (UAF_TokenBinding challenge client)
  (hash "uaf_token_binding" challenge (cat (pubk client) (enc (pubk client) (privk client)))))

(defmacro (UAF_ServerEndPoint challenge server ca)
  (hash "uaf_server_endpoint" challenge (hash (Certificate server ca))))

(defmacro (UAF_ServerCert challenge server ca)
  (hash "uaf_server_cert" challenge (Certificate server ca)))
  
;;; TLS Exporter PRF. We approximate this with a hash function.
(defmacro (UAF_Exporter ms label cr sr ctx)
  (hash ms label cr sr ctx))

;;; FIDO UAF TLS 1.2 macros.
;;;
;;; Requires TLS1.2_macros.lisp
;;;
;;; Required variables:
;;; [See UAF macros]
;;; cr, sr (random32): client and server random values for TLS 1.2.
;;; pms (random48): client's pre-master secret for TLS 1.2.
;;;
;;; Required for ChannelID and TokenBinding:
;;; client (name): the identifier of the client.
;;;
;;; Required for ServerEndPoint and ServerCert:
;;; server (name): the identifier of the server.
;;; ca (name): the identifier of the certificate authority.

(defmacro (UAF_Reg_TLS12 d1 d2 username appid challenge auth authk cr sr pms binding)
  (UAF_Registration d1 d2 username appid challenge auth authk binding
    (ClientWriteKey (MasterSecret pms cr sr))
    (ServerWriteKey (MasterSecret pms cr sr))))
    
(defmacro (UAF_Auth_TLS12 d1 d2 appid challenge authk cr sr pms binding)
  (UAF_Authentication d1 d2 appid challenge authk binding
    (ClientWriteKey (MasterSecret pms cr sr))
    (ServerWriteKey (MasterSecret pms cr sr))))

(defmacro (UAF_Reg_Unbound_TLS12 d1 d2 username appid challenge auth authk cr sr pms)
  (UAF_Reg_TLS12 d1 d2 username appid challenge auth authk cr sr pms "unbound"))

(defmacro (UAF_Auth_Unbound_TLS12 d1 d2 appid challenge authk cr sr pms)
  (UAF_Auth_TLS12 d1 d2 appid challenge authk cr sr pms "unbound"))

(defmacro (UAF_Reg_ChannelID_TLS12 d1 d2 client username appid challenge auth authk cr sr pms)
  (UAF_Reg_TLS12 d1 d2 username appid challenge auth authk cr sr pms
    (UAF_ChannelID challenge client)))

(defmacro (UAF_Auth_ChannelID_TLS12 d1 d2 client appid challenge authk cr sr pms)
  (UAF_Auth_TLS12 d1 d2 appid challenge authk cr sr pms
    (UAF_ChannelID challenge client)))

(defmacro (UAF_Reg_TokenBinding_TLS12 d1 d2 client username appid challenge auth authk cr sr pms)
  (UAF_Reg_TLS12 d1 d2 username appid challenge auth authk cr sr pms
    (UAF_TokenBinding challenge client)))

(defmacro (UAF_Auth_TokenBinding_TLS12 d1 d2 client appid challenge authk cr sr pms)
  (UAF_Auth_TLS12 d1 d2 appid challenge authk cr sr pms
    (UAF_TokenBinding challenge client)))

(defmacro (UAF_Reg_EndPoint_TLS12 d1 d2 server ca username appid challenge auth authk cr sr pms)
  (UAF_Reg_TLS12 d1 d2 username appid challenge auth authk cr sr pms
    (UAF_ServerEndPoint challenge server ca)))

(defmacro (UAF_Auth_EndPoint_TLS12 d1 d2 server ca appid challenge authk cr sr pms)
  (UAF_Auth_TLS12 d1 d2 appid challenge authk cr sr pms
    (UAF_ServerEndPoint challenge server ca)))
    
(defmacro (UAF_Reg_ServerCert_TLS12 d1 d2 server ca username appid challenge auth authk cr sr pms)
  (UAF_Reg_TLS12 d1 d2 username appid challenge auth authk cr sr pms
    (UAF_ServerCert challenge server ca)))

(defmacro (UAF_Auth_ServerCert_TLS12 d1 d2 server ca appid challenge authk cr sr pms)
  (UAF_Auth_TLS12 d1 d2 appid challenge authk cr sr pms
    (UAF_ServerCert challenge server ca)))

;;; FIDO UAF TLS 1.3 macros.
;;;
;;; Requires TLS1.3_macros.lisp
;;;
;;; Required variables:
;;; [See UAF macros]
;;; cr, sr (random32): client and server random values for TLS 1.3.
;;; spk (akey): the server public key.
;;; x (expt/rndx): the sender's DH secret for TLS 1.3.
;;; y (expt/rndx): the receivers's DH secret for TLS 1.3.
;;;
;;; Note that when using these macros, you must reverse x and y for the client and the server.

(defmacro (UAF_Reg_TLS13 d1 d2 username appid challenge auth authk cr sr spk x y binding)
  (UAF_Registration d1 d2 username appid challenge auth authk binding
    (ClientApKey cr sr (MS y x))
    (ServerApKey cr sr (MS y x))))
    
(defmacro (UAF_Auth_TLS13 d1 d2 appid challenge authk cr sr spk x y binding)
  (UAF_Authentication d1 d2 appid challenge authk binding
    (ClientApKey cr sr (MS y x))
    (ServerApKey cr sr (MS y x))))

(defmacro (UAF_Reg_Unbound_TLS13 d1 d2 username appid challenge auth authk cr sr spk x y)
  (UAF_Reg_TLS13 d1 d2 username appid challenge auth authk cr sr spk x y "unbound"))

(defmacro (UAF_Auth_Unbound_TLS13 d1 d2 appid challenge authk cr sr spk x y)
  (UAF_Auth_TLS13 d1 d2 appid challenge authk cr sr spk x y "unbound"))

(defmacro (UAF_Reg_Exporter_TLS13 d1 d2 username appid challenge auth authk cr sr spk x y)
  (UAF_Reg_TLS13 d1 d2 username appid challenge auth authk cr sr spk x y
    (UAF_Exporter (MS x y) "uaf-exporter-binding" cr sr challenge)))

(defmacro (UAF_Auth_Exporter_TLS13 d1 d2 appid challenge authk cr sr spk x y)
  (UAF_Auth_TLS13 d1 d2 appid challenge authk cr sr spk x y
    (UAF_Exporter (MS x y) "uaf-exporter-binding" cr sr challenge)))