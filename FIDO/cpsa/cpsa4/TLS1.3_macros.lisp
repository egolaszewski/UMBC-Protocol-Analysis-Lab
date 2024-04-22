;; TLS 1.3 macros for both server-only authentication and mutual authentication.

(defmacro (DHpublic exponent)
    (exp (gen) exponent))

;; Initial Hello messages provide values for key derivation (the only
;; unencrypted messages in the protocol). key_share can be a Diffie_Hellman
;; value, Pre-Shared Key (PSK) or both. We model using Diffie_Hellman.

(defmacro (ClientHello random exponent)
    (cat random (DHpublic exponent))) ;; key_share is DHpublic

(defmacro (ServerHello random exponent)
    (cat random (DHpublic exponent))) ;; key_share is DHpublic

;; Secret Derivation

(defmacro (HandshakeSecret key_share exponent)
    (exp key_share exponent))

(defmacro (MasterSecret secret)
    (hash secret "derived"))

;; Key derivations from computed secrets

(defmacro (ClientHandshakeKey client_random server_random secret)
    (hash secret "c hs traffic" client_random server_random)) 

(defmacro (ServerHandshakeKey client_random server_random secret)
    (hash secret "s hs traffic" client_random server_random)) 

;; simplified ApKey derivation, used by the applications for encryption (actual
;; derivation would include all messages received in the hash.)

(defmacro (ServerApKey client_random server_random master_secret)
    (hash "s ap traffic" client_random server_random master_secret)) 

(defmacro (ClientApKey client_random server_random master_secret)
    (hash "c ap traffic" client_random server_random master_secret)) 

(defmacro (finish_key key) ;; MAC key for the Finished message
    (hash "finished" key)) ;; uses handshake key

;; Encrypted handshake messages

(defmacro (Certificate party publickey ca)
    (cat party publickey (enc (hash party publickey) (privk ca))))

(defmacro (CertificateVerify messages key)
    (enc (hash messages) key))

(defmacro (ServerCertVerifyMesgs client_random server_random client_expt
				 server_expt server serverpubkey ca)
    (^
     (ClientHello client_random client_expt)
     (ServerHello server_random server_expt)
     (Certificate server serverpubkey ca)))

(defmacro (ClientCertVerifyMesgs client_random server_random client_expt
				 server_expt server serverpubkey serverprivkey
				 client clientpubkey ca handshakesecret)
    (^
     (ServerCertVerifyMesgs client_random server_random client_expt server_expt
			    server serverpubkey ca)
     (CertificateVerify
      (ServerCertVerifyMesgs client_random server_random client_expt server_expt
			     server serverpubkey ca)
      serverprivkey)
     (Finish
      (ServerFinishedMesgs client_random server_random server_expt client_expt
			   server serverpubkey serverprivkey ca)
      (ServerHandshakeKey client_random server_random handshakesecret))
     (Certificate client clientpubkey ca)))
     
(defmacro (Finish messages key)
    (hash (finish_key key) messages))

(defmacro (ServerFinishedMesgs client_random server_random client_expt
			       server_expt server serverpubkey serverprivkey ca)
    (^
     (ServerCertVerifyMesgs client_random server_random client_expt server_expt
			    server serverpubkey ca)
     (CertificateVerify
      (ServerCertVerifyMesgs client_random server_random client_expt server_expt
			     server serverpubkey ca)
      serverprivkey)))

(defmacro (ClientFinishedMesgs_nocert client_random server_random client_expt
				      server_expt server serverpubkey
				      serverprivkey ca handshakesecret)
    (^
     (ServerFinishedMesgs client_random server_random client_expt server_expt
			  server serverpubkey serverprivkey ca)
     (Finish
      (ServerFinishedMesgs client_random server_random client_expt server_expt
			   server serverpubkey serverprivkey ca)
      (ServerHandshakeKey client_random server_random handshakesecret))))

(defmacro (ClientFinishedMesgs client_random server_random client_expt
			       server_expt server serverpubkey serverprivkey
			       client clientpubkey clientprivkey ca
			       handshakesecret)
    (^
     (ClientCertVerifyMesgs client_random server_random client_expt server_expt
			    server serverpubkey serverprivkey client
			    clientpubkey ca handshakesecret)
     (CertificateVerify
      (ClientCertVerifyMesgs client_random server_random client_expt server_expt
			     server serverpubkey serverprivkey client
			     clientpubkey ca handshakesecret)
      clientprivkey)))
				     

;; TLS macros: Server Authentication (TLS) and Mutual Authentication (mTLS)

;; Notes on using the macros. d1 and d2 are direction and are replaced with
;; send and receive, depending upon whether it is the client and the server. The
;; handshakesecret exists as the client and the server compute the secret in
;; different ways. The handshakesecret should be replaced with the correct secret
;; computation for the given role. For a client with a client_random variable of
;; x and the server_random variable of y with client_random of cr and
;; server_random of sr, the handshakesecret = (HandshakeSecret (DHpublic y) x).
;; For the server it will be (HandshakeSecret (DHpublic x) y).

;; TLS with Server Authentication only (Handshake Protocol)
(defmacro (TLS d1 d2 client_random server_random client_expt server_expt server
	       serverpubkey serverprivkey ca handshakesecret)
    (^
     (d1 (ClientHello client_random client_expt))
     (d2 (cat (ServerHello server_random server_expt)
	      (enc (Certificate server serverpubkey ca)
		   (CertificateVerify
		    (ServerCertVerifyMesgs client_random server_random
					   client_expt server_expt server
					   serverpubkey ca)
		    serverprivkey)
		   (Finish
		    (ServerFinishedMesgs client_random server_random client_expt
				       server_expt server serverpubkey
				       serverprivkey ca)
		    (ServerHandshakeKey client_random server_random
					handshakesecret))
		   (ServerHandshakeKey client_random server_random
				       handshakesecret))))
     (d1 (enc (Finish
	       (ClientFinishedMesgs_nocert client_random server_random
					   client_expt server_expt server
					   serverpubkey serverprivkey ca
					   handshakesecret)
	       (ClientHandshakeKey client_random server_random handshakesecret))
	      (ClientHandshakeKey client_random server_random
				  handshakesecret)))))

;; Mutual TLS (Handshake Protocol)
(defmacro (mTLS d1 d2 client_random server_random client_expt server_expt server
		serverpubkey serverprivkey client clientpubkey clientprivkey ca
		handshakesecret)
    (^
     (d1 (ClientHello client_random client_expt))
     (d2 (cat (ServerHello server_random server_expt)
	      (enc (Certificate server serverpubkey ca)
		   (CertificateVerify
		    (ServerCertVerifyMesgs client_random server_random
					   client_expt server_expt server
					   serverpubkey ca)
		    serverprivkey)
		   (Finish
		    (ServerFinishedMesgs client_random server_random client_expt
				       server_expt server serverpubkey
				       serverprivkey ca)
		    (ServerHandshakeKey client_random server_random
					handshakesecret))
		   (ServerHandshakeKey client_random server_random
				       handshakesecret))))
     (d1 (enc (Certificate client clientpubkey ca)
	      (CertificateVerify
	       (ClientCertVerifyMesgs client_random server_random client_expt
				      server_expt server serverpubkey
				      serverprivkey client clientpubkey ca
				      handshakesecret)
	       clientprivkey)
	      (Finish
	       (ClientFinishedMesgs client_random server_random client_expt
				    server_expt server serverpubkey serverprivkey
				    client clientpubkey clientprivkey ca
				    handshakesecret)
	       (ClientHandshakeKey client_random server_random handshakesecret))
	      (ClientHandshakeKey client_random server_random
				  handshakesecret)))))
