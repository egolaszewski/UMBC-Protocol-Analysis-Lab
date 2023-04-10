(defmacro (ClientHello random)
    random)

(defmacro (ServerHello random)
    random)

(defmacro (Certificate id pubkeyid ca)
    (cat id pubkeyid (enc (hash id pubkeyid) (privk ca))))

(defmacro (ClientKeyExchange pre_master_secret pubkeyserver)
    (enc pre_master_secret pubkeyserver))

(defmacro (MasterSecret pre_master_secret client_random server_random)
    (hash pre_master_secret client_random server_random))

(defmacro (ClientWriteKey master_secret)
    (hash master_secret "client write"))

(defmacro (ServerWriteKey master_secret)
    (hash master_secret "server write"))

(defmacro (ClientFinish_nocerts client_random server_random pre_master_secret server pubkeyserver ca)
    (enc (hash pre_master_secret "client finished"
	       (hash (ClientHello client_random)
		     (ServerHello server_random)
		     (Certificate server pubkeyserver ca)
		     (ClientKeyExchange pre_master_secret pubkeyserver)))
	 (ClientWriteKey (MasterSecret pre_master_secret client_random server_random))))

(defmacro (ServerFinish_nocertreq client_random server_random pre_master_secret server pubkeyserver ca)
    (enc (hash pre_master_secret "server finished"
	       (hash (ClientHello client_random)
		     (ServerHello server_random)
		     (Certificate server pubkeyserver ca)
		     (ClientKeyExchange pre_master_secret pubkeyserver)
		     (ClientFinish_nocerts client_random server_random pre_master_secret server pubkeyserver ca)))
	 (ServerWriteKey (MasterSecret pre_master_secret client_random server_random))))

(defmacro (TLSclient_nocerts client_random server_random pre_master_secret server pubkeyserver ca)
    (^
     (send (ClientHello client_random))
     (recv (ServerHello server_random))
     (recv (Certificate server pubkeyserver ca))
     (send (ClientKeyExchange pre_master_secret pubkeyserver))
     (send (ClientFinish_nocerts client_random server_random pre_master_secret server pubkeyserver ca))
     (recv (ServerFinish_nocertreq client_random server_random pre_master_secret server pubkeyserver ca))))

(defmacro (TLSserver_nocertreq client_random server_random pre_master_secret server pubkeyserver ca)
    (^
     (recv (ClientHello client_random))
     (send (ServerHello server_random))
     (send (Certificate server pubkeyserver ca))
     (recv (ClientKeyExchange pre_master_secret pubkeyserver))
     (recv (ClientFinish_nocerts client_random server_random pre_master_secret server pubkeyserver ca))
     (send (ServerFinish_nocertreq client_random server_random pre_master_secret server pubkeyserver ca))))

(defmacro (CertificateVerify client_random server_random pre_master_secret client pubkeyclient server pubkeyserver ca)
    (enc
     (hash (ClientHello client_random)
	   (ServerHello server_random)
	   (Certificate server pubkeyserver ca)
	   (Certificate client pubkeyclient ca)
	   (ClientKeyExchange pre_master_secret pubkeyserver))
     (invk pubkeyclient)))

(defmacro (ClientFinish_certs client_random server_random pre_master_secret client pubkeyclient server pubkeyserver ca)
    (enc (hash pre_master_secret "client finished"
	       (hash (ClientHello client_random)
		     (ServerHello server_random)
		     (Certificate server pubkeyserver ca)
		     (Certificate client pubkeyclient ca)
		     (ClientKeyExchange pre_master_secret pubkeyserver)
		     (CertificateVerify client_random server_random pre_master_secret client pubkeyclient server pubkeyserver ca)))
	 (ClientWriteKey (MasterSecret pre_master_secret client_random server_random))))

(defmacro (ServerFinish_certreq client_random server_random pre_master_secret client pubkeyclient server pubkeyserver ca)
    (enc (hash pre_master_secret "server finished"
	       (hash (ClientHello client_random)
		     (ServerHello server_random)
		     (Certificate server pubkeyserver ca)
		     (Certificate client pubkeyclient ca)
		     (ClientKeyExchange pre_master_secret pubkeyserver)
		     (CertificateVerify client_random server_random pre_master_secret client pubkeyclient server pubkeyserver ca)
		     (ClientFinish_certs client_random server_random pre_master_secret client pubkeyclient server pubkeyserver ca)))
	 (ServerWriteKey (MasterSecret pre_master_secret client_random server_random))))

(defmacro (TLSclient_certs client_random server_random pre_master_secret client pubkeyclient server pubkeyserver ca)
    (^
     (send (ClientHello client_random))
     (recv (ServerHello server_random))
     (recv (Certificate server pubkeyserver ca)) ;; CertificateRequest message implied
     (send (Certificate client pubkeyclient ca))
     (send (ClientKeyExchange pre_master_secret pubkeyserver))
     (send (CertificateVerify client_random server_random pre_master_secret client pubkeyclient server pubkeyserver ca))
     (send (ClientFinish_certs client_random server_random pre_master_secret client pubkeyclient server pubkeyserver ca))
     (recv (ServerFinish_certreq client_random server_random pre_master_secret client pubkeyclient server pubkeyserver ca))))

(defmacro (TLSserver_certreq client_random server_random pre_master_secret client pubkeyclient server pubkeyserver ca)
    (^
     (recv (ClientHello client_random))
     (send (ServerHello server_random))
     (send (Certificate server pubkeyserver ca)) ;; CertificateRequest message implied
     (recv (Certificate client pubkeyclient ca))
     (recv (ClientKeyExchange pre_master_secret pubkeyserver))
     (recv (CertificateVerify client_random server_random pre_master_secret client pubkeyclient server pubkeyserver ca))
     (recv (ClientFinish_certs client_random server_random pre_master_secret client pubkeyclient server pubkeyserver ca))
     (send (ServerFinish_certreq client_random server_random pre_master_secret client pubkeyclient server pubkeyserver ca))))

