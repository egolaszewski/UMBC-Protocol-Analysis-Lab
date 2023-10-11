(defmacro (ClientHello random)
    random)

(defmacro (ServerHello random)
    random)

(defmacro (Certificate id ca)
    (cat id (pubk id) (enc (hash id (pubk id)) (privk ca))))

(defmacro (ClientKeyExchange pre_master_secret server)
    (enc pre_master_secret (pubk server)))

(defmacro (MasterSecret pre_master_secret client_random server_random)
    (hash pre_master_secret client_random server_random))

(defmacro (ClientWriteKey master_secret)
    (hash master_secret "client_write"))

(defmacro (ServerWriteKey master_secret)
    (hash master_secret "server_write"))

(defmacro (clientTLSmesgsCommon client_random server_random server ca)
    (^
     (ClientHello client_random)
     (ServerHello server_random)
     (Certificate server ca)))

(defmacro (CertificateVerifymesgs pre_master_secret client_random server_random client server ca)
    (^
     (clientTLSmesgsCommon client_random server_random server ca)
     (Certificate client ca)
     (ClientKeyExchange pre_master_secret server)))

(defmacro (CertificateVerify pre_master_secret client_random server_random client server ca)
    (enc
     (hash
      (CertificateVerifymesgs pre_master_secret client_random server_random client server ca))
     (privk client)))

(defmacro (ClientFinishmesgs_ncc pre_master_secret client_random server_random server ca)
    (^
     (clientTLSmesgsCommon client_random server_random server ca)
     (ClientKeyExchange pre_master_secret server)))

(defmacro (ClientFinishmesgs_cc pre_master_secret client_random server_random client server ca)
    (^
     (CertificateVerifymesgs pre_master_secret client_random server_random client server ca)
     (CertificateVerify pre_master_secret client_random server_random client server ca)))

(defmacro (ClientFinish_ncc pre_master_secret client_random server_random server ca)
    (enc
     (hash pre_master_secret "client finished"
	   (hash
	    (ClientFinishmesgs_ncc pre_master_secret client_random server_random server ca)))
     (ClientWriteKey (MasterSecret pre_master_secret client_random server_random))))
     
(defmacro (ClientFinish_cc pre_master_secret client_random server_random client server ca)
    (enc
     (hash pre_master_secret "client finished"
	   (hash
	    (ClientFinishmesgs_cc pre_master_secret client_random server_random client server ca)))
     (ClientWriteKey (MasterSecret pre_master_secret client_random server_random))))
     
(defmacro (ServerFinish_ncc pre_master_secret client_random server_random server ca)
    (enc
     (hash pre_master_secret "server finished"
	   (hash
	    (ClientFinishmesgs_ncc pre_master_secret client_random server_random server ca)
	    (ClientFinish_ncc pre_master_secret client_random server_random server ca)))
     (ServerWriteKey (MasterSecret pre_master_secret client_random server_random))))

(defmacro (ServerFinish_cc pre_master_secret client_random server_random client server ca)
    (enc
     (hash pre_master_secret "server finished"
	   (hash
	    (ClientFinishmesgs_cc pre_master_secret client_random server_random client server ca)
	    (ClientFinish_cc pre_master_secret client_random server_random client server ca)))
     (ServerWriteKey (MasterSecret pre_master_secret client_random server_random))))

(defmacro (TLS d1 d2 pre_master_secret client_random server_random server ca)
    (^
     (d1 (ClientHello client_random))
     (d2 (cat (ServerHello server_random)
	 (Certificate server ca)))
     (d1 (cat (ClientKeyExchange pre_master_secret server)
	 (ClientFinish_ncc pre_master_secret client_random server_random server ca)))
     (d2 (ServerFinish_ncc pre_master_secret client_random server_random server ca))))

(defmacro (mTLS d1 d2 pre_master_secret client_random server_random client server ca)
    (^
     (d1 (ClientHello client_random))
     (d2 (cat (ServerHello server_random)
	 (Certificate server ca)))
     (d1 (cat (Certificate client ca)
	 (ClientKeyExchange pre_master_secret server)
	 (CertificateVerify pre_master_secret client_random server_random client server ca)
	 (ClientFinish_cc pre_master_secret client_random server_random client server ca)))
     (d2 (ServerFinish_cc pre_master_secret client_random server_random client server ca))))

; Channels used to put TLS connection on a private network

(defmacro (TLSprvt d1 d2 ch pre_master_secret client_random server_random server ca)
    (^
     (d1 ch (ClientHello client_random))
     (d2 ch (cat (ServerHello server_random)
	 (Certificate server ca)))
     (d1 ch (cat (ClientKeyExchange pre_master_secret server)
	 (ClientFinish_ncc pre_master_secret client_random server_random server ca)))
     (d2 ch (ServerFinish_ncc pre_master_secret client_random server_random server ca))))

(defmacro (mTLSprvt d1 d2 ch pre_master_secret client_random server_random client server ca)
    (^
     (d1 ch (ClientHello client_random))
     (d2 ch (cat (ServerHello server_random)
	 (Certificate server ca)))
     (d1 ch (cat (Certificate client ca)
	 (ClientKeyExchange pre_master_secret server)
	 (CertificateVerify pre_master_secret client_random server_random client server ca)
	 (ClientFinish_cc pre_master_secret client_random server_random client server ca)))
     (d2 ch (ServerFinish_cc pre_master_secret client_random server_random client server ca))))

