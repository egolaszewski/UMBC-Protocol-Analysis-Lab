(defmacro (ClientHello random)
    random)

(defmacro (ServerHello random)
    random)

(defmacro (Certificate id publickey ca)
    (cat id publickey (enc (hash id publickey) (privk ca))))

(defmacro (CertificateDH id exponent ca)
    (cat id (exp (gen) exponent) (enc (hash id (exp (gen) exponent))
				      (privk ca))))

(defmacro (ClientKeyExchange pre_master_secret server_pubk)
    (enc pre_master_secret server_pubk))

(defmacro (ClientKeyExchangeEDH exponent)
    (exp (gen) exponent))

(defmacro (ServerKeyExchangeEDH client_random server_random exponent server_pubk)
    (cat (exp (gen) exponent) (enc (hash client_random server_random
					 (exp (gen) exponent))
				   (invk server_pubk))))

(defmacro (MasterSecret pre_master_secret client_random server_random)
    (hash pre_master_secret client_random server_random))

(defmacro (ClientWriteKey master_secret)
    (hash master_secret "client_write"))

(defmacro (ServerWriteKey master_secret)
    (hash master_secret "server_write"))

(defmacro (clientTLSmesgsCommon client_random server_random server server_pubk
				ca)
    (^
     (ClientHello client_random)
     (ServerHello server_random)
     (Certificate server server_pubk ca)))

(defmacro (clientTLSmesgsCommonEDH client_random server_random exponent server
				   server_pubk ca)
    (^
     (ClientHello client_random)
     (ServerHello server_random)
     (Certificate server server_pubk ca)
     (ServerKeyExchangeEDH client_random server_random exponent server_pubk)))

(defmacro (CertificateVerifymesgs pre_master_secret client_random server_random
				  client client_pubk server server_pubk ca)
    (^
     (clientTLSmesgsCommon client_random server_random server server_pubk ca)
     (Certificate client client_pubk ca)
     (ClientKeyExchange pre_master_secret server_pubk)))

(defmacro (CertificateVerifymesgsEDH server_expt client_expt client_random
				     server_random client client_pubk server
				     server_pubk ca)
    (^
     (clientTLSmesgsCommonEDH client_random server_random server_expt server
			      server_pubk ca)
     (Certificate client client_pubk ca)
     (ClientKeyExchangeEDH client_expt)))

(defmacro (CertificateVerify pre_master_secret client_random server_random
			     client client_pubk server server_pubk ca)
    (enc
     (hash
      (CertificateVerifymesgs pre_master_secret client_random server_random
			      client client_pubk server server_pubk ca))
     (invk client_pubk)))

(defmacro (CertificateVerifyEDH server_expt client_expt client_random
				server_random client client_pubk server
				server_pubk ca)
    (enc
     (hash
      (CertificateVerifymesgsEDH server_expt client_expt client_random
				 server_random client client_pubk server
				 server_pubk ca))
     (invk client_pubk)))

(defmacro (ClientFinishmesgs_ncc pre_master_secret client_random server_random
				 server server_pubk ca)
    (^
     (clientTLSmesgsCommon client_random server_random server server_pubk ca)
     (ClientKeyExchange pre_master_secret server_pubk)))

(defmacro (ClientFinishmesgs_cc pre_master_secret client_random server_random
				client client_pubk server server_pubk ca)
    (^
     (CertificateVerifymesgs pre_master_secret client_random server_random
			     client client_pubk server server_pubk ca)
     (CertificateVerify pre_master_secret client_random server_random client
			client_pubk server server_pubk ca)))

(defmacro (ClientFinishmesgsEDH_ncc server_expt client_expt client_random
				    server_random server server_pubk ca)
    (^
     (clientTLSmesgsCommonEDH client_random server_random server_expt server
			      server_pubk ca)
     (ClientKeyExchangeEDH client_expt)))

(defmacro (ClientFinishmesgsEDH_cc server_expt client_expt client_random
				   server_random client client_pubk server
				   server_pubk ca)
    (^
     (CertificateVerifymesgsEDH server_expt client_expt client_random
				server_random client client_pubk server
				server_pubk ca)
     (CertificateVerifyEDH server_expt client_expt client_random server_random
			   client client_pubk server server_pubk ca)))

(defmacro (ClientFinish_ncc pre_master_secret client_random server_random server
			    server_pubk ca)
    (enc
     (hash pre_master_secret "client finished"
	   (hash
	    (ClientFinishmesgs_ncc pre_master_secret client_random server_random
				   server server_pubk ca)))
     (ClientWriteKey (MasterSecret pre_master_secret client_random
				   server_random))))
     
(defmacro (ClientFinish_cc pre_master_secret client_random server_random client
			   client_pubk server server_pubk ca)
    (enc
     (hash pre_master_secret "client finished"
	   (hash
	    (ClientFinishmesgs_cc pre_master_secret client_random server_random
				  client client_pubk server server_pubk ca)))
     (ClientWriteKey (MasterSecret pre_master_secret client_random
				   server_random))))
     
(defmacro (ClientFinishEDH_ncc server_expt client_expt client_random
			       server_random server server_pubk ca)
    (enc
     (hash (exp (gen) (mul server_expt client_expt)) "client finished"
	   (hash
	    (ClientFinishmesgsEDH_ncc server_expt client_expt client_random
				      server_random server server_pubk ca)))
     (ClientWriteKey (MasterSecret (exp (gen) (mul server_expt client_expt))
				   client_random server_random))))
     
(defmacro (ClientFinishEDH_cc server_expt client_expt client_random server_random
			      client client_pubk server server_pubk ca)
    (enc
     (hash (exp (gen) (mul server_expt client_expt)) "client finished"
	   (hash
	    (ClientFinishmesgsEDH_cc server_expt client_expt client_random
				     server_random client client_pubk server
				     server_pubk ca)))
     (ClientWriteKey (MasterSecret (exp (gen) (mul server_expt client_expt))
				   client_random server_random))))
     
(defmacro (ServerFinish_ncc pre_master_secret client_random server_random server
			    server_pubk ca)
    (enc
     (hash pre_master_secret "server finished"
	   (hash
	    (ClientFinishmesgs_ncc pre_master_secret client_random server_random
				   server server_pubk ca)
	    (ClientFinish_ncc pre_master_secret client_random server_random
			      server server_pubk ca)))
     (ServerWriteKey (MasterSecret pre_master_secret client_random
				   server_random))))

(defmacro (ServerFinish_cc pre_master_secret client_random server_random client
			   client_pubk server server_pubk ca)
    (enc
     (hash pre_master_secret "server finished"
	   (hash
	    (ClientFinishmesgs_cc pre_master_secret client_random server_random
				  client client_pubk server server_pubk ca)
	    (ClientFinish_cc pre_master_secret client_random server_random
			     client client_pubk server server_pubk ca)))
     (ServerWriteKey (MasterSecret pre_master_secret client_random
				   server_random))))

(defmacro (ServerFinishEDH_ncc server_expt client_expt client_random
			       server_random server server_pubk ca)
    (enc
     (hash (exp (gen) (mul server_expt client_expt)) "server finished"
	   (hash
	    (ClientFinishmesgsEDH_ncc server_expt client_expt client_random
				      server_random server server_pubk ca)
	    (ClientFinishEDH_ncc server_expt client_expt client_random
				 server_random server server_pubk ca)))
     (ServerWriteKey (MasterSecret (exp (gen) (mul server_expt client_expt))
				   client_random server_random))))

(defmacro (ServerFinishEDH_cc server_expt client_expt client_random
			      server_random client client_pubk server
			      server_pubk ca)
    (enc
     (hash (exp (gen) (mul server_expt client_expt)) "server finished"
	   (hash
	    (ClientFinishmesgsEDH_cc server_expt client_expt client_random
				     server_random client client_pubk server
				     server_pubk ca)
	    (ClientFinishEDH_cc server_expt client_expt client_random
				server_random client client_pubk server
				server_pubk ca)))
     (ServerWriteKey (MasterSecret (exp (gen) (mul server_expt client_expt))
				   client_random server_random))))

(defmacro (TLS d1 d2 pre_master_secret client_random server_random server
	       server_pubk ca)
    (^
     (d1 (ClientHello client_random))
     (d2 (cat (ServerHello server_random)
	 (Certificate server server_pubk ca)))
     (d1 (cat (ClientKeyExchange pre_master_secret server_pubk)
	      (ClientFinish_ncc pre_master_secret client_random server_random
				server server_pubk ca)))
     (d2 (ServerFinish_ncc pre_master_secret client_random server_random server
			   server_pubk ca))))

(defmacro (mTLS d1 d2 pre_master_secret client_random server_random client
		client_pubk server server_pubk ca)
    (^
     (d1 (ClientHello client_random))
     (d2 (cat (ServerHello server_random)
	 (Certificate server server_pubk ca)))
     (d1 (cat (Certificate client client_pubk ca)
	 (ClientKeyExchange pre_master_secret server_pubk)
	 (CertificateVerify pre_master_secret client_random server_random client
			    client_pubk server server_pubk ca)
	 (ClientFinish_cc pre_master_secret client_random server_random client
			  client_pubk server server_pubk ca)))
     (d2 (ServerFinish_cc pre_master_secret client_random server_random client
			  client_pubk server server_pubk ca))))

(defmacro (TLS_EDH d1 d2 server_expt client_expt client_random server_random
		   server server_pubk ca)
    (^
     (d1 (ClientHello client_random))
     (d2 (cat (ServerHello server_random)
	      (Certificate server server_pubk ca)
	      (ServerKeyExchangeEDH client_random server_random server_expt
				    server_pubk)))
     (d1 (cat (ClientKeyExchangeEDH client_expt)
	      (ClientFinishEDH_ncc server_expt client_expt client_random
				   server_random server server_pubk ca)))
     (d2 (ServerFinishEDH_ncc server_expt client_expt client_random server_random
			      server server_pubk ca))))

(defmacro (mTLS_EDH d1 d2 server_expt client_expt client_random server_random
		    client client_pubk server server_pubk ca)
    (^
     (d1 (ClientHello client_random))
     (d2 (cat (ServerHello server_random)
	      (Certificate server server_pubk ca)
	      (ServerKeyExchangeEDH client_random server_random server_expt
				    server_pubk)))
     (d1 (cat (Certificate client client_pubk ca)
	 (ClientKeyExchangeEDH client_expt)
	 (CertificateVerifyEDH server_expt client_expt client_random
			       server_random client client_pubk server
			       server_pubk ca)
	 (ClientFinishEDH_cc server_expt client_expt client_random server_random
			     client client_pubk server server_pubk ca)))
     (d2 (ServerFinishEDH_cc server_expt client_expt client_random server_random
			     client client_pubk server server_pubk ca))))

