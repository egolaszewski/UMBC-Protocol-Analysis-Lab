(herald "FIDO with TLS authentication of server and no binding")

(include "tlsmacros.lisp")

;;; Sign a message and append the signature.
(defmacro (signed m i)
    (cat m (enc m (privk i)))
)

(defprotocol fido basic
  (defrole auth
    (vars
     (auth client name)
     (challenge text)
     )
    (trace
     (recv (enc challenge (ltk client auth)))
     (send (enc (signed challenge auth) (ltk client auth)))
     )
    )

  (defrole server
    (vars
     (auth server ca name)
     (n1 n2 pms challenge text)
     )
    (trace
     (TLSserver_nocertreq n1 n2 pms server ca)
     (send (enc challenge (ServerWriteKey (MasterSecret pms n1 n2))))
     (recv (enc (signed challenge auth)
		(ClientWriteKey (MasterSecret pms n1 n2))))
     )
    (uniq-orig challenge)
    (non-orig (privk ca))
    )

  (defrole client
    (vars
     (auth client server ca name)
     (n1 n2 pms challenge text)
     )
    (trace
     (TLSclient_nocerts n1 n2 pms server ca)
     (recv (enc challenge (ServerWriteKey (MasterSecret pms n1 n2))))
     (send (enc challenge (ltk client auth)))
     (recv (enc (signed challenge auth) (ltk client auth)))
     (send (enc (signed challenge auth)
		(ClientWriteKey (MasterSecret pms n1 n2))))
     )
    (non-orig (privk ca))
    )

  (defrule one-authenticator-per-client
    (forall ((z0 z1 strd) (client name))
	    (implies
	     (and
	      (p "auth" z0 1)
	      (p "auth" z1 1)
	      (p "auth" "client" z0 client)
	      (p "auth" "client" z1 client)
	      )
	     (= z0 z1)
	     )
	    )
    )
  )

;;; Server perspective
(defskeleton fido
  (vars (auth server name) (n2 text))
  (defstrand server 8
    (auth auth)
    (server server)
    (n2 n2))
  (non-orig
   (privk auth)
   (privk server))
  (uniq-orig n2)
  )

;;; Authenticator perspective
(defskeleton fido
  (vars (auth client name))
  (defstrand auth 2
    (auth auth)
    (client client))
  (non-orig
   (privk auth)
   (ltk client auth))
  )

;;; Client perspective
(defskeleton fido
  (vars (auth client server name) (n1 pms text))
  (defstrand client 9
    (auth auth)
    (client client)
    (server server)
    (n1 n1)
    (pms pms))
  (non-orig
   (privk auth)
   (privk server)
   (ltk client auth))
  (uniq-orig n1 pms)
  )

;;; Test for Penetrator available values
(defskeleton fido
  (vars (auth server name) (n2 challenge text))
  (defstrand server 8
    (auth auth)
    (server server)
    (n2 n2)
    (challenge challenge))
  (deflistener challenge)
  (non-orig
   (privk auth)
   (privk server))
  (uniq-orig n2)
  )

(defskeleton fido
  (vars (auth client name) (challenge text))
  (defstrand auth 2
    (auth auth)
    (client client)
    (challenge challenge))
  (deflistener (signed challenge auth))
  (non-orig
   (privk auth)
   (ltk client auth))
  )
