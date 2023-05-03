(herald "FIDO with TLS authentication of server and channel ID binding."
	(bound 20))

(include "tlsmacros.lisp")

;;; Sign a message and append the signature.
(defmacro (signed m i)
    (cat m (enc m (privk i)))
)

;; Produce a channel ID binding.
(defmacro (channel_binding_channel_id challenge client)
  (hash challenge (pubk client) (enc (pubk client) (privk client)))
)

(defprotocol fido basic
  (defrole auth
    (vars
     (auth client name)
     (fcp mesg)
     )
    (trace
     (recv (enc fcp (ltk client auth)))
     (send (enc (signed fcp auth) (ltk client auth)))
     )
    )

  (defrole server
    (vars
     (auth server client ca name)
     (n1 n2 pms challenge text)
     (pks akey)
     )
    (trace
     (TLSserver_nocertreq n1 n2 pms server pks ca)
     (send (enc challenge (ServerWriteKey (MasterSecret pms n1 n2))))
     (recv (enc (signed (channel_binding_channel_id challenge client) auth)
		(ClientWriteKey (MasterSecret pms n1 n2))))
     )
    )

  (defrole client
    (vars
     (auth client server ca name)
     (n1 n2 pms challenge text)
     (pks akey)
     )
    (trace
     (TLSclient_nocerts n1 n2 pms server pks ca)
     (recv (enc challenge (ServerWriteKey (MasterSecret pms n1 n2))))
     (send (enc (channel_binding_channel_id challenge client) (ltk client auth)))
     (recv (enc (signed (channel_binding_channel_id challenge client) auth) (ltk client auth)))
     (send (enc (signed (channel_binding_channel_id challenge client) auth)
		(ClientWriteKey (MasterSecret pms n1 n2))))
     )
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
  (vars (auth server ca name) (n2 challenge text) (pks akey))
  (defstrandmax server
    (auth auth)
    (server server)
	(ca ca)
    (n2 n2)
	(challenge challenge)
	(pks pks))
  (non-orig
   (privk auth)
   (privk server)
   (privk ca)
   (invk pks))
  (uniq-orig n2 challenge)
  )

;;; Authenticator perspective
(defskeleton fido
  (vars (auth client name))
  (defstrandmax auth
    (auth auth)
    (client client))
  (non-orig
   (privk auth)
   (ltk client auth))
  )

;;; Client perspective
(defskeleton fido
  (vars (auth client server ca name) (n1 pms text) (pks akey))
  (defstrandmax client
    (auth auth)
    (client client)
    (server server)
	(ca ca)
    (n1 n1)
    (pms pms)
	(pks pks))
  (non-orig
   (privk auth)
   (privk ca)
   (ltk client auth)
   (invk pks))
  (uniq-orig n1 pms)
  )

;;; Test for Penetrator available values
(defskeleton fido
  (vars (auth server ca name) (n2 challenge text) (pks akey))
  (defstrandmax server
    (auth auth)
    (server server)
	(ca ca)
    (n2 n2)
	(challenge challenge)
	(pks pks))
  (deflistener challenge)
  (non-orig
   (privk auth)
   (privk server)
   (privk ca)
   (invk pks))
  (uniq-orig n2 challenge)
 )

(defskeleton fido
  (vars (auth client name) (fcp mesg))
  (defstrandmax auth
    (auth auth)
    (client client)
    (fcp fcp))
  (deflistener (signed fcp auth))
  (non-orig
   (privk auth)
   (ltk client auth))
  )
