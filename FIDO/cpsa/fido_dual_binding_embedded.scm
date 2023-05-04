(herald "FIDO with TLS authentication of server and dual binding (authenticator embedded in client)"
	(bound 20) (limit 10000))

;; In this version, the authenticator is treated as if it is embedded in the client. This is
;; consistent with the FIDO specifications in which they view the authenticator as a part of
;; the client system, such as a finger print reader, camara for facial recognition, TPM, etc.
;; that is used to authenticate the user on the client's system (phone, computer, etc.) that
;; is running the application. In this case there are no protocols that connect to the
;; authenticator, only function calls within the operating system. As we are not evaluating
;; the CTAP protocols, this model provides a better view of the bindings between the client
;; and the server by including the authentication responses directly from the client. This
;; highlights the TLS channel and its relationship to the FIDO authentication protocol. 

(include "TLSmacros.lisp")

;;; Sign a message and append the signature.
(defmacro (signed m i)
    (cat m (enc m (privk i)))
    )

(defprotocol fido basic

  (defrole server
    (vars
     (auth server ca name)
     (n1 n2 pms text)
     (pks akey)
     (ns data)
     )
    (trace
     (TLSserver_nocertreq n1 n2 pms server pks ca)
     (send (enc ns (hash ns (Certificate server pks ca)) (ServerWriteKey (MasterSecret pms n1 n2))))
     (recv (enc (signed (hash (hash ns (Certificate server pks ca)) (Certificate server pks ca)) auth)
		(ClientWriteKey (MasterSecret pms n1 n2))))
     )
    )

  (defrole client
    (vars
     (auth server ca name)
     (n1 n2 pms text)
     (pks akey)
     (ns data)
     )
    (trace
     (TLSclient_nocerts n1 n2 pms server pks ca)
     (recv (enc ns (hash ns (Certificate server pks ca)) (ServerWriteKey (MasterSecret pms n1 n2))))
     (send (enc (signed (hash (hash ns (Certificate server pks ca)) (Certificate server pks ca)) auth)
		(ClientWriteKey (MasterSecret pms n1 n2))))
     )
    )
  )

;;; Server perspective with assumptions a server can realistically make
(defskeleton fido
  (vars (auth server ca name) (pks akey) (n2 text) (ns data))
  (defstrandmax server
    (auth auth)
    (ca ca)
    (pks pks)
    (n2 n2)
    (ns ns))
  (non-orig
   (privk auth)
   (invk pks)
   (privk ca))
  (uniq-orig n2 ns)
  )

;;; Client perspective with assumptions a client can realistically make
(defskeleton fido
  (vars (auth server ca name) (pks akey) (n1 pms text) (ns data))
  (defstrandmax client
    (auth auth)
    (server server)
    (ca ca)
    (pks pks)
    (n1 n1)
    (pms pms))
  (non-orig
   (privk auth)
   (invk pks)
   (privk ca))
  (uniq-orig n1 pms)
  )

;;; Test for Penetrator available values
(defskeleton fido
  (vars (auth server ca name) (pks akey) (n2 text) (ns data))
  (defstrandmax server
    (auth auth)
    (server server)
    (ca ca)
    (pks pks)
    (n2 n2)
    (ns ns))
  (deflistener ns)
  (non-orig
   (privk auth)
   (invk pks)
   (privk ca))
  (uniq-orig n2 ns)
  )

(defskeleton fido
  (vars (auth server ca name) (pks akey) (n1 pms text) (ns data))
  (defstrandmax client
    (auth auth)
    (server server)
    (ca ca)
    (pks pks)
    (n1 n1)
    (pms pms)
    (ns ns))
  (deflistener (signed (hash (hash ns (Certificate server pks ca)) (Certificate server pks ca)) auth))
  (non-orig
   (privk auth)
   (privk ca)
   (invk pks))
  (uniq-orig n1 pms)
  )

