(herald "FIDO with TLS authentication of server and server certificate binding (authenticator embedded in client)"
	(bound 20))

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

(defmacro (channel_binding_server_cert challenge server pks ca)
  (hash challenge (Certificate server pks ca))
  )

(defprotocol fido basic

  (defrole server
    (vars
     (auth server ca name)
     (n1 n2 pms challenge text)
     (pks akey)
     )
    (trace
     (TLSserver_nocertreq n1 n2 pms server pks ca)
     (send (enc challenge (ServerWriteKey (MasterSecret pms n1 n2))))
     (recv (enc (signed (channel_binding_server_cert challenge server pks ca) auth)
		(ClientWriteKey (MasterSecret pms n1 n2))))
     )
    )

  (defrole client
    (vars
     (auth server ca name)
     (n1 n2 pms challenge text)
     (pks akey)
     )
    (trace
     (TLSclient_nocerts n1 n2 pms server pks ca)
     (recv (enc challenge (ServerWriteKey (MasterSecret pms n1 n2))))
     (send (enc (signed (channel_binding_server_cert challenge server pks ca) auth)
		(ClientWriteKey (MasterSecret pms n1 n2))))
     )
    )
  )


;;; Server perspective with assumptions a server can realistically make
(defskeleton fido
  (vars (auth server ca name) (pks akey) (n2 challenge text))
  (defstrandmax server
    (auth auth)
    (ca ca)
    (pks pks)
    (n2 n2)
    (challenge challenge))
  (non-orig
   (privk auth)
   (invk pks)
   (privk ca))
  (uniq-orig n2 challenge)
  )

;;; Server perspective with assumption that client picks a good pms
(defskeleton fido
  (vars (auth server ca name) (pks akey) (n2 challenge pms text))
  (defstrandmax server
    (auth auth)
    (ca ca)
    (pks pks)
    (n2 n2)
    (pms pms)
    (challenge challenge))
  (non-orig
   (privk auth)
   (invk pks)
   (privk ca))
  (uniq-orig n2 challenge pms)
  )

;;; Client perspective with assumptions a client can realistically make
(defskeleton fido
  (vars (auth server ca name) (pks akey) (n1 pms text))
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
  (vars (auth server ca name) (pks akey) (n2 challenge text))
  (defstrandmax server
    (auth auth)
    (server server)
    (ca ca)
    (pks pks)
    (n2 n2)
    (challenge challenge))
  (deflistener challenge)
  (non-orig
   (privk auth)
   (invk pks)
   (privk ca))
  (uniq-orig n2 challenge)
  )

(defskeleton fido
  (vars (auth server ca name) (pks akey) (n1 pms challenge text))
  (defstrandmax client
    (auth auth)
    (server server)
    (ca ca)
    (pks pks)
    (n1 n1)
    (pms pms)
    (challenge challenge))
  (deflistener (signed (channel_binding_server_cert challenge server pks ca) auth))
  (non-orig
   (privk auth)
   (privk ca)
   (invk pks))
  (uniq-orig n1 pms)
  )

