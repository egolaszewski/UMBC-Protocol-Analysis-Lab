(herald "Session Binding Protocol with TLS 1.2 (combined proxy and server as used in paper implementation"
	(bound 12)
	)

(include "tls_1.2_macros.lisp") ; 4 message exchange by combining TLS messages.

(defmacro (cwk pre_master_secret client_random server_random)
  (ClientWriteKey (MasterSecret pre_master_secret client_random server_random)))

(defmacro (swk pre_master_secret client_random server_random)
  (ServerWriteKey (MasterSecret pre_master_secret client_random server_random)))

(defprotocol sbp basic

  (defrole client
    (vars
     (c s ca name)
     (cr sr random32)
     (pms random48)
     (p password)
     (cookie mesg)
     (request httprqst)
     (response httpdata)
     )
    (trace
     (TLS send recv pms cr sr s ca)
     (send (enc "login" c p (cwk pms cr sr)))
     (recv (enc "login-successful" cookie (swk pms cr sr)))
     (send (enc request cookie (cwk pms cr sr)))
     (recv (enc response (swk pms cr sr)))
     )
    )

  (defrole server
    (vars
     (c s ca name)
     (cr sr random32)
     (pms random48)
     (p password)
     (cookie data)
     (request httprqst)
     (response httpdata)
     )
    (trace
     (TLS recv send pms cr sr s ca)
     (recv (enc "login" c p (cwk pms cr sr)))
     (send (enc "login-successful"
		(hash cookie (MasterSecret pms cr sr)) (swk pms cr sr)))
     (recv (enc request (hash cookie (MasterSecret pms cr sr)) (cwk pms cr sr)))
     (send (enc response (swk pms cr sr)))
     )
    )

; The additional types created below are to allow items which should be distinct in
; the protocol from being equated by CPSA. In particular, there are to random values
; random32 and random48 to distinguish nonces, which are 32 bits, from the premaster
; secret that is 48 bits. This is not necessary in this model, where the proxy and  
; server are combined, but is necessary when they are not to keep CPSA from equating
; the nonces with the premaster secret and potentially exposing the secret by 
; sending it as a nonce, when in fact the protocol wouldn't support that interaction.
  
  (lang (password atom) (httprqst atom) (httpdata atom) (random32 atom) (random48 atom))

  )

; Test of client authentication. This skeleton generates many shapes, but in all
; cases, the client successfully authenticates the server to which it is connected.
; This is due to the client not knowing if the server is generating a fresh nonce
; for each connection. If the server does not, then an adversary could replay the 
; initial TLS messages to multiple instances of the same server. In no case will 
; login be exposed outside the channel, as the client has supplied fresh values
; that guarantee the keys used in the communication are fresh and and the adversary
; has no way to retrieve them based on the shapes.

(defskeleton sbp
  (vars (s ca name) (cr random32) (pms random48) (p password))
  (defstrandmax client (s s) (ca ca) (cr cr) (pms pms) (p p))
  (non-orig (privk s) (privk ca))
  (uniq-orig cr pms)
  (pen-non-orig p)
  )

; Check that password is not exposed outside of connection between client and
; server that the client has authenticated. This skeleton produces the same
; number of shapes as the first skeleton. In all of the shapes, the password
; is shown leaking from a different client. In no shapes is the client the 
; same as the client with the secure TLS connection. The password leaks from
; a client that has the same password as the client with the secure TLS connection,
; indicating that multiple clients could have the same password (true in reality)
; or that a client uses the same password with multiple servers (also true).
; This could be cleaned up if clients instead sent a hash of their username and
; password as their password, guaranteeing (probabalistically) that the passwords
; would be unique for each client, except in the case the same password is used
; with multiple servers by the same client.

(defskeleton sbp 
  (vars (s ca name) (cr random32) (pms random48) (p password))
  (defstrandmax client (s s) (ca ca) (cr cr) (pms pms) (p p))
  (deflistener p)
  (non-orig (privk s) (privk ca))
  (uniq-orig cr pms)
  (pen-non-orig p)
  )

; Skeleton that assumes the server generates a fresh nonce in the TLS connection.
; This skeleton only produces one shape, as the assumption is that the server will
; not reuse a previous nonce, guaranteeing that it cannot match a nonce with
; another run of the server. This cleans up all the shapes from the initial skeleton
; despite making an assumtion that the client can not guarantee. It is, however,
; consistent with the first set of shapes where the client only talks to and
; authenticates one server and the adversary has no access to any of the values.

(defskeleton sbp
  (vars (s ca name) (cr sr random32) (pms random48) (p password))
  (defstrandmax client (s s) (ca ca) (cr cr) (pms pms) (p p) (sr sr))
  (non-orig (privk s) (privk ca))
  (uniq-orig cr pms sr)
  (pen-non-orig p)
  )

; Skeleton from the server's perspective. As TLS does not authenticate the client,
; the server does not know if it is actually talking to the client or the adversary.
; The adversary can gain access to the password and authenticate as the client to 
; the server as the client could talk to the adversary intentionally. This is the
; built in MitM that TLS supports. (Also explains how passwords leak.)

(defskeleton sbp
  (vars (s ca name) (sr random32) (p password) (cookie data))
  (defstrand server 7 (s s) (ca ca) (sr sr) (p p) (cookie cookie))
  (non-orig (privk s) (privk ca))
  (uniq-orig sr)
  (pen-non-orig p)
  )

; This skeleton is just to show that making assumptions about the values produced
; by the client will not correct the shape, as the server has no idea with whom it
; has established a connection. It produces the same shape as the previous skeleton.

(defskeleton sbp
  (vars (s ca name) (sr cr random32) (pms random48) (p password) (cookie data))
  (defstrand server 7 (s s) (ca ca) (sr sr) (p p) (cookie cookie) (cr cr) (pms pms))
  (non-orig (privk s) (privk ca))
  (uniq-orig sr cr pms)
  (pen-non-orig p)
  )
    

;; Client authentication goal.
(defgoal sbp
  (forall
    ((cookie mesg) (response httpdata) (request httprqst) (p password)
      (cr sr random32) (pms random48) (s ca c name) (z strd))
    (implies
      (and
        (p "client" z 8)
        (p "client" "cookie" z cookie)
        (p "client" "response" z response)
        (p "client" "request" z request)
        (p "client" "p" z p)
        (p "client" "cr" z cr)
        (p "client" "sr" z sr)
        (p "client" "pms" z pms)
        (p "client" "c" z c)
        (p "client" "s" z s)
        (p "client" "ca" z ca)
        (non (privk s))
        (non (privk ca))
        (pnon p)
        (uniq-at cr z 0)
        (uniq-at pms z 2))
      (exists ((cookie-0 data) (z-0 strd))
        (and
          (= cookie (hash cookie-0 (hash pms cr sr)))
          (p "server" z-0 8)
          (p "client" "cookie" z (hash cookie-0 (hash pms cr sr)))
          (p "server" "cookie" z-0 cookie-0))))))

;; Server authentication goal. (Should fail, since TLS is one-way.)
(defgoal sbp
  (forall
    ((cookie data) (request httprqst) (p password) (sr cr random32)
      (pms random48) (s ca c name) (z strd))
    (implies
      (and 
        (p "server" z 7)
        (p "server" "cookie" z cookie)
        (p "server" "request" z request)
        (p "server" "p" z p)
        (p "server" "cr" z cr)
        (p "server" "sr" z sr)
        (p "server" "pms" z pms)
        (p "server" "c" z c)
        (p "server" "s" z s)
        (p "server" "ca" z ca)
        (non (privk s))
        (non (privk ca))
        (pnon p)
        (uniq cr)
        (uniq pms)
        (uniq-at sr z 1))
      (exists
        ((cookie-0 data) (z-0 strd))
        (and
          (= cookie-0 (hash cookie (hash pms cr sr)))
          (p "client" z-0 8)
          (p "server" "cookie" z cookie)
          (p "client" "cookie" z-0 cookie-0)
          (p "server" "p" z p)
          (p "client" "p" z-0 p))))

;; Password secrecy goal.
(defgoal sbp
  (forall
    ((cookie mesg) (response httpdata) (request httprqst) (pw password)
      (cr sr random32) (pms random48) (s ca c name) (z z-0 strd))
    (implies
      (and
        (p "client" z 8)
        (p "" z-0 2)
        (p "client" "cookie" z cookie)
        (p "client" "response" z response)
        (p "client" "request" z request)
        (p "client" "p" z pw)
        (p "client" "cr" z cr)
        (p "client" "sr" z sr)
        (p "client" "pms" z pms)
        (p "client" "c" z c)
        (p "client" "s" z s)
        (p "client" "ca" z ca)
        (p "" "x" z-0 pw)
        (non (privk s))
        (non (privk ca))
        (pnon pw)
        (uniq-at cr z 0)
        (uniq-at pms z 2))
      (exists ()
        (and
          (p "" "x" z-0 pw))))))