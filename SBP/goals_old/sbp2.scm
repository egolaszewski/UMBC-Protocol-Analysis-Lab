(herald "Session Binding Protocol with TLS 1.2 (proxy and server seperate as in paper description (TLS connection from proxy to server))"
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

  (defrole proxy
    (vars
     (c prxy s ca name)
     (cr pr1 pr2 sr random32)
     (pms ppms random48)
     (p password)
     (cookie data)
     (ppk skey)
     (request httprqst)
     (response httpdata)
     (ln chan) ; local area network
     )
    (trace
     (TLS recv send pms cr pr1 prxy ca)     
     (recv (enc "login" c p (cwk pms cr pr1)))
     (TLSprvt send recv ln ppms pr2 sr s ca)
     (send ln (enc "login" c p (cwk ppms pr2 sr)))
     (recv ln (enc "login-successful" cookie (swk ppms pr2 sr)))
     (send (enc "login-successful"
		(enc cookie (hash ppk (MasterSecret pms cr pr1))) (swk pms cr pr1)))
     (recv (enc request (enc cookie (hash ppk (MasterSecret pms cr pr1))) (cwk pms cr pr1)))
     (send ln (enc request cookie (cwk ppms pr2 sr)))
     (recv ln (enc response (cwk ppms pr2 sr)))
     (send (enc response (swk pms cr pr1)))
     )
    (conf ln)
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
     (ln chan) ; local area network
     )
    (trace
     (TLSprvt recv send ln pms cr sr s ca)
     (recv ln (enc "login" c p (cwk pms cr sr)))
     (send ln (enc "login-successful" cookie (swk pms cr sr)))
     (recv ln (enc request cookie (cwk pms cr sr)))
     (send ln (enc response (swk pms cr sr)))
     )
    
    )

  (defrule proxy-and-server-are-distinct
    (forall ((z0 z1 strd) (x name))
	    (implies
	     (and (p "proxy" z0 1)
		  (p "proxy" z1 1)
		  (p "proxy" "s" z0 x)
		  (p "proxy" "prxy" z1 x))
	     (false))))
  
  (lang (password atom) (httprqst atom) (httpdata atom) (random48 atom) (random32 atom))

  )

; Test of client authentication. This skeleton generates many shapes, but in all
; cases, the client successfully authenticates the server to which it is connected.
; This is due to the client not knowing if the server is generating a fresh nonce
; for each connection. If the server does not, then an adversary could replay the 
; initial TLS messages to multiple instances of the same server. In no case will 
; login be exposed outside the channel, as the client has supplied fresh values
; that guarantee the keys used in the communication are fresh and and the adversary
; has no way to retrieve them based on the shapes.

;(defskeleton sbp
;  (vars (s ca name) (cr pms text) (p password))
;  (defstrandmax client (s s) (ca ca) (cr cr) (pms pms) (p p))
;  (non-orig (privk s) (privk ca))
;  (uniq-orig cr pms)
;  (pen-non-orig p)
;  (fact (neq cr pms))
;  )

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
; with multiple servers.

;(defskeleton sbp 
;  (vars (s ca name) (cr pms text) (p password))
;  (defstrandmax client (s s) (ca ca) (cr cr) (pms pms) (p p))
;  (deflistener p)
;  (non-orig (privk s) (privk ca))
;  (uniq-orig cr pms)
;  (pen-non-orig p)
;  (fact (neq cr pms))
;  )

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

;(defskeleton sbp
;  (vars (s ca name) (sr cr pms text) (p password) (cookie data))
;  (defstrand server 7 (s s) (ca ca) (sr sr) (p p) (cookie cookie) (cr cr) (pms pms))
;  (non-orig (privk s) (privk ca))
;  (uniq-orig sr cr pms)
;  (pen-non-orig p)
;  )
    
;; Client<->Proxy authentication goal.
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
        (uniq sr)
        (uniq-at cr z 0)
        (uniq-at pms z 2))
      (exists ((cookie-0 data) (z-0 z-1 strd) (ppk skey) (pr2 sr-0 random32) (ppms random48))
        (and
          (= cookie (enc cookie-0 (hash ppk (hash pms cr sr))))
            (p "client" "cookie" z cookie))
            (p "proxy" z-0 16)
            (p "proxy" "cookie" z-0 cookie-0)
            (p "server" z-1 8)
            (p "server" "cookie" z-1 cookie-0))))))

;; Server<->Client authentication goal.
(defgoal sbp
  (forall
    ((cookie data) (request httprqst) (p password) (sr cr random32)
      (pms random48) (s ca c name) (z strd))
    (implies
      (and
        (p "server" z 8)
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
        (uniq-at sr z 1))
      (exists 
        ((cookie-0 data) (cr-0 sr-0 random32) (pms-0 random48) (c-0 s-0 ca-0 name) (z-0 z-1 strd)
        (ppk skey))
        (and
          (= cookie-0 (enc cookie (hash ppk (hash pms-0 cr-0 sr-0))))
          (p "client" z-0 8)
          (p "client" "cookie" z-0 cookie-0)
          (p "client" "p" z-0 p)
          (p "proxy" z-1 16)
          (p "proxy" "cookie" z-1 cookie)
          (p "proxy" "p" z-1 p)
          (p "server" "cookie" z cookie)
          (p "server" "p" z p))))))

;; Password confidentiality goal.
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
        (uniq sr)
        (uniq-at cr z 0)
        (uniq-at pms z 2))
      (exists ((pw-0 password))
        (= pw pw-0)))))