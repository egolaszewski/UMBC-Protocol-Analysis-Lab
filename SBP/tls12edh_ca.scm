(herald "Cookie Authentication with TLS 1.2 Signed Ephemeral Diffie-Hellman"
	(bound 16)
	)

(include "tls_1.2_macros.lisp") ; 4 message exchange by combining TLS messages.

;; The following two macros are only shortcuts to the TLS macros that generate
;; the write keys for a TLS session. The are only used to reduce the number of
;; characters that must be typed each time the a key is used.

(defmacro (cwk server_expt client_expt client_random server_random)
  (ClientWriteKey (MasterSecret (exp (gen) (mul server_expt client_expt))
				client_random server_random)))

(defmacro (swk server_expt client_expt client_random server_random)
  (ServerWriteKey (MasterSecret (exp (gen) (mul server_expt client_expt))
				client_random server_random)))

(defprotocol ca basic

  ;; This protocol is basic cookie authentication of requests. Once a user logs
  ;; in with their username and password, the server provides an authentication
  ;; cookie to the client that the client can provide to authenticate requests
  ;; to the server without the need to authenticate again with the username
  ;; and password.

  (defrole clienta ;; Role in which the client authenticates with password
    (vars
     (u s ca name) ;; u - username, s - server, ca - certificate authority
     (cr sr random32) ;; cr - client random, sr - server random for TLS
     (y rndx) ;; client's random DH exponent used to create premaster secret
     (x expt) ;; server's DH exponent used to create premaster secret
     (spk akey) ;; server's public key
     (p password) ;; user's password
     (cookie data) ;; authentication cookie provided by the server
     (any mesg)
     (cookiestor locn) ;; client storage of authentication cookie
     (request httpreq)
     (response httpdata)
     )
    (trace
     (TLS_EDH send recv x y cr sr s spk ca) ;; establish TLS session with server
     (send (enc "login" u p (cwk x y cr sr)))
     (recv (enc "login-successful" cookie (swk x y cr sr)))
     (load cookiestor any)            ;; store authentication cookie associated
     (stor cookiestor (cat "client store" u s cookie)) ;; with the server s
     (send (enc cookie request (cwk x y cr sr)))
     (recv (enc response (swk x y cr sr)))
     )
    (uniq-gen y)
    )

  (defrole clientr ;; Role where client makes requests, but already has an
                   ;; authentication cookie (does not need to authenticate)
    (vars
     (u s ca name) ;; u - username, s - server, ca - certificate authority
     (cr sr random32) ;; cr - client random, sr - server random for TLS
     (y rndx) ;; client's random DH exponent used to create premaster secret
     (x expt) ;; server's DH exponent used to create premaster secret
     (spk akey) ;; server's public key
     (p password) ;; user's password
     (cookie data) ;; authentication cookie provided by the server
     (cookiestor locn) ;; client storage of authentication cookie
     (request httpreq)
     (response httpdata)
     )
    (trace
     (TLS_EDH send recv x y cr sr s spk ca) ;; establish TLS session with server
     (load cookiestor (cat "client store" u s cookie));; retrieve authentication
                                                      ;; cookie associated
                                                      ;; with the server s
     (send (enc cookie request (cwk x y cr sr)))
     (recv (enc response (swk x y cr sr)))
     )
    (uniq-gen y)
    (gen-st (cat "client store" u s cookie))
    )

  (defrole servera ;; Role where server authenticates user with password and
                   ;; creates authentication cookie used to authenticate
                   ;; requests
    (vars
     (u s ca name) ;; u - username, s - server, ca - certificate authority
     (cr sr random32) ;; cr - client random, sr - server random for TLS
     (x rndx) ;; server's random DH exponent used to create premaster secret
     (y expt) ;; client's DH exponent used to create premaster secret
     (spk akey) ;; server's public key
     (p password) ;; user's password
     (cookie data) ;; authentication cookie provided by the server
     (any mesg)
     (authstor locn) ;; server storage of clients authentication cookie
     (request httpreq)
     (response httpdata)
     )
    (trace
     (TLS_EDH recv send x y cr sr s spk ca) ;; establish TLS session with client
     (recv (enc "login" u p (cwk x y cr sr)))
     (send (enc "login-successful" cookie (swk x y cr sr)))
     (load authstor any)                             ;; store authentication 
     (stor authstor (cat "server store" s u cookie)) ;; cookie associated with u
     (recv (enc cookie request (cwk x y cr sr)))
     (send (enc response (swk x y cr sr)))
     )
    (facts (neq u s))
    (uniq-gen x)
    (uniq-orig cookie) ;; The unique origination assumption for the cookie is
    ;; included in the role where it is generated to illustrate cookie stealing.
    ;; If the cookie is not uniquely generated, the results are uninteresting
    ;; as the cookie is potentially known to everyone, so it is not tied to any
    ;; authentication.
    )

  (defrole serverr ;; Role where server responds to user requests authenticated
                   ;; with an authentication cookie
    (vars
     (u s ca name) ;; u - username, s - server, ca - certificate authority
     (cr sr random32) ;; cr - client random, sr - server random for TLS
     (x rndx) ;; server's random DH exponent used to create premaster secret
     (y expt) ;; client's DH exponent used to create premaster secret
     (spk akey) ;; server's public key
     (p password) ;; user's password
     (cookie data) ;; authentication cookie provided by the server
     (any mesg)
     (authstor locn) ;; server storage of clients authentication cookie
     (request httpreq)
     (response httpdata)
     )
    (trace
     (TLS_EDH recv send x y cr sr s spk ca) ;; establish TLS session with client
     (recv (enc cookie request (cwk x y cr sr)))
     (load authstor (cat "server store" s u cookie)) ;; retrieve user cookie
     (send (enc response (swk x y cr sr)))
     )
    (facts (neq u s))
    (uniq-gen x)
    (gen-st (cat "server store" s u cookie))
    )

  (lang
   (random32 atom)
   (password atom)
   (httpreq atom)
   (httpdata atom)
   )
  )

;; The following skeleton checks the case where the client authenticates,
;; receives the authentication cookie, and makes the cookie authenticated
;; request over the same TLS connection. Given that the client authenticates
;; the server, the entire process is secure from the client's perspective. The
;; client has authenticated the server and all communication is within the
;; authenticated confidential channel created by TLS. The authentication cookie
;; isn't stolen, nor does it leak from the TLS channel.

(defskeleton ca
  (vars (u s ca name) (p password) (cr sr random32) (spk akey))
  (defstrandmax clienta (u u) (p p) (s s) (ca ca) (cr cr) (sr sr) (spk spk))
  (pen-non-orig p)
  (non-orig (privk ca) (invk spk))
  (uniq-orig cr)
  (uniq-orig sr) ;; This is only included to prevent multiple runs of the same
  ;; server interacting with the same client.
  )

;; Test that the cookie isn't available outside of the TLS channel when it is
;; provided in response to a username and password authentication. The cookie
;; is not available outside of the TLS channel, but CPSA finds a way that the
;; cookie can leak, if the cookie is used again on an insecure connection. CPSA
;; actually found the cookie stealing attack.

(defskeleton ca
  (vars (u s ca name) (p password) (cr sr random32) (cookie data) (spk akey))
  (defstrandmax clienta (u u) (p p) (s s) (ca ca) (cr cr) (sr sr) (spk spk)
    (cookie cookie))
  (deflistener cookie)
  (pen-non-orig p)
  (non-orig (privk ca) (invk spk))
  (uniq-orig cr)
  (uniq-orig sr) ;; This is only included to prevent multiple runs of the same
  ;; server interacting with the same client.
  )

;; Test of a client making a request over a new TLS connection using the cookie
;; for authentication. In this case, the skeleton generated shows that the
;; cookie was created for one user, but the client is a different user. This
;; skeleton illustrates the use of a stolen cookie.

(defskeleton ca
  (vars (s ca name) (cr sr random32) (spk akey))
  (defstrandmax clientr (s s) (ca ca) (cr cr) (sr sr) (spk spk))
  (non-orig (privk ca) (invk spk))
  (uniq-orig cr)
  (uniq-orig sr) ;; This is only included to prevent multiple runs of the same
  ;; server interacting with the same client.
  )

;; The following skeletons determine the theorems that the server supports

(defskeleton ca
  (vars (s ca name) (cr sr random32) (cookie data) (spk akey))
  (defstrand servera 9 (s s) (ca ca) (cr cr) (sr sr) (cookie cookie) (spk spk))
  (non-orig (privk ca) (invk spk))
  (uniq-orig sr cookie)
  )

(defskeleton ca
  (vars (s ca name) (cr sr random32) (cookie data) (spk akey))
  (defstrand servera 9 (s s) (ca ca) (cr cr) (sr sr) (cookie cookie) (spk spk))
  (non-orig (privk ca) (invk spk))
  (uniq-orig sr cookie)
  (uniq-orig cr) ;; Assumes a client produces fresh values (Not a verifiable
                     ;; assumption from the server's perspective.)
  )

(defskeleton ca
  (vars (s ca name) (cr sr random32) (spk akey))
  (defstrand serverr 6 (s s) (ca ca) (cr cr) (sr sr) (spk spk))
  (non-orig (privk ca) (invk spk))
  (uniq-orig sr)
  )




;; Cookie Stealing Prevention Theorems

;; The following goal states that a cookie created during the authentication of
;; a client cannot be obtained by the adversary.

(defgoal ca
  (forall
   ((cookie data) (p password) (cr sr random32) (spk akey)
    (u s ca name) (y rndx) (x expt) (z z-0 strd))
    (implies
      (and (p "clienta" z 10) (p "" z-0 2) 
        (p "clienta" "cookie" z cookie)
	(p "clienta" "p" z p)
        (p "clienta" "cr" z cr) (p "clienta" "sr" z sr)
        (p "clienta" "spk" z spk) (p "clienta" "u" z u)
        (p "clienta" "s" z s) (p "clienta" "ca" z ca)
	(p "clienta" "y" z y)
        (p "clienta" "x" z x) (p "" "x" z-0 cookie) (non (invk spk))
        (non (privk ca)) (pnon p) (uniq sr) (ugen y) (uniq-at cr z 0))
      (false))))

;; The following goal states that if a client uses a cookie to make a request
;; within a TLS connection in which it has authenticated, a server produced
;; the cookie for the user on that client. This prevents cookie stealing as a
;; client cannot have a cookie that authenticates a different user.

(defgoal ca
  (forall
   ((cookie data) (cr sr random32) (spk akey) (u s ca name) (y rndx) (x expt)
    (z strd))
    (implies
      (and (p "clienta" z 10) 
        (p "clienta" "cookie" z cookie)
        (p "clienta" "cr" z cr)
	(p "clienta" "sr" z sr)
        (p "clienta" "spk" z spk)
	(p "clienta" "u" z u)
        (p "clienta" "s" z s)
	(p "clienta" "ca" z ca)
	(p "clienta" "y" z y)
        (p "clienta" "x" z x)
	(non (invk spk))
	(non (privk ca))
        (uniq sr)
	(ugen y)
	(uniq-at cr z 0))
      (exists
       ((z-0 strd))
       (and
        (p "servera" "cookie" z-0 cookie)
        (p "servera" "spk" z-0 spk)
	(p "servera" "u" z-0 u)
        (p "servera" "s" z-0 s)
	(p "servera" "ca" z-0 ca)
        (uniq-at cookie z-0 5)
	(fact neq u s))))))

;; The following goal states that if a client uses a cookie to make a request
;; within a TLS connection in which it has not authenticated, a server produced
;; the cookie for the user on that client. This prevents cookie stealing as a
;; client cannot have a cookie that authenticates a different user.

(defgoal ca
  (forall
   ((cookie data) (cr sr random32) (spk akey) (s ca u name) (y rndx) (x expt)
    (z strd))
    (implies
     (and
      (p "clientr" z 7)
      (p "clientr" "cookie" z cookie)
      (p "clientr" "cr" z cr)
      (p "clientr" "sr" z sr)
      (p "clientr" "spk" z spk)
      (p "clientr" "u" z u)
      (p "clientr" "s" z s)
      (p "clientr" "ca" z ca)
      (p "clientr" "y" z y)
      (p "clientr" "x" z x)
      (non (invk spk))
      (non (privk ca))
      (uniq sr)
      (ugen y)
      (uniq-at cr z 0))
      (exists
       ((z-0 strd))
       (and
        (p "servera" "cookie" z-0 cookie)
        (p "servera" "spk" z-0 spk)
	(p "servera" "u" z-0 u)
        (p "servera" "s" z-0 s)
	(p "servera" "ca" z-0 ca)
        (uniq-at cookie z-0 5)
	(fact neq u s))))))

