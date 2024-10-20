(herald "Session Binding Protocol with mTLS 1.2 EDH (uses the modified server as implemented and tested in the paper and the cookie authentication model (ca.scm) which showed the cookie stealing attack)."
	(bound 12)
	)

(include "tls_1.2_macros.lisp") ; 4 message exchange by combining TLS messages.
(include "mtls_rules.lisp") ; file containing rules to constrain CPSA search.

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
     (c u s ca name) ;; c - client u - username, s - server,
                     ;; ca - certificate authority
     (spk akey) ;; server's public key
     (cpk akey) ;; client's public key
     (cr sr random32) ;; cr - client random, sr - server random for TLS
     (y rndx) ;; client's random DH exponent used to create premaster secret
     (x expt) ;; server's DH exponent used to create premaster secret
     (p password) ;; user's password
     (cookie mesg) ;; authentication cookie provided by the server
     (any mesg)
     (cookiestor locn) ;; client storage of authentication cookie
     (request httpreq)
     (response httpdata)
     )
    (trace
     (mTLS_EDH send recv x y cr sr c cpk s spk ca) ;; establish mTLS session
                                                 ;; with server
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
     (c u s ca name) ;; c -client u - username, s - server,
                     ;; ca - certificate authority
     (spk akey) ;; server's public key
     (cpk akey) ;; client's public key
     (cr sr random32) ;; cr - client random, sr - server random for TLS
     (y rndx) ;; client's random DH exponent used to create premaster secret
     (x expt) ;; server's DH exponent used to create premaster secret
     (p password) ;; user's password
     (cookie mesg) ;; authentication cookie provided by the server
     (cookiestor locn) ;; client storage of authentication cookie
     (request httpreq)
     (response httpdata)
     )
    (trace
     (mTLS_EDH send recv x y cr sr c cpk s spk ca) ;; establish mTLS session
                                                   ;; with server
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
                   ;; requests. This role differs from the same role in ca.scm
                   ;; as it has been modified to transform the cookie created by
                   ;; the server by encrypting the cookie with a key derived 
                   ;; from the TLS master secret and a secret proxy key. The 
                   ;; client receives the transformed cookie.
    
    (vars
     (c u s ca name) ;; c - client, u - username, s - server,
                     ;; ca - certificate authority
     (spk akey) ;; server's public key
     (cpk akey) ;; client's public key
     (cr sr random32) ;; cr - client random, sr - server random for TLS
     (x rndx) ;; server's random DH exponent used to create premaster secret
     (y expt) ;; client's DH exponent used to create premaster secret
     (p password) ;; user's password
     (cookie data) ;; authentication cookie provided by the server
     (ppk skey) ;; proxy private key
     (any mesg)
     (authstor locn) ;; server storage of clients authentication cookie
     (request httpreq)
     (response httpdata)
     )
    (trace
     (mTLS_EDH recv send x y cr sr c cpk s spk ca) ;; establish mTLS session
                                                   ;; with client
     (recv (enc "login" u p (cwk x y cr sr)))
     (send (enc "login-successful"
		(enc cookie (hash ppk (MasterSecret (exp (gen) (mul x y)) cr
						    sr)))
		(swk x y cr sr)))
     (load authstor any)                             ;; store authentication 
     (stor authstor (cat "server store" s u cookie)) ;; cookie associated with u
     (recv (enc (enc cookie (hash ppk (MasterSecret (exp (gen) (mul x y)) cr
							 sr)))
		request (cwk x y cr sr)))
     (send (enc response (swk x y cr sr)))
     )
    (facts (neq u s))
    (uniq-gen x)
    (non-orig ppk) ;; Proxy private key is only known by the proxy or the server
                   ;; in this case as the proxy and server are implemented
                   ;; together.
    (uniq-orig cookie) ;; The unique origination assumption for the cookie is
    ;; included in the role where it is generated to illustrate cookie stealing.
    ;; If the cookie is not uniquely generated, the results are uninteresting
    ;; as the cookie is potentially known to everyone, so it is not tied to any
    ;; authentication.
    )

  (defrole serverr ;; Role where server responds to user requests authenticated
                   ;; with an authentication cookie
    (vars
     (c u s ca name) ;; c - client, u - username, s - server,
                     ;; ca - certificate authority
     (spk akey) ;; server's public key
     (cpk akey) ;; client's public key
     (cr sr random32) ;; cr - client random, sr - server random for TLS
     (x rndx) ;; server's random DH exponent used to create premaster secret
     (y expt) ;; client's DH exponent used to create premaster secret
     (p password) ;; user's password
     (cookie data) ;; authentication cookie provided by the server
     (ppk skey)
     (any mesg)
     (authstor locn) ;; server storage of clients authentication cookie
     (request httpreq)
     (response httpdata)
     )
    (trace
     (mTLS_EDH recv send x y cr sr c cpk s spk ca) ;; establish mTLS session
                                                   ;; with client
     (recv (enc (enc cookie (hash ppk (MasterSecret (exp (gen) (mul x y)) cr
						    sr)))
		request (cwk x y cr sr)))
     (load authstor (cat "server store" s u cookie)) ;; retrieve user cookie
     (send (enc response (swk x y cr sr)))
     )
    (facts (neq u s))
    (uniq-gen x)
    (non-orig ppk) ;; Proxy private key is only known by the proxy or the server
                   ;; in this case as the proxy and server are implemented
                   ;; together.
    (gen-st (cat "server store" s u cookie))
    )

  (clients-distinct-from-servers-rules)
  
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
  (vars (c u s ca name) (p password) (cr sr random32) (spk cpk akey))
  (defstrandmax clienta (u u) (p p) (s s) (c c) (ca ca) (cr cr) (sr sr)
    (spk spk) (cpk cpk))
  (pen-non-orig p)
  (non-orig (privk ca) (invk spk) (invk cpk))
  (uniq-orig cr)
  (uniq-orig sr) ;; This is only included to prevent multiple runs of the same
  ;; server interacting with the same client. (When removed has no impact on
  ;; security theorems.)
  )

;; Test that the cookie isn't available outside of the TLS channel when it is
;; provided in response to a username and password authentication. The cookie
;; is not available outside of the original TLS channel, as the client's cookie
;; is tied to the original TLS session where it was created. This is a dead
;; skeleton since the server cannot correctly decrypt the cookie as the TLS
;; parameters have changed. This skeleton demonstrates that the approach of
;; binding the cookie to the TLS channel prevents the cookie stealing attack,
;; as the same skeleton in ca.scm model produced a shape in which the cookie
;; was leaked.

(defskeleton ca
  (vars (c u s ca name) (p password) (cr sr random32) (spk cpk akey)
	(cookie data))
  (defstrandmax clienta (u u) (p p) (s s) (c c) (ca ca) (cr cr) (sr sr) 
    (cookie cookie) (spk spk) (cpk cpk))
  (deflistener cookie)
  (pen-non-orig p)
  (non-orig (privk ca) (invk spk) (invk cpk))
  (uniq-orig cr)
  (uniq-orig sr) ;; This is only included to prevent multiple runs of the same
  ;; server interacting with the same client. (When removed has no impact on
  ;; security theorems.)
  )

;; Test of a client making a request over a new TLS connection using the cookie
;; for authentication. With the binding of a cookie to the TLS session in which
;; the cookie was created, the skeleton is dead because the cookie created by 
;; the server cannot be decrypted from the value received from the client as
;; the TLS master secret used in the key is different. This demonstrates that
;; binding the cookie to the TLS session prevents cookie stealing.

(defskeleton ca
  (vars (c s ca name) (cr sr random32) (spk cpk akey))
  (defstrandmax clientr (s s) (c c) (ca ca) (cr cr) (sr sr) (spk spk) (cpk cpk))
  (non-orig (privk ca) (invk spk) (invk cpk))
  (uniq-orig cr)
  (uniq-orig sr) ;; This is only included to prevent multiple runs of the same
  ;; server interacting with the same client.  (When removed has no impact on
  ;; security theorems.)
  )

;; The following skeletons determine the theorems that the server supports

(defskeleton ca
  (vars (c s ca name) (cr sr random32) (spk cpk akey) (cookie data))
  (defstrand servera 9 (s s) (c c) (ca ca) (cr cr) (sr sr) (spk spk) (cpk cpk)
    (cookie cookie))
  (non-orig (privk ca) (invk spk) (invk cpk))
  (uniq-orig sr cookie)
  )

(defskeleton ca
  (vars (c s ca name) (cr sr random32) (spk cpk akey) (cookie data))
  (defstrand servera 9 (s s) (c c) (ca ca) (cr cr) (sr sr) (spk spk) (cpk cpk)
    (cookie cookie))
  (non-orig (privk ca) (invk spk) (invk cpk))
  (uniq-orig sr cookie)
  (uniq-orig cr) ;; Assumes a client produces fresh values (Not a verifiable
                     ;; assumption from the server's perspective.)
  )

(defskeleton ca
  (vars (c s ca name) (cr sr random32) (spk cpk akey))
  (defstrand serverr 6 (s s) (c c) (ca ca) (cr cr) (sr sr) (spk spk) (cpk cpk))
  (non-orig (privk ca) (invk spk) (invk cpk))
  (uniq-orig sr)
  )


	    
;; Cookie Stealing Prevention Theorems

;; The following goal states that a cookie created during the authentication of
;; a client cannot be obtained by the adversary.

(defgoal ca
  (forall
    ((cookie data) (p password) (cr sr random32) (spk cpk akey) (c u s ca name)
     (y rndx) (x expt) (z z-0 strd))
    (implies
     (and
      (p "clienta" z 10) (p "" z-0 2) (p "clienta" "cookie" z cookie)
      (p "clienta" "p" z p)
      (p "clienta" "cr" z cr) (p "clienta" "sr" z sr)
      (p "clienta" "spk" z spk) (p "clienta" "cpk" z cpk)
      (p "clienta" "c" z c) (p "clienta" "u" z u)
      (p "clienta" "s" z s) (p "clienta" "ca" z ca)
      (p "clienta" "y" z y) (p "" "x" z-0 cookie)
      (p "clienta" "x" z x) (non (invk spk)) (non (invk cpk))
      (non (privk ca)) (pnon p) (uniq sr) (ugen y) (uniq-at cr z 0))
     (false))))

;; The following goal states that if a client uses a cookie to make a request
;; within a TLS connection in which it has authenticated, a server produced
;; the cookie for the user on that client. This prevents cookie stealing as a
;; client cannot have a cookie that authenticates a different user.

(defgoal ca
  (forall
    ((cookie mesg) (p password) (cr sr random32) (spk cpk akey) (c u s ca name)
     (y rndx) (x expt) (z strd) (ppk skey))
    (implies
     (and
      (p "clienta" z 10)
      (p "clienta" "cookie" z (enc cookie (hash ppk (hash (exp (gen) (mul x y))
							   cr sr))))
      (p "clienta" "p" z p)
      (p "clienta" "cr" z cr) (p "clienta" "sr" z sr)
      (p "clienta" "spk" z spk) (p "clienta" "cpk" z cpk)
      (p "clienta" "c" z c) (p "clienta" "u" z u)
      (p "clienta" "s" z s) (p "clienta" "ca" z ca)
      (p "clienta" "y" z y)
      (p "clienta" "x" z x) (non (invk spk)) (non (invk cpk))
      (non (privk ca)) (pnon p) (uniq sr) (ugen y) (uniq-at cr z 0))
     (exists
      ((z0 strd))
      (and
       (p "servera" z0 10)
       (p "servera" "cookie" z0 cookie)
       (p "servera" "u" z0 u)
       (p "servera" "s" z0 s)
       (p "servera" "spk" z0 spk)
       (uniq-at cookie z0 5)
       (fact neq u s))))))
     
;; The following goal states that if a client uses a cookie to make a request
;; within a TLS connection in which it has not authenticated, a server produced
;; the cookie for the user on that client. This prevents cookie stealing as a
;; client cannot have a cookie that authenticates a different user.
;; This goal is satisfied by default, as such a client is precluded by the
;; Session Binding Proxy protocol. This goal results in a dead skeleton.

(defgoal ca
  (forall
   ((cookie mesg) (cr sr random32) (spk cpk akey) (c s ca u name) (y rndx)
    (x expt) (z strd))
    (implies
      (and (p "clientr" z 7) (p "clientr" "cookie" z cookie)
	(p "clientr" "cr" z cr)
        (p "clientr" "sr" z sr) (p "clientr" "spk" z spk)
        (p "clientr" "cpk" z cpk) (p "clientr" "c" z c)
        (p "clientr" "u" z u) (p "clientr" "s" z s)
        (p "clientr" "ca" z ca) 
        (p "clientr" "y" z y) (p "clientr" "x" z x) (non (invk spk))
        (non (invk cpk)) (non (privk ca)) (uniq sr) (ugen y)
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


