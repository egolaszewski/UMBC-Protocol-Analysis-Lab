(herald "Session Binding Protocol with mTLS 1.3/server's perspective analysis (uses the modified server as implemented and tested in the paper and the cookie authentication model (ca.scm) which showed the cookie stealing attack)."
	(bound 16)
	(try-old-strands)
	)

(include "TLS1.3_macros.lisp") ;; 3 message exchange by combining TLS messages.
(include "mtls13_rules.lisp") ;; Proven rules to control CPSA analysis.

;; The following macro is a shortcut to create the TLS master secret.

(defmacro (MS exponent1 exponent2)
  (MasterSecret (HandshakeSecret (DHpublic exponent1) exponent2)))


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
     (cr sr random32) ;; cr - client random, sr - server random for TLS
     (x rndx) ;; client's Diffie-Hellman secret
     (y expt) ;; server's Diffie-Hellman secret
     (spk cpk akey) ;; server's and client's public key's
     (p password) ;; user's password
     (cookie mesg) ;; authentication cookie provided by the server
     (any mesg)
     (cookiestor locn) ;; client storage of authentication cookie
     (request httpreq)
     (response httpdata)
     )
    (trace
     (mTLS send recv cr sr x y s spk (invk spk) c cpk (invk cpk) ca
	  (HandshakeSecret (DHpublic y) x)) ;; establish TLS session with server
     (send (enc "login" u p (ClientApKey cr sr (MS y x))))
     (recv (enc "login-successful" cookie (ServerApKey cr sr (MS y x))))
     (load cookiestor any)            ;; store authentication cookie associated
     (stor cookiestor (cat "client store" u s cookie)) ;; with the server s
     (send (enc cookie request (ClientApKey cr sr (MS y x))))
     (recv (enc response (ServerApKey cr sr (MS y x))))
     )
    (uniq-gen x)
    )

  (defrole clientr ;; Role where client makes requests, but already has an
                   ;; authentication cookie (does not need to authenticate)
    
    (vars
     (c u s ca name) ;; c - client u - username, s - server,
                     ;; ca - certificate authority
     (cr sr random32) ;; cr - client random, sr - server random for TLS
     (x rndx) ;; client's Diffie-Hellman secret
     (y expt) ;; server's Diffie-Hellman secret
     (spk cpk akey) ;; server's and client's public key's
     (p password) ;; user's password
     (cookie mesg) ;; authentication cookie provided by the server
     (cookiestor locn) ;; client storage of authentication cookie
     (request httpreq)
     (response httpdata)
     )
    (trace
     (mTLS send recv cr sr x y s spk (invk spk) c cpk (invk cpk) ca
	  (HandshakeSecret (DHpublic y) x)) ;; establish TLS session with server
     (load cookiestor (cat "client store" u s cookie));; retrieve authentication
                                                      ;; cookie associated
                                                      ;; with the server s
     (send (enc cookie request (ClientApKey cr sr (MS y x))))
     (recv (enc response (ServerApKey cr sr (MS y x))))
     )
    (uniq-gen x)
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
     (c u s ca name) ;; c - client u - username, s - server,
                     ;; ca - certificate authority
     (cr sr random32) ;; cr - client random, sr - server random for TLS
     (y rndx) ;; client's Diffie-Hellman secret
     (x expt) ;; server's Diffie-Hellman secret
     (spk cpk akey) ;; server's and client's public key's
     (p password) ;; user's password
     (cookie data) ;; authentication cookie provided by the server
     (ppk skey) ;; proxy private key
     (any mesg)
     (authstor locn) ;; server storage of clients authentication cookie
     (request httpreq)
     (response httpdata)
     )
    (trace
     (mTLS recv send cr sr x y s spk (invk spk) c cpk (invk cpk) ca
	  (HandshakeSecret (DHpublic x) y)) ;; establish TLS session with client
     (recv (enc "login" u p (ClientApKey cr sr (MS x y))))
     (send (enc "login-successful"
		(enc cookie (hash ppk (MS x y)))
		(ServerApKey cr sr (MS x y))))
     (load authstor any)                             ;; store authentication 
     (stor authstor (cat "server store" s u cookie)) ;; cookie associated with u
     (recv (enc (enc cookie (hash ppk (MS x y)))
		request (ClientApKey cr sr (MS x y))))
     (send (enc response (ServerApKey cr sr (MS x y))))
     )
    (facts (neq u s))
    (uniq-gen y)
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
     (c u s ca name) ;; c - client u - username, s - server,
                     ;; ca - certificate authority
     (cr sr random32) ;; cr - client random, sr - server random for TLS
     (y rndx) ;; client's Diffie-Hellman secret
     (x expt) ;; server's Diffie-Hellman secret
     (spk cpk akey) ;; server's and client's public key's
     (p password) ;; user's password
     (cookie data) ;; authentication cookie provided by the server
     (ppk skey)
     (any mesg)
     (authstor locn) ;; server storage of clients authentication cookie
     (request httpreq)
     (response httpdata)
     )
    (trace
     (mTLS recv send cr sr x y s spk (invk spk) c cpk (invk cpk) ca
	  (HandshakeSecret (DHpublic x) y)) ;; establish TLS session with client
     (recv (enc (enc cookie (hash ppk (MS x y)))
		request (ClientApKey cr sr (MS x y))))
     (load authstor (cat "server store" s u cookie)) ;; retrieve user cookie
     (send (enc response (ServerApKey cr sr (MS x y))))
     )
    (facts (neq u s))
    (uniq-gen y)
    (non-orig ppk) ;; Proxy private key is only known by the proxy or the server
                   ;; in this case as the proxy and server are implemented
                   ;; together.
    (gen-st (cat "server store" s u cookie))
    )

  (clients-distinct-from-servers-rules)
  (server-analysis-rules)

  (lang
   (random32 atom)
   (random48 atom)
   (password atom)
   (httpreq atom)
   (httpdata atom)
   )
  )

;; The following skeletons determine the theorems that the server supports

(defskeleton ca
  (vars (c s ca name) (x expt) (y rndx) (cr sr random32) (cpk spk akey))
  (defstrand servera 8 (s s) (spk spk) (c c) (cpk cpk) (ca ca) (cr cr) (sr sr)
    (x x) (y y))
;;  (deflistener (hash "c ap traffic" cr sr (hash (exp (gen) (mul x y)) "derived")))
  (non-orig (privk ca) (invk spk) (invk cpk))
  (uniq-orig sr)
  (facts (neq c s))
  )

;; Server Theorems

;; The following theorem is True. It guarantees that the client is authenticated
;; and the client and server agree that the cookie is for the authenticated user
;; As the client authentication is not necessarily tied to the user, we haven't
;; proven that a client machine could not provide a stolen username and
;; password. If the client and user are associated with each other through the
;; certificate, then and only then can we assume that the user isn't stolen. In
;; a case similar to SSH machine authentication, it could still be possible to
;; use a stolen username and password, but that is outside the scope of our
;; proof. 

(defgoal ca
  (forall
   ((z strd) (cookie data) (u c s ca name) (sr random32) (cpk spk akey)
    (y rndx) (x expt) (ppk skey))
   (implies
    (and
     (p "servera" z 8)
     (p "servera" "ca" z ca)
     (p "servera" "s" z s)
     (p "servera" "c" z c)
     (p "servera" "u" z u)
     (p "servera" "x" z x)
     (p "servera" "y" z y)
     (p "servera" "sr" z sr)
     (p "servera" "cpk" z cpk)
     (p "servera" "spk" z spk)
     (p "servera" "ppk" z ppk)
     (p "servera" "cookie" z cookie)
     (non (privk ca))
     (non (invk spk))
     (non (invk cpk))
     (non ppk)
     (ugen y)
     (uniq-at sr z 1)
     (uniq-at cookie z 4)
     (fact neq c s))
    (exists
     ((z0 strd))
     (and
      (p "clienta" z0 8)
      (p "clienta" "cookie" z0 (enc cookie (hash ppk (MS y x))))
      (p "clienta" "u" z0 u)
      (p "clienta" "s" z0 s)
      (fact neq u s))))))

;; The following goal is for completeness as the SBP protocol prevents the 
;; server from using a cookie in a different TLS session from the one in which
;; it was created. No skeletons are produced. The theorem is vacuously true.

(defgoal ca
  (forall
   ((z strd) (cookie data) (u c s ca name) (sr random32) (cpk spk akey) (y rndx)
    (x expt) (ppk skey))
   (implies
    (and
     (p "serverr" z 4)
     (p "serverr" "ca" z ca)
     (p "serverr" "s" z s)
     (p "serverr" "c" z c)
     (p "serverr" "u" z u)
     (p "serverr" "x" z x)
     (p "serverr" "y" z y)
     (p "serverr" "sr" z sr)
     (p "serverr" "cpk" z cpk)
     (p "serverr" "spk" z spk)
     (p "serverr" "ppk" z ppk)
     (p "serverr" "cookie" z cookie)
     (non (privk ca))
     (non (invk spk))
     (non (invk cpk))
     (non ppk)
     (ugen y)
     (uniq-at sr z 1)
     (fact neq c s))
    (exists
     ((z0 strd))
     (and
      (p "clientr" z0 4)
      (p "clientr" "cookie" z0 (enc cookie (hash ppk (MS y x))))
      (p "clientr" "u" z0 u)
      (p "clientr" "s" z0 s)
      (fact neq u s))))))
