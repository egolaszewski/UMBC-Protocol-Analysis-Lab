(herald "Cookie Authentication with TLS 1.3"
	(bound 12)
	)

(include "TLS1.3_macros.lisp") ; 3 message exchange by combining TLS messages.

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
     (u s ca name) ;; u - username, s - server, ca - certificate authority
     (cr sr random32) ;; cr - client random, sr - server random for TLS
     (x rndx) ;; client's Diffie-Hellman secret
     (y expt) ;; server's Diffie-Hellman secret
     (spk akey) ;; server's public key
     (p password) ;; user's password
     (cookie data) ;; authentication cookie provided by the server
     (any mesg)
     (cookiestor locn) ;; client storage of authentication cookie
     (request httpreq)
     (response httpdata)
     )
    (trace
     (TLS send recv cr sr x y s spk (invk spk) ca
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
     (u s ca name) ;; u - username, s - server, ca - certificate authority
     (cr sr random32) ;; cr - client random, sr - server random for TLS
     (x rndx) ;; client's Diffie-Hellman secret
     (y expt) ;; server's Diffie-Hellman secret
     (spk akey) ;; server's public key
     (p password) ;; user's password
     (cookie data) ;; authentication cookie provided by the server
     (cookiestor locn) ;; client storage of authentication cookie
     (request httpreq)
     (response httpdata)
     )
    (trace
     (TLS send recv cr sr x y s spk (invk spk) ca
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
                   ;; requests
    (vars
     (u s ca name) ;; u - username, s - server, ca - certificate authority
     (cr sr random32) ;; cr - client random, sr - server random for TLS
     (y rndx) ;; client's Diffie-Hellman secret
     (x expt) ;; server's Diffie-Hellman secret
     (spk akey) ;; server's public key
     (p password) ;; user's password
     (cookie data) ;; authentication cookie provided by the server
     (any mesg)
     (authstor locn) ;; server storage of clients authentication cookie
     (request httpreq)
     (response httpdata)
     )
    (trace
     (TLS recv send cr sr x y s spk (invk spk) ca
	  (HandshakeSecret (DHpublic x) y)) ;; establish TLS session with client
     (recv (enc "login" u p (ClientApKey cr sr (MS x y))))
     (send (enc "login-successful" cookie (ServerApKey cr sr (MS x y))))
     (load authstor any)                             ;; store authentication 
     (stor authstor (cat "server store" s u cookie)) ;; cookie associated with u
     (recv (enc cookie request (ClientApKey cr sr (MS x y))))
     (send (enc response (ServerApKey cr sr (MS x y))))
     )
    (facts (neq u s))
    (uniq-gen y)
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
     (y rndx) ;; client's Diffie-Hellman secret
     (x expt) ;; server's Diffie-Hellman secret
     (spk akey) ;; server's public key
     (p password) ;; user's password
     (cookie data) ;; authentication cookie provided by the server
     (any mesg)
     (authstor locn) ;; server storage of clients authentication cookie
     (request httpreq)
     (response httpdata)
     )
    (trace
     (TLS recv send cr sr x y s spk (invk spk) ca
	  (HandshakeSecret (DHpublic x) y)) ;; establish TLS session with client
     (recv (enc cookie request (ClientApKey cr sr (MS x y))))
     (load authstor (cat "server store" s u cookie)) ;; retrieve user cookie
     (send (enc response (ServerApKey cr sr (MS x y))))
     )
    (facts (neq u s))
    (uniq-gen y)
    (gen-st (cat "server store" s u cookie))
    )

  (lang
   (random32 atom)
   (random48 atom)
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
  (vars (u s ca name) (p password) (cr sr random32) (spk akey) (cookie data))
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
  (vars (s ca name) (cr sr random32) (spk akey) (cookie data))
  (defstrand servera 8 (s s) (ca ca) (cr cr) (sr sr) (spk spk) (cookie cookie))
  (non-orig (privk ca) (invk spk))
  (uniq-orig sr cookie)
  )

(defskeleton ca
  (vars (s ca name) (cr sr random32) (spk akey) (cookie data))
  (defstrand serverr 5 (s s) (ca ca) (cr cr) (sr sr) (spk spk) (cookie cookie))
  (non-orig (privk ca) (invk spk))
  (uniq-orig sr)
  )



;; Cookie Stealing Prevention Theorems

(defgoal ca
  (forall
    ((any mesg) (cookie data) (response httpdata) (request httpreq)
      (p password) (cr sr random32) (spk akey) (x rndx) (u s ca name)
      (cookiestor locn) (z z-0 strd))
    (implies
      (and (p "clienta" z 9) (p "" z-0 2) (p "clienta" "any" z any)
        (p "clienta" "cookie" z cookie)
        (p "clienta" "response" z response) (p "clienta" "spk" z spk)
        (p "clienta" "request" z request) (p "clienta" "p" z p)
        (p "clienta" "cr" z cr) (p "clienta" "sr" z sr)
        (p "clienta" "x" z x) (p "clienta" "u" z u)
        (p "clienta" "s" z s) (p "clienta" "ca" z ca)
        (p "clienta" "cookiestor" z cookiestor) (p "" "x" z-0 cookie)
        (non (invk spk)) (non (privk ca)) (pnon p) (uniq sr)
        (uniq-at cr z 0) (ugen-at x z 0))
      (false))))

(defgoal ca
  (forall
   ((z strd) (cookie data) (u s ca name) (cr sr random32) (spk akey) (x rndx))
   (implies
    (and
     (p "clienta" z 9)
     (p "clienta" "cookie" z cookie)
     (p "clienta" "u" z u)
     (p "clienta" "s" z s)
     (p "clienta" "spk" z spk)
     (p "clienta" "ca" z ca)
     (p "clienta" "cr" z cr)
     (p "clienta" "sr" z sr)
     (p "clienta" "x" z x)
     (non (privk ca))
     (non (invk spk))
     (uniq sr)
     (uniq-at cr z 0)
     (ugen-at x z 0))
    (exists
     ((z0 strd))
     (and
      (p "servera" z0 9)
      (p "servera" "cookie" z0 cookie)
      (p "servera" "u" z0 u)
      (p "servera" "s" z0 s)
      (uniq-at cookie z0 4)
      (fact neq u s))))))
	    
(defgoal ca
  (forall
   ((z strd) (cookie data) (u s ca name) (cr sr random32) (spk akey) (x rndx))
   (implies
    (and
     (p "clientr" z 6)
     (p "clientr" "cookie" z cookie)
     (p "clientr" "u" z u)
     (p "clientr" "s" z s)
     (p "clientr" "spk" z spk)
     (p "clientr" "ca" z ca)
     (p "clientr" "cr" z cr)
     (p "clientr" "sr" z sr)
     (p "clientr" "x" z x)
     (non (privk ca))
     (non (invk spk))
     (uniq sr)
     (uniq-at cr z 0)
     (ugen-at x z 0))
    (exists
     ((z0 strd))
     (and
      (p "servera" z0 7)
      (p "servera" "cookie" z0 cookie)
      (p "servera" "u" z0 u)
      (p "servera" "s" z0 s)
      (uniq-at cookie z0 4)
      (fact neq u s))))))
	    
