(herald "Session Binding Protocol with TLS 1.3 (uses the modified server as implemented and tested in the paper and the cookie authentication model (ca.scm) which showed the cookie stealing attack)."
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
     (cookie mesg) ;; authentication cookie provided by the server
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
     (cookie mesg) ;; authentication cookie provided by the server
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
                   ;; requests. This role differs from the same role in ca.scm
                   ;; as it has been modified to transform the cookie created by
                   ;; the server by encrypting the cookie with a key derived 
                   ;; from the TLS master secret and a secret proxy key. The 
                   ;; client receives the transformed cookie.
    
    (vars
     (u s ca name) ;; u - username, s - server, ca - certificate authority
     (cr sr random32) ;; cr - client random, sr - server random for TLS
     (y rndx) ;; client's Diffie-Hellman secret
     (x expt) ;; server's Diffie-Hellman secret
     (spk akey) ;; server's public key
     (p password) ;; user's password
     (cookie data) ;; authentication cookie provided by the server
     (ppk skey) ;; proxy private key
     (any mesg)
     (authstor locn) ;; server storage of clients authentication cookie
     (request httpreq)
     (response httpdata)
     )
    (trace
     (TLS recv send cr sr x y s spk (invk spk) ca
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
     (u s ca name) ;; u - username, s - server, ca - certificate authority
     (cr sr random32) ;; cr - client random, sr - server random for TLS
     (y rndx) ;; client's Diffie-Hellman secret
     (x expt) ;; server's Diffie-Hellman secret
     (spk akey) ;; server's public key
     (p password) ;; user's password
     (cookie data) ;; authentication cookie provided by the server
     (ppk skey)
     (any mesg)
     (authstor locn) ;; server storage of clients authentication cookie
     (request httpreq)
     (response httpdata)
     )
    (trace
     (TLS recv send cr sr x y s spk (invk spk) ca
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
  (vars (u s ca name) (spk akey) (p password) (cr sr random32))
  (defstrandmax clienta (u u) (p p) (s s) (spk spk) (ca ca) (cr cr) (sr sr))
  (pen-non-orig p)
  (non-orig (privk ca) (invk spk))
  (uniq-orig cr)
  (uniq-orig sr) ;; This is only included to prevent multiple runs of the same
  ;; server interacting with the same client.
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
  (vars (u s ca name) (spk akey) (p password) (cr sr random32) (cookie data))
  (defstrandmax clienta (u u) (p p) (s s) (spk spk) (ca ca) (cr cr) (sr sr)
    (cookie cookie))
  (deflistener cookie)
  (pen-non-orig p)
  (non-orig (privk ca) (invk spk))
  (uniq-orig cr)
  (uniq-orig sr) ;; This is only included to prevent multiple runs of the same
  ;; server interacting with the same client.
  )

;; Test of a client making a request over a new TLS connection using the cookie
;; for authentication. With the binding of a cookie to the TLS session in which
;; the cookie was created, the skeleton is dead because the cookie created by 
;; the server cannot be decrypted from the value received from the client as
;; the TLS master secret used in the key is different. This demonstrates that
;; binding the cookie to the TLS session prevents cookie stealing.

(defskeleton ca
  (vars (s ca name) (cr sr random32) (spk akey))
  (defstrandmax clientr (s s) (spk spk) (ca ca) (cr cr) (sr sr))
  (non-orig (privk ca) (invk spk))
  (uniq-orig cr)
  (uniq-orig sr) ;; This is only included to prevent multiple runs of the same
  ;; server interacting with the same client.
  )

;; The following skeletons determine the theorems that the server supports

(defskeleton ca
  (vars (s ca name) (cr sr random32) (spk akey) (ppk skey) (cookie data))
  (defstrand servera 8 (s s) (ca ca) (cr cr) (sr sr) (spk spk) (ppk ppk)
    (cookie cookie))
  (non-orig (privk ca) (invk spk) ppk)
  (uniq-orig sr cookie)
  )

(defskeleton ca
  (vars (s ca name) (cr sr random32) (spk akey) (ppk skey) (cookie data))
  (defstrand serverr 5 (s s) (ca ca) (cr cr) (sr sr) (spk spk) (ppk ppk)
    (cookie cookie))
  (non-orig (privk ca) (invk spk) ppk)
  (uniq-orig sr)
  )


	    
;; Cookie Stealing Prevention Theorems

(defgoal ca
  (forall
   ((z strd) (cookie data) (u s ca name) (spk akey) (cr sr random32) (ppk skey)
    (x rndx) (y expt))
   (implies
    (and
     (p "clienta" z 9)
     (p "clienta" "cookie" z (enc cookie (hash ppk (MS y x))))
     (p "clienta" "u" z u)
     (p "clienta" "s" z s)
     (p "clienta" "spk" z spk)
     (p "clienta" "ca" z ca)
     (p "clienta" "cr" z cr)
     (p "clienta" "sr" z sr)
     (p "clienta" "x" z x)
     (p "clienta" "y" z y)
     (non (privk ca))
     (non (invk spk))
     (non ppk)
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
   ((z strd) (cookie data) (u s ca name) (cr sr random32) (x rndx) (y expt)
    (spk akey) (ppk skey))
   (implies
    (and
     (p "clientr" z 6)
     (p "clientr" "cookie" z (enc cookie (hash ppk (MS y x))))
     (p "clientr" "u" z u)
     (p "clientr" "s" z s)
     (p "clientr" "spk" z spk)
     (p "clientr" "ca" z ca)
     (p "clientr" "cr" z cr)
     (p "clientr" "sr" z sr)
     (p "clientr" "x" z x)
     (p "clientr" "y" z y)
     (non (privk ca))
     (non (invk spk))
     (non ppk)
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
	    
