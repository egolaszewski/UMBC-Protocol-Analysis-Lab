(herald "Session Binding Protocol with mTLS 1.3and TLS Exporter Binding/client's perspective analysis (uses the modified server as implemented and tested in the paper and the cookie authentication model (ca.scm) which showed the cookie stealing attack)."
	(bound 12)
	(limit 16000)
	)

(include "TLS1.3_macros.lisp") ;; 3 message exchange by combining TLS messages.
(include "mtls_rules.lisp") ;; Proven rules to control CPSA analysis.


;; The following macro is a shortcut to create the TLS master secret.

(defmacro (MS exponent1 exponent2)
  (MasterSecret (HandshakeSecret (DHpublic exponent1) exponent2)))

(defmacro (TLS_Exporter ms label cr sr ctx)
  (hash ms label cr sr ctx))

(defprotocol ca basic

  ;; This protocol is basic cookie authentication of requests. Once a user logs
  ;; in with their username and password, the server provides an authentication
  ;; cookie to the client that the client can provide to authenticate requests
  ;; to the server without the need to authenticate again with the username
  ;; and password. (This protocol contains the SBP wrapper around the cookie.)

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
		(hash cookie (TLS_Exporter (MS x y) "EXPORTER-Channel-Binding" cr sr (cat u s)))
		(ServerApKey cr sr (MS x y))))
     (load authstor any)                             ;; store authentication 
     (stor authstor (cat "server store" s u cookie)) ;; cookie associated with u
     (recv (enc (hash cookie (TLS_Exporter (MS x y) "EXPORTER-Channel-Binding" cr sr (cat u s)))
		request (ClientApKey cr sr (MS x y))))
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
     (c u s ca name) ;; c - client u - username, s - server,
                     ;; ca - certificate authority
     (cr sr random32) ;; cr - client random, sr - server random for TLS
     (y rndx) ;; client's Diffie-Hellman secret
     (x expt) ;; server's Diffie-Hellman secret
     (spk cpk akey) ;; server's and client's public key's
     (p password) ;; user's password
     (cookie data) ;; authentication cookie provided by the server
     (any mesg)
     (authstor locn) ;; server storage of clients authentication cookie
     (request httpreq)
     (response httpdata)
     )
    (trace
     (mTLS recv send cr sr x y s spk (invk spk) c cpk (invk cpk) ca
	  (HandshakeSecret (DHpublic x) y)) ;; establish TLS session with client
     (recv (enc (hash cookie (TLS_Exporter (MS x y) "EXPORTER-Channel-Binding" cr sr (cat u s)))
		request (ClientApKey cr sr (MS x y))))
     (load authstor (cat "server store" s u cookie)) ;; retrieve user cookie
     (send (enc response (ServerApKey cr sr (MS x y))))
     )
    (facts (neq u s))
    (uniq-gen y)
    (gen-st (cat "server store" s u cookie))
    )

  ;; Rules to control the analysis

  (clients-distinct-from-servers-rules)
   
  (defrule partial-server-merge ;
    (forall ((z0 z1 strd) (spk akey) (s ca name))
            (implies
	     (and (p "serverr" z0 2)
		  (p "serverr" z1 2)
		  (p "serverr" "spk" z0 spk)
		  (p "serverr" "spk" z1 spk)
		  (p "serverr" "s" z0 s)
		  (p "serverr" "s" z1 s)
      (p "serverr" "ca" z0 ca)
		  (p "serverr" "ca" z1 ca))
	     (= z0 z1))))
   
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

;; The following skeletons determine the theorems that the server supports

(defskeleton ca
  (vars (c s ca name) (cr sr random32) (spk cpk akey) (cookie data))
  (defstrand servera 9 (s s) (c c) (ca ca) (cr cr) (sr sr) (spk spk) (cpk cpk)
    (cookie cookie))
  (non-orig (privk ca) (invk spk) (invk cpk))
  (uniq-orig sr cookie)
  )

;; Cookie Stealing Prevention Theorems

;; The following goal states that a cookie created during the authentication of
;; a client cannot be obtained by the adversary.

(defgoal ca
  (forall
    ((cookie data) (p password) (cr sr random32) (spk cpk akey) (c u s ca name)
     (x rndx) (y expt) (z z-0 strd))
    (implies
     (and
      (p "clienta" z 9) (p "" z-0 2) (p "clienta" "cookie" z cookie)
      (p "clienta" "p" z p)
      (p "clienta" "cr" z cr) (p "clienta" "sr" z sr)
      (p "clienta" "spk" z spk) (p "clienta" "cpk" z cpk)
      (p "clienta" "c" z c) (p "clienta" "u" z u)
      (p "clienta" "s" z s) (p "clienta" "ca" z ca)
      (p "clienta" "y" z y) (p "" "x" z-0 cookie)
      (p "clienta" "x" z x) (non (invk spk)) (non (invk cpk))
      (non (privk ca)) (pnon p) (uniq sr) (ugen x) (uniq-at cr z 0))
     (false))))

;; The following goal states that if a client uses a cookie to make a request
;; within a TLS connection in which it has authenticated, a server produced
;; the cookie for the user on that client. This prevents cookie stealing as a
;; client cannot have a cookie that authenticates a different user.

(defgoal ca
  (forall
   ((z strd) (cookie data) (c u s ca name) (spk cpk akey) (cr sr random32)
    (ppk skey) (x rndx) (y expt))
   (implies
    (and
     (p "clienta" z 9)
     (p "clienta" "cookie" z (enc cookie (hash ppk (MS y x))))
     (p "clienta" "c" z c)
     (p "clienta" "u" z u)
     (p "clienta" "s" z s)
     (p "clienta" "spk" z spk)
     (p "clienta" "cpk" z cpk)
     (p "clienta" "ca" z ca)
     (p "clienta" "cr" z cr)
     (p "clienta" "sr" z sr)
     (p "clienta" "x" z x)
     (p "clienta" "y" z y)
     (non (privk ca))
     (non (invk cpk))
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
	    
;; The following goal states that if a client uses a cookie to make a request
;; within a TLS connection in which it has not authenticated, a server produced
;; the cookie for the user on that client. This prevents cookie stealing as a
;; client cannot have a cookie that authenticates a different user.
;; This goal is satisfied by default, as such a client is precluded by the
;; Session Binding Proxy protocol. This goal results in a dead skeleton.

(defgoal ca
  (forall
   ((z strd) (cookie data) (c u s ca name) (cr sr random32) (x rndx) (y expt)
    (spk cpk akey) (ppk skey))
   (implies
    (and
     (p "clientr" z 6)
     (p "clientr" "cookie" z (enc cookie (hash ppk (MS y x))))
     (p "clientr" "c" z c)
     (p "clientr" "u" z u)
     (p "clientr" "s" z s)
     (p "clientr" "spk" z spk)
     (p "clientr" "cpk" z cpk)
     (p "clientr" "ca" z ca)
     (p "clientr" "cr" z cr)
     (p "clientr" "sr" z sr)
     (p "clientr" "x" z x)
     (p "clientr" "y" z y)
     (non (privk ca))
     (non (invk cpk))
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
	    
