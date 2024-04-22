(herald "UAF using TLS1.3 with exporter channel binding."
  (algebra diffie-hellman))

(include "TLS1.3_macros.lisp") ; 4 message exchange by combining TLS messages.
(include "UAF_macros.lisp")

(defprotocol uaf-exporter-tls13 diffie-hellman
  ;; Client roles.
  (defrole client-reg
    (vars
      (username auth server ca appid name)
      (challenge text)
      (cr sr data) ;; TLS nonces. cr: client random, sr: server random
      (authk akey) ;; Authenticator's asymmetric key for this registration.
      (spk akey) ;; Server's public key.
      (x rndx) ;; Client's Diffie-Hellman secret for TLS 1.3.
      (y expt) ;; Server's Diffie-Hellman secret for TLS 1.3.
    )
    (trace
      (TLS send recv cr sr x y server spk (invk spk) ca (HandshakeSecret (DHpublic y) x))
      (UAF_Reg_Exporter_TLS13 send recv username appid challenge auth authk cr sr spk y x)
    )
    (uniq-gen x)
  )
  (defrole client-auth
    (vars
      (server ca appid name)
      (challenge text)
      (cr sr data) ;; TLS nonces. cr: client random, sr: server random
      (authk akey)
      (spk akey) ;; Server's public key.
      (x rndx) ;; Client's Diffie-Hellman secret for TLS 1.3.
      (y expt) ;; Server's Diffie-Hellman secret for TLS 1.3.
    )
    (trace
      (TLS send recv cr sr x y server spk (invk spk) ca (HandshakeSecret (DHpublic y) x))
      (UAF_Auth_Exporter_TLS13 send recv appid challenge authk cr sr spk y x)
    )
    (uniq-gen x)
  )
  ;; Server roles.
  (defrole server-reg
    (vars
      (username auth server ca appid name)
      (challenge text)
      (cr sr data) ;; TLS nonces. cr: client random, sr: server random
      (authk akey)
      (spk akey) ;; Server's public key.
      (x expt) ;; Client's Diffie-Hellman secret for TLS 1.3.
      (y rndx) ;; Server's Diffie-Hellman secret for TLS 1.3.
    )
    (trace
      (TLS recv send cr sr x y server spk (invk spk) ca (HandshakeSecret (DHpublic x) y))
      (UAF_Reg_Exporter_TLS13 recv send username appid challenge auth authk cr sr spk x y)
    )
    (uniq-gen y)
  )
  (defrole server-auth
    (vars
      (auth server ca appid name)
      (challenge text)
      (cr sr data) ;; TLS nonces. cr: client random, sr: server random
      (authk akey)
      (spk akey) ;; Server's public key.
      (x expt) ;; Client's Diffie-Hellman secret for TLS 1.3.
      (y rndx) ;; Server's Diffie-Hellman secret for TLS 1.3.
    )
    (trace
      (TLS recv send cr sr x y server spk (invk spk) ca (HandshakeSecret (DHpublic x) y))
      (UAF_Auth_Exporter_TLS13 recv send appid challenge authk cr sr spk x y)
    )
    (uniq-gen y)
  )
  ;; Custom sorts.
)

;; Client-reg perspective skeleton.
(defskeleton uaf-exporter-tls13
  (vars
    (server ca name)
    (cr sr data)
    (authk spk akey)
  )
  (defstrandmax client-reg
    (server server) (ca ca) (cr cr) (authk authk) (spk spk) (sr sr))
  (non-orig (privk ca) (invk spk) (invk authk))
  (uniq-orig cr)
;;  (uniq-orig sr) ;; Prevents multiple instances of the same server interacting with the client.
)

;; Client-auth perspective skeleton.
(defskeleton uaf-exporter-tls13
  (vars
    (server ca name)
    (cr sr data)
    (authk spk akey)
  )
  (defstrandmax client-auth
    (server server) (ca ca) (cr cr) (authk authk) (spk spk) (sr sr))
  (non-orig (privk ca) (invk spk) (invk authk))
  (uniq-orig cr)
;;  (uniq-orig sr) ;; Prevents multiple instances of the same server interacting with the client.
)

;; Server-reg perspective skeleton.
(defskeleton uaf-exporter-tls13
  (vars
    (username server ca name)
    (sr data)
    (challenge text)
    (authk spk akey)
  )
  (defstrandmax server-reg
    (username username) (server server) (ca ca) (sr sr) (challenge challenge) (authk authk) (spk spk))
  (non-orig (privk ca) (invk spk) (invk authk))
  (uniq-orig username challenge sr)
)

;; Server-auth perspective skeleton.
(defskeleton uaf-exporter-tls13
  (vars
    (server ca name)
    (sr data)
    (challenge text)
    (authk spk akey)
  )
  (defstrandmax server-auth
    (server server) (ca ca) (sr sr) (challenge challenge) (authk authk) (spk spk))
  (non-orig (privk ca) (invk spk) (invk authk))
  (uniq-orig challenge sr)
)

;; Combined perspective skeleton.
(defskeleton uaf-exporter-tls13
  (vars
    (username server ca name)
    (sr data)
    (challenge text)
    (authk spk akey)
  )
  (defstrandmax server-reg
    (username username) (server server) (ca ca) (sr sr) (challenge challenge) (authk authk) (spk spk))
  (defstrandmax client-reg
    (username username) (server server) (ca ca) (sr sr) (challenge challenge) (authk authk) (spk spk))  
  (non-orig (privk ca) (invk spk) (invk authk))
  (uniq-orig username challenge sr)
)

;; Combined perspective skeleton.
(defskeleton uaf-exporter-tls13
  (vars
    (server ca name)
    (sr data)
    (challenge text)
    (authk spk akey)
  )
  (defstrandmax server-auth
    (server server) (ca ca) (sr sr) (challenge challenge) (authk authk) (spk spk))
  (defstrandmax client-auth
    (server server) (ca ca) (sr sr) (challenge challenge) (authk authk) (spk spk))
  (non-orig (privk ca) (invk spk) (invk authk))
  (uniq-orig challenge sr)
)

(defgoal uaf-exporter-tls13
  (forall
    ((cr sr data) (challenge text) (authk spk akey)
      (server ca appid name) (x rndx) (z strd))
    (implies
      (and
        (p "client-reg" z 5)
        (p "client-reg" "cr" z cr)
        (p "client-reg" "sr" z sr)
        (p "client-reg" "challenge" z challenge)
        (p "client-reg" "authk" z authk)
        (p "client-reg" "spk" z spk)
        (p "client-reg" "appid" z appid)
        (p "client-reg" "server" z server)
        (p "client-reg" "ca" z ca)
        (p "client-reg" "x" z x)
        (non (invk authk))
        (non (invk spk))
        (non (privk ca))
;;	(uniq sr)
        (ugen x)
        (uniq-at cr z 0))
      (exists ((z-0 strd))
        (and
          (p "server-reg" z-0 4)
          (p "server-reg" "challenge" z-0 challenge)
          (p "server-reg" "appid" z-0 appid)
          (p "server-reg" "server" z-0 server))))))


(defgoal uaf-exporter-tls13
  (forall
    ((cr sr data) (challenge text) (authk spk akey)
      (server ca appid name) (x rndx) (z strd))
    (implies
      (and
        (p "client-auth" z 5)
        (p "client-auth" "cr" z cr)
        (p "client-auth" "sr" z sr)
        (p "client-auth" "challenge" z challenge)
        (p "client-auth" "authk" z authk)
        (p "client-auth" "spk" z spk)
        (p "client-auth" "appid" z appid)
        (p "client-auth" "server" z server)
        (p "client-auth" "ca" z ca)
        (p "client-auth" "x" z x)
        (non (invk authk))
        (non (invk spk))
        (non (privk ca))
;;        (uniq sr)
        (ugen x)
        (uniq-at cr z 0))
      (exists ((z-0 strd))
        (and 
          (p "server-auth" z-0 4)
          (p "server-auth" "challenge" z-0 challenge)
          (p "server-auth" "appid" z-0 appid)
          (p "server-auth" "server" z-0 server))))))

(defgoal uaf-exporter-tls13
  (forall
    ((sr data) (challenge text) (authk spk akey) (server ca appid name)
      (y rndx) (z strd))
    (implies
      (and
        (p "server-reg" z 5)
        (p "server-reg" "sr" z sr)
        (p "server-reg" "challenge" z challenge)
        (p "server-reg" "authk" z authk) 
        (p "server-reg" "spk" z spk)
        (p "server-reg" "server" z server)
        (p "server-reg" "appid" z appid)
        (p "server-reg" "ca" z ca)
        (p "server-reg" "y" z y)
        (non (invk authk))
        (non (invk spk))
        (non (privk ca))
        (ugen y)
        (uniq-at challenge z 3)
        (uniq-at sr z 1))
      (exists
        ((z-0 strd))
        (and
          (p "client-reg" z-0 5)
          (p "client-reg" "challenge" z-0 challenge)
          (p "client-reg" "server" z-0 server)
          (p "client-reg" "appid" z-0 appid))))))

(defgoal uaf-exporter-tls13
  (forall
    ((sr data) (challenge text) (authk spk akey) (server ca appid name)
      (y rndx) (z strd))
    (implies
      (and
        (p "server-auth" z 5)
        (p "server-auth" "sr" z sr)
        (p "server-auth" "challenge" z challenge)
        (p "server-auth" "authk" z authk) 
        (p "server-auth" "spk" z spk)
        (p "server-auth" "server" z server)
        (p "server-auth" "appid" z appid)
        (p "server-auth" "ca" z ca)
        (p "server-auth" "y" z y)
        (non (invk authk))
        (non (invk spk))
        (non (privk ca))
        (ugen y)
        (uniq-at challenge z 3)
        (uniq-at sr z 1))
      (exists
        ((z-0 strd))
        (and
          (p "client-auth" z-0 5)
          (p "client-auth" "challenge" z-0 challenge)
          (p "client-auth" "server" z-0 server)
          (p "client-auth" "appid" z-0 appid))))))
