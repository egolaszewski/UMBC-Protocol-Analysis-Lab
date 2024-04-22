(herald "UAF using TLS1.3 with dual (server/client) exporter binding."
  (algebra diffie-hellman))

;; In this version, the authenticator is treated as if it is embedded in the client. This is
;; consistent with the FIDO specifications in which they view the authenticator as a part of
;; the client system, such as a finger print reader, camara for facial recognition, TPM, etc.
;; that is used to authenticate the user on the client's system (phone, computer, etc.) that
;; is running the application. In this case there are no protocols that connect to the
;; authenticator, only function calls within the operating system. As we are not evaluating
;; the CTAP protocols, this model provides a better view of the bindings between the client
;; and the server by including the authentication responses directly from the client. This
;; highlights the TLS channel and its relationship to the FIDO authentication protocol. 

(include "TLS1.3_macros.lisp") ; 4 message exchange by combining TLS messages.
(include "UAF_macros.lisp") ; Two message exchange by combining UAF messages.

(defprotocol uaf-dualbinding-tls13 diffie-hellman
  ;; Client roles.
  (defrole client-reg
    (vars
      (username auth server ca appid name)
      (challenge text)
      (cr sr data) ;; TLS nonces. cr: client random, sr: server random
      (authk spk akey) ;; Authenticator's asymmetric key for this registration.
      (x rndx)
      (y expt)
    )
    (trace
      (TLS send recv cr sr x y server spk (invk spk) ca (HandshakeSecret (DHpublic y) x))
      (recv (enc username appid challenge
        (UAF_Exporter (MS y x) "dual-binding" cr sr (cat username appid challenge server))
        (ServerApKey cr sr (MS y x))))
      (send (enc
        (UAF_KH (invk authk) username)
        (UAF_Attestation (cat auth authk (hash appid challenge
          (UAF_Exporter (MS y x) "dual-binding" cr sr (cat username appid challenge server)))) 
        (invk authk))
        (ClientApKey cr sr (MS y x))))
    )
    (uniq-gen x)
  )
  (defrole client-auth
    (vars
      (auth server ca appid name)
      (challenge text)
      (cr sr data) ;; TLS nonces. cr: client random, sr: server random
      (authk spk akey) ;; Authenticator's asymmetric key for this registration.
      (x rndx)
      (y expt)
    )
    (trace
      (TLS send recv cr sr x y server spk (invk spk) ca (HandshakeSecret (DHpublic y) x))
      (recv (enc appid challenge
        (UAF_Exporter (MS y x) "dual-binding" cr sr (cat appid challenge server))
        (ServerApKey cr sr (MS y x))))
      (send (enc
        (UAF_Attestation (cat auth authk (hash appid challenge
          (UAF_Exporter (MS y x) "dual-binding" cr sr (cat appid challenge server)))) 
        (invk authk))
        (ClientApKey cr sr (MS y x))))
    )
    (uniq-gen x)
  )
  ;; Server roles.
  (defrole server-reg
    (vars
      (username auth server ca appid name)
      (challenge text)
      (cr sr data) ;; TLS nonces. cr: client random, sr: server random
      (authk spk akey) ;; Authenticator's asymmetric key for this registration.
      (x expt)
      (y rndx)
    )
    (trace
      (TLS recv send cr sr x y server spk (invk spk) ca (HandshakeSecret (DHpublic x) y))
      (send (enc username appid challenge
        (UAF_Exporter (MS x y) "dual-binding" cr sr (cat username appid challenge server))
        (ServerApKey cr sr (MS x y))))
      (recv (enc
        (UAF_KH (invk authk) username)
        (UAF_Attestation (cat auth authk (hash appid challenge
          (UAF_Exporter (MS x y) "dual-binding" cr sr (cat username appid challenge server)))) 
        (invk authk))
        (ClientApKey cr sr (MS x y))))
    )
   (uniq-gen y)
  )
  (defrole server-auth
    (vars
      (auth server ca appid name)
      (challenge text)
      (cr sr data) ;; TLS nonces. cr: client random, sr: server random
      (authk spk akey) ;; Authenticator's asymmetric key for this registration.
      (x expt)
      (y rndx)
    )
    (trace
      (TLS recv send cr sr x y server spk (invk spk) ca (HandshakeSecret (DHpublic x) y))
      (send (enc appid challenge
        (UAF_Exporter (MS x y) "dual-binding" cr sr (cat appid challenge server))
        (ServerApKey cr sr (MS x y))))
      (recv (enc
        (UAF_Attestation (cat auth authk (hash appid challenge
          (UAF_Exporter (MS x y) "dual-binding" cr sr (cat appid challenge server)))) 
        (invk authk))
        (ClientApKey cr sr (MS x y))))
    )
    (uniq-gen y)
  )
)

(defgoal uaf-dualbinding-tls13
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


(defgoal uaf-dualbinding-tls13
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

(defgoal uaf-dualbinding-tls13
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

(defgoal uaf-dualbinding-tls13
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