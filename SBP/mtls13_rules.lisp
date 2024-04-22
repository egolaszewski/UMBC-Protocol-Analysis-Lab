(defmacro (clients-distinct-from-servers-rules)
    (^
  (defrule clients-servers-distinct1
    (forall
     ((z z-0 strd) (c name))
     (implies
      (and
       (p "clienta" "c" z c)
       (p "clienta" "s" z-0 c))
      (false))))

  (defrule clients-servers-distinct2
    (forall
     ((z z-0 strd) (c name))
     (implies
      (and
       (p "clienta" "c" z c)
       (p "clientr" "s" z-0 c))
      (false))))

  (defrule clients-servers-distinct3
    (forall
     ((z z-0 strd) (c name))
     (implies
      (and
       (p "clientr" "c" z c)
       (p "clientr" "s" z-0 c))
      (false))))

  (defrule clients-servers-distinct4
    (forall
     ((z z-0 strd) (c name))
     (implies
      (and
       (p "clientr" "c" z c)
       (p "clienta" "s" z-0 c))
      (false))))

  (defrule clients-servers-distinct5
    (forall
     ((z z-0 strd) (c name))
     (implies
      (and
       (p "clienta" "c" z c)
       (p "servera" "s" z-0 c))
      (false))))

  (defrule clients-servers-distinct6
    (forall
     ((z z-0 strd) (c name))
     (implies
      (and
       (p "clienta" "c" z c)
       (p "serverr" "s" z-0 c))
      (false))))

  (defrule clients-servers-distinct7
    (forall
     ((z z-0 strd) (c name))
     (implies
      (and
       (p "clientr" "c" z c)
       (p "serverr" "s" z-0 c))
      (false))))

  (defrule clients-servers-distinct8
    (forall
     ((z z-0 strd) (c name))
     (implies
      (and
       (p "clientr" "c" z c)
       (p "servera" "s" z-0 c))
      (false))))

  ))


(defmacro (mtls-secret-unavailable-rules1)
    (^

(defrule tls-secret-unavailable1
  (forall
    ((p password) (cr sr random32) (cpk spk akey) (c s ca u name)
      (x expt) (y rndx) (z z-0 strd))
    (implies
      (and (p "servera" z 4) (p "" z-0 2) (p "servera" "p" z p)
        (p "servera" "cr" z cr) (p "servera" "sr" z sr)
        (p "servera" "spk" z spk) (p "servera" "cpk" z cpk)
        (p "servera" "c" z c) (p "servera" "u" z u)
        (p "servera" "s" z s) (p "servera" "ca" z ca)
        (p "servera" "y" z y) (p "servera" "x" z x)
        (p "" "x" z-0 (exp (gen) (mul x y))) (non (invk cpk))
        (non (invk spk)) (non (privk ca)) (ugen y) (uniq-at sr z 1)
        (fact neq c s))
      (false))))

(defrule tls-secret-unavailable3
  (forall
    ((p password) (cr sr random32) (spk cpk akey) (c s ca u name)
      (x rndx) (y expt) (z z-0 strd))
    (implies
      (and (p "clienta" z 4) (p "" z-0 2) (p "clienta" "p" z p)
        (p "clienta" "cr" z cr) (p "clienta" "sr" z sr)
        (p "clienta" "spk" z spk) (p "clienta" "cpk" z cpk)
        (p "clienta" "c" z c) (p "clienta" "u" z u)
        (p "clienta" "s" z s) (p "clienta" "ca" z ca)
        (p "clienta" "x" z x) (p "clienta" "y" z y)
        (p "" "x" z-0 (exp (gen) (mul x y))) (non (invk spk))
        (non (invk cpk)) (non (privk ca)) (uniq sr) (ugen x)
        (fact neq c s))
      (false))))
))

(defmacro (mtls-secret-unavailable-rules2)
    (^

(defrule tls-secret-unavailable2
  (forall
    ((cookie data) (request httpreq) (cr sr random32) (ppk skey)
      (cpk spk akey) (c s ca name) (x expt) (y rndx) (z z-0 strd))
    (implies
      (and (p "serverr" z 4) (p "" z-0 2)
        (p "serverr" "cookie" z cookie)
        (p "serverr" "request" z request) (p "serverr" "cr" z cr)
        (p "serverr" "sr" z sr) (p "serverr" "ppk" z ppk)
        (p "serverr" "spk" z spk) (p "serverr" "cpk" z cpk)
        (p "serverr" "c" z c) (p "serverr" "s" z s)
        (p "serverr" "ca" z ca) (p "serverr" "y" z y)
        (p "serverr" "x" z x) (p "" "x" z-0 (exp (gen) (mul x y)))
        (non ppk) (non (invk cpk)) (non (invk spk)) (non (privk ca))
        (ugen y) (uniq-at sr z 1) (fact neq c s))
      (false))))



(defrule tls-secret-unavailable4
  (forall
    ((cookie mesg) (cr sr random32) (spk cpk akey) (c s ca u name)
      (cookiestor locn) (x rndx) (y expt) (z z-0 strd))
    (implies
      (and (p "clientr" z 4) (p "" z-0 2)
        (p "clientr" "cookie" z cookie) (p "clientr" "cr" z cr)
        (p "clientr" "sr" z sr) (p "clientr" "spk" z spk)
        (p "clientr" "cpk" z cpk) (p "clientr" "c" z c)
        (p "clientr" "u" z u) (p "clientr" "s" z s)
        (p "clientr" "ca" z ca) (p "clientr" "cookiestor" z cookiestor)
        (p "clientr" "x" z x) (p "clientr" "y" z y)
        (p "" "x" z-0 (exp (gen) (mul x y))) (non (invk spk))
        (non (invk cpk)) (non (privk ca)) (uniq sr) (ugen x)
        (fact neq c s))
      (false))))
))


(defmacro (mtls-hs-traffic-keys-unavailable1)
    (^
     
(defrule client-hs-traffic-key-unavailable1
  (forall
    ((cr sr random32) (spk cpk akey) (c s ca name) (x rndx) (y expt)
      (z z-0 strd))
    (implies
      (and (p "clienta" z 3) (p "" z-0 2) (p "clienta" "cr" z cr)
        (p "clienta" "sr" z sr) (p "clienta" "spk" z spk)
        (p "clienta" "cpk" z cpk) (p "clienta" "c" z c)
        (p "clienta" "s" z s) (p "clienta" "ca" z ca)
        (p "clienta" "x" z x) (p "clienta" "y" z y)
        (p "" "x" z-0 (hash (exp (gen) (mul x y)) "c hs traffic" cr sr))
        (non (invk spk)) (non (invk cpk)) (non (privk ca)) (ugen x)
        (uniq-at cr z 0))
      (false))))

(defrule server-hs-traffic-key-unavailable1
  (forall
    ((cr sr random32) (spk cpk akey) (c s ca name) (x rndx) (y expt)
      (z z-0 strd))
    (implies
      (and (p "clienta" z 3) (p "" z-0 2) (p "clienta" "cr" z cr)
        (p "clienta" "sr" z sr) (p "clienta" "spk" z spk)
        (p "clienta" "cpk" z cpk) (p "clienta" "c" z c)
        (p "clienta" "s" z s) (p "clienta" "ca" z ca)
        (p "clienta" "x" z x) (p "clienta" "y" z y)
        (p "" "x" z-0 (hash (exp (gen) (mul x y)) "s hs traffic" cr sr))
        (non (invk spk)) (non (invk cpk)) (non (privk ca)) (ugen x)
        (uniq-at cr z 0))
      (false))))
))

(defmacro (mtls-hs-traffic-keys-unavailable2)
    (^
     
(defrule client-hs-traffic-key-unavailable2
  (forall
    ((cr sr random32) (spk cpk akey) (c s ca name) (x rndx) (y expt)
      (z z-0 strd))
    (implies
      (and (p "clientr" z 3) (p "" z-0 2) (p "clientr" "cr" z cr)
        (p "clientr" "sr" z sr) (p "clientr" "spk" z spk)
        (p "clientr" "cpk" z cpk) (p "clientr" "c" z c)
        (p "clientr" "s" z s) (p "clientr" "ca" z ca)
        (p "clientr" "x" z x) (p "clientr" "y" z y)
        (p "" "x" z-0 (hash (exp (gen) (mul x y)) "c hs traffic" cr sr))
        (non (invk spk)) (non (invk cpk)) (non (privk ca)) (ugen x)
        (uniq-at cr z 0))
      (false))))

(defrule server-hs-traffic-key-unavailable2
  (forall
    ((cr sr random32) (spk cpk akey) (c s ca name) (x rndx) (y expt)
      (z z-0 strd))
    (implies
      (and (p "clientr" z 3) (p "" z-0 2) (p "clientr" "cr" z cr)
        (p "clientr" "sr" z sr) (p "clientr" "spk" z spk)
        (p "clientr" "cpk" z cpk) (p "clientr" "c" z c)
        (p "clientr" "s" z s) (p "clientr" "ca" z ca)
        (p "clientr" "x" z x) (p "clientr" "y" z y)
        (p "" "x" z-0 (hash (exp (gen) (mul x y)) "s hs traffic" cr sr))
        (non (invk spk)) (non (invk cpk)) (non (privk ca)) (ugen x)
        (uniq-at cr z 0))
      (false))))

(defrule client-hs-traffic-key-unavailable3
  (forall
    ((cr sr random32) (cpk spk akey) (c s ca name) (x expt) (y rndx)
      (z z-0 strd))
    (implies
      (and (p "servera" z 3) (p "" z-0 2) (p "servera" "cr" z cr)
        (p "servera" "sr" z sr) (p "servera" "spk" z spk)
        (p "servera" "cpk" z cpk) (p "servera" "c" z c)
        (p "servera" "s" z s) (p "servera" "ca" z ca)
        (p "servera" "y" z y) (p "servera" "x" z x)
        (p "" "x" z-0 (hash (exp (gen) (mul x y)) "c hs traffic" cr sr))
        (non (invk cpk)) (non (invk spk)) (non (privk ca)) (ugen y)
        (uniq-at sr z 1) (fact neq c s))
      (false))))

(defrule server-hs-traffic-key-unavailable3
  (forall
    ((cr sr random32) (cpk spk akey) (c s ca name) (x expt) (y rndx)
      (z z-0 strd))
    (implies
      (and (p "servera" z 3) (p "" z-0 2) (p "servera" "cr" z cr)
        (p "servera" "sr" z sr) (p "servera" "spk" z spk)
        (p "servera" "cpk" z cpk) (p "servera" "c" z c)
        (p "servera" "s" z s) (p "servera" "ca" z ca)
        (p "servera" "y" z y) (p "servera" "x" z x)
        (p "" "x" z-0 (hash (exp (gen) (mul x y)) "s hs traffic" cr sr))
        (non (invk cpk)) (non (invk spk)) (non (privk ca)) (ugen y)
        (uniq-at sr z 1) (fact neq c s))
      (false))))

(defrule client-hs-traffic-key-unavailable4
  (forall
    ((cr sr random32) (cpk spk akey) (c s ca name) (x expt) (y rndx)
      (z z-0 strd))
    (implies
      (and (p "serverr" z 3) (p "" z-0 2) (p "serverr" "cr" z cr)
        (p "serverr" "sr" z sr) (p "serverr" "spk" z spk)
        (p "serverr" "cpk" z cpk) (p "serverr" "c" z c)
        (p "serverr" "s" z s) (p "serverr" "ca" z ca)
        (p "serverr" "y" z y) (p "serverr" "x" z x)
        (p "" "x" z-0 (hash (exp (gen) (mul x y)) "c hs traffic" cr sr))
        (non (invk cpk)) (non (invk spk)) (non (privk ca)) (ugen y)
        (uniq-at sr z 1) (fact neq c s))
      (false))))

(defrule server-hs-traffic-key-unavailable4
  (forall
    ((cr sr random32) (cpk spk akey) (c s ca name) (x expt) (y rndx)
      (z z-0 strd))
    (implies
      (and (p "serverr" z 3) (p "" z-0 2) (p "serverr" "cr" z cr)
        (p "serverr" "sr" z sr) (p "serverr" "spk" z spk)
        (p "serverr" "cpk" z cpk) (p "serverr" "c" z c)
        (p "serverr" "s" z s) (p "serverr" "ca" z ca)
        (p "serverr" "y" z y) (p "serverr" "x" z x)
        (p "" "x" z-0 (hash (exp (gen) (mul x y)) "s hs traffic" cr sr))
        (non (invk cpk)) (non (invk spk)) (non (privk ca)) (ugen y)
        (uniq-at sr z 1) (fact neq c s))
      (false))))
)
  )

(defmacro (server-analysis-rules)
    (^

(defrule tls-s-hs-traffic-key-unavailable
  (forall
    ((p password) (cr sr random32) (cpk spk akey) (c s ca u name)
      (x expt) (y rndx) (z z-0 strd))
    (implies
      (and (p "servera" z 4) (p "" z-0 2) (p "servera" "p" z p)
        (p "servera" "cr" z cr) (p "servera" "sr" z sr)
        (p "servera" "spk" z spk) (p "servera" "cpk" z cpk)
        (p "servera" "c" z c) (p "servera" "u" z u)
        (p "servera" "s" z s) (p "servera" "ca" z ca)
        (p "servera" "y" z y) (p "servera" "x" z x)
        (p "" "x" z-0 (hash (exp (gen) (mul x y)) "s hs traffic" cr sr))
        (non (invk cpk)) (non (invk spk)) (non (privk ca)) (ugen y)
        (uniq-at sr z 1) (fact neq c s))
      (false))))

(defrule tls-c-hs-traffic-key-unavailable
  (forall
    ((p password) (cr sr random32) (spk cpk akey) (c u s ca name)
      (x rndx) (y expt) (z z-0 strd))
    (implies
      (and (p "clienta" z 4) (p "" z-0 2) (p "clienta" "p" z p)
        (p "clienta" "cr" z cr) (p "clienta" "sr" z sr)
        (p "clienta" "spk" z spk) (p "clienta" "cpk" z cpk)
        (p "clienta" "c" z c) (p "clienta" "u" z u)
        (p "clienta" "s" z s) (p "clienta" "ca" z ca)
        (p "clienta" "x" z x) (p "clienta" "y" z y)
        (p "" "x" z-0 (hash (exp (gen) (mul x y)) "c hs traffic" cr sr))
        (non (invk spk)) (non (invk cpk)) (non (privk ca)) (pnon p)
        (uniq sr) (ugen x) (uniq-at cr z 0))
      (false))))

(defrule tls-c-ap-traffic-key-unavailable
  (forall
    ((p password) (cr sr random32) (cpk spk akey) (c s ca u name)
      (x expt) (y rndx) (z z-0 strd))
    (implies
      (and (p "servera" z 4) (p "" z-0 2) (p "servera" "p" z p)
        (p "servera" "cr" z cr) (p "servera" "sr" z sr)
        (p "servera" "spk" z spk) (p "servera" "cpk" z cpk)
        (p "servera" "c" z c) (p "servera" "u" z u)
        (p "servera" "s" z s) (p "servera" "ca" z ca)
        (p "servera" "y" z y) (p "servera" "x" z x)
        (p "" "x" z-0
          (hash "c ap traffic" cr sr
            (hash (exp (gen) (mul x y)) "derived"))) (non (invk cpk))
        (non (invk spk)) (non (privk ca)) (ugen y) (uniq-at sr z 1)
        (fact neq c s))
      (false))))

(defrule tls-s-ap-traffic-key-unavailable
  (forall
    ((p password) (cr sr random32) (cpk spk akey) (c s ca u name)
      (x expt) (y rndx) (z z-0 strd))
    (implies
      (and (p "servera" z 4) (p "" z-0 2) (p "servera" "p" z p)
        (p "servera" "cr" z cr) (p "servera" "sr" z sr)
        (p "servera" "spk" z spk) (p "servera" "cpk" z cpk)
        (p "servera" "c" z c) (p "servera" "u" z u)
        (p "servera" "s" z s) (p "servera" "ca" z ca)
        (p "servera" "y" z y) (p "servera" "x" z x)
        (p "" "x" z-0
          (hash "s ap traffic" cr sr
            (hash (exp (gen) (mul x y)) "derived"))) (non (invk cpk))
        (non (invk spk)) (non (privk ca)) (ugen y) (uniq-at sr z 1)
        (fact neq c s))
      (false))))

))
