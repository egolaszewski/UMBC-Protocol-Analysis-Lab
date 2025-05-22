(herald "Secure DNA Query Protocol without Cert. Chaining"
  (comment "This model does not feature any certificate chaining.")
  (algebra diffie-hellman)
  (reverse-nodes)
)

(defmacro (Token subject-id subject-pubk signer-id signer-pubk data)
  (cat 
    (cat "Token" subject-id subject-pubk signer-id signer-pubk data)
    (enc (hash subject-id subject-pubk signer-id signer-pubk data) (privk signer-id))
  )
)

(defmacro (Certificate subject-id subject-pubk signer-id signer-pubk data)
  (cat 
    (cat "Certificate" subject-id subject-pubk signer-id signer-pubk data)
    (enc (hash subject-id subject-pubk signer-id signer-pubk data) (privk signer-id))
  )
)

(defmacro (Bundle subject-id signer-id)
  (cat "Bundle"
    (Token subject-id (pubk subject-id) signer-id (pubk signer-id) "data")
    (Certificate subject-id (pubk subject-id) signer-id (pubk signer-id) "data")
  )
)

(defprotocol secure-dna-query diffie-hellman
  (defrole synth-client-2-ks
    (vars
      (ks-ch chan)
      (r-s r-k random256)
      (c-id k-id m-root i-root name)
      (t cookie)
      (seq blind sign rndx)
      (seqstor locn)
      (any mesg)
    )
    (trace
      (send ks-ch (cat r-s "keyserver" k-id (Bundle c-id m-root)))
      (recv ks-ch (cat t r-k (Bundle k-id i-root)
        (enc (hash "server-mutauth" r-k r-s (Bundle k-id i-root)) (privk k-id))))
      (send ks-ch (cat t "nSeq"
        (enc (hash "client-mutauth" r-k r-s (Bundle c-id m-root)) (privk c-id))))
      ;; (recv s-ch "OK")
      (send ks-ch (cat t (exp (gen) (mul seq blind))))
      (recv ks-ch (cat (exp (gen) (mul seq blind sign))))
      (load seqstor any)
      (stor seqstor (exp (gen) (mul seq sign blind (rec blind))))
    )
    (uniq-orig r-s)
    (uniq-gen blind seq)
  )
  (defrole synth-client-2-db
    (vars
      (db-ch chan)
      (r-s r-d random256)
      (c-id d-id m-root i-root name)
      (t cookie)
      (resp query-response)
      (seqstor locn)
      (signed expt)
    )
    (trace
      (load seqstor (exp (gen) signed))
      (send db-ch (cat r-s "screen" (Bundle c-id m-root)))
      (recv db-ch (cat t r-d (Bundle d-id i-root)
        (enc (hash "server-mutauth" r-d r-s (Bundle d-id i-root)) (privk d-id))))
      (send db-ch (cat t
        (enc (hash "client-mutauth" r-d r-s (Bundle c-id m-root)) (privk c-id))))
      ;; (recv db-ch "OK")
      (send db-ch (cat t (exp (gen) signed)))
      (recv db-ch resp)
    )
    (gen-st (exp (gen) signed))
    (uniq-orig r-s)
  )
  (defrole key-server
    (vars
      (ks-ch chan)
      (r-s r-k random256)
      (c-id k-id m-root i-root name)
      (t cookie)
      (seq blind sign rndx)
      (seq-blinded expt)
    )
    (trace
      (recv ks-ch (cat r-s "keyserver" k-id (Bundle c-id m-root)))
      (send ks-ch (cat t r-k (Bundle k-id i-root)
        (enc (hash "server-mutauth" r-k r-s (Bundle k-id i-root)) (privk k-id))))
      (recv ks-ch (cat t "nSeq"
        (enc (hash "client-mutauth" r-k r-s (Bundle c-id m-root)) (privk c-id))))
      ;; (send s-ch "OK")
      (recv ks-ch (cat t (exp (gen) (mul seq blind))))
      (send ks-ch (cat (exp (gen) (mul seq blind sign))))
    )
    (uniq-orig t)
    (uniq-gen sign)
  )
  (defrole database
    (vars
      (db-ch chan)
      (r-s r-d random256)
      (c-id d-id m-root i-root name)
      (t cookie)
      (resp query-response)
      (signed expt)
    )
    (trace
      (recv db-ch (cat r-s "screen" (Bundle c-id m-root)))
      (send db-ch (cat t r-d (Bundle d-id i-root)
        (enc (hash "server-mutauth" r-d r-s (Bundle d-id i-root)) (privk d-id))))
      (recv db-ch (cat t
        (enc (hash "client-mutauth" r-d r-s (Bundle c-id m-root)) (privk c-id))))
      ;; (send db-ch "OK")
      (recv db-ch (cat t (exp (gen) signed)))
      (send db-ch resp)
    )
    (uniq-orig t)
  )
  (lang
    (random256 atom)
    (cookie atom)
    (query-response atom)
  )
)

;; Basic query synth-client-2-ks perspective.
(defskeleton secure-dna-query
  (vars
    (ks-ch chan)
    (c-id k-id m-root i-root name)
    (r-s random256)
    (seq blind rndx)
  )
  (defstrandmax synth-client-2-ks
    (ks-ch ks-ch)
    (c-id c-id) (k-id k-id) (m-root m-root) (i-root i-root)
    (r-s r-s)
    (seq seq) (blind blind)
  )
  (auth ks-ch)
  (conf ks-ch)
  (non-orig (privk c-id) (privk k-id) (privk m-root) (privk i-root))
  (uniq-orig r-s)
  (facts (neq seq blind))
)

;; Basic query key-server perspective.
(defskeleton secure-dna-query
  (vars
    (ks-ch chan)
    (c-id k-id m-root i-root name)
    (r-k random256)
    (t cookie)
    (sign rndx)
  )
  (defstrandmax key-server
    (ks-ch ks-ch)
    (c-id c-id) (k-id k-id) (m-root m-root) (i-root i-root)
    (r-k r-k)
    (t t)
    (sign sign)
  )
  (auth ks-ch)
  (conf ks-ch)
  (non-orig (privk c-id) (privk k-id) (privk m-root) (privk i-root))
  (uniq-orig r-k)
  (uniq-orig t)
  (uniq-gen sign)
)

;; Basic query synth-client-2-db perspective.
(defskeleton secure-dna-query
  (vars
    (db-ch chan)
    (c-id d-id m-root i-root name)
    (r-s random256)
  )
  (defstrandmax synth-client-2-db
    (db-ch db-ch)
    (c-id c-id) (d-id d-id) (m-root m-root) (i-root i-root)
    (r-s r-s)
  )
  (auth db-ch)
  (conf db-ch)
  (non-orig (privk c-id) (privk d-id) (privk m-root) (privk i-root))
  (uniq-orig r-s)
)

;; Basic query databse perspective.
(defskeleton secure-dna-query
  (vars
    (db-ch chan)
    (c-id d-id m-root i-root name)
    (r-d random256)
  )
  (defstrandmax database
    (db-ch db-ch)
    (c-id c-id) (d-id d-id) (m-root m-root) (i-root i-root)
    (r-d r-d)
  )
  (auth db-ch)
  (conf db-ch)
  (non-orig (privk c-id) (privk d-id) (privk m-root) (privk i-root))
  (uniq-orig r-d)
)

;; Sequence listener synth-client perspective.
(defskeleton secure-dna-query
  (vars
    (ks-ch chan)
    (c-id k-id m-root i-root name)
    (r-s random256)
    (seq blind sign rndx)
  )
  (defstrandmax synth-client-2-ks
    (ks-ch ks-ch)
    (c-id c-id) (k-id k-id) (m-root m-root) (i-root i-root)
    (r-s r-s)
    (seq seq) (blind blind) (sign sign)
  )
  (deflistener (exp (gen) seq))
  (auth ks-ch)
  (conf ks-ch)
  (non-orig (privk c-id) (privk k-id) (privk m-root) (privk i-root))
  (uniq-orig r-s)
  (uniq-gen seq blind)
  (facts (neq seq blind sign))
)

;; Sequence listener key-server perspective.
(defskeleton secure-dna-query
  (vars
    (ks-ch chan)
    (c-id k-id m-root i-root name)
    (r-k random256)
    (t cookie)
    (sign seq rndx)
  )
  (defstrandmax key-server
    (ks-ch ks-ch)
    (c-id c-id) (k-id k-id) (m-root m-root) (i-root i-root)
    (r-k r-k)
    (t t)
    (sign sign)
  )
  (deflistener (exp (gen) seq))
  (auth ks-ch)
  (conf ks-ch)
  (non-orig (privk c-id) (privk k-id) (privk m-root) (privk i-root))
  (uniq-orig r-k)
  (uniq-orig t)
  (uniq-gen sign seq)
)