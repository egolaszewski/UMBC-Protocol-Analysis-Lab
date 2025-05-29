(herald "Secure DNA Query Protocol without Cert. Chaining"
  (comment "This model does not feature any certificate chaining.")
  (algebra diffie-hellman)
)

(defmacro (Token subject-id signer-id data)
  (cat 
    (cat "Token" 
    subject-id (pubk subject-id) signer-id (pubk signer-id) data)
    (enc (hash
    subject-id (pubk subject-id) signer-id (pubk signer-id) data)
  (invk (pubk signer-id)))
  )
)

(defmacro (ServerMutauthReq
  server-id client-id infrastructure-root
  server-nonce client-nonce cookie
  server-bundle)
  (cat cookie server-nonce
    (Token server-id infrastructure-root server-bundle)
    (enc
      (hash "server-mutauth" server-nonce client-nonce
      (Token server-id infrastructure-root server-bundle))
      (privk server-id)
    )
  )
)

(defmacro (ClientMutauthResp
  client-id server-id manufacturer-root
  server-nonce client-nonce cookie
  client-bundle)
  (cat cookie "nSeq"
    (enc
      (hash "client-mutauth" server-nonce client-nonce
      (Token client-id manufacturer-root client-bundle))
      (privk client-id)
    )
  )
)

(defmacro (Client2Keyserver 
  d1 d2 channel
  client-id server-id manufacturer-root infrastructure-root
  client-nonce server-nonce cookie
  client-bundle server-bundle
  sequence blinding key)
  (^
    (d1 channel
      (cat client-nonce "keyserver" server-id
        (Token client-id manufacturer-root client-bundle)))
    (d2 channel (ServerMutauthReq
      server-id client-id infrastructure-root
      server-nonce client-nonce cookie
      server-bundle))
    (d1 channel (ClientMutauthResp
      client-id server-id manufacturer-root
      server-nonce client-nonce cookie
      client-bundle))
    ;; (recv s-ch "OK")
    (d1 channel
      (cat cookie (exp (gen) (mul sequence blinding))))
    (d2 channel
      (cat (exp (gen) (mul sequence blinding key))))
  )
)

(defmacro (Client2Database 
  d1 d2 channel
  client-id database-id manufacturer-root infrastructure-root
  client-nonce database-nonce cookie
  client-bundle database-bundle
  sequence
  resp)
  (^
    (d1 channel
      (cat client-nonce "screen"
        (Token client-id manufacturer-root client-bundle)))
    (d2 channel (ServerMutauthReq
      database-id client-id infrastructure-root
      database-nonce client-nonce cookie
      database-bundle))
    (d1 channel (ClientMutauthResp
      client-id database-id manufacturer-root
      database-nonce client-nonce cookie
      client-bundle))
    ;; (recv database-ch "OK")
    (d1 channel
      (cat cookie sequence))
    (d2 channel
      (cat resp))
  )
)

(defprotocol secure-dna-query diffie-hellman
  (defrole synth-client
    (vars
      (keyserver-ch database-ch chan) 
      (r-s r-s2 r-k r-d t t2 random256)
      (c-id k-id d-id m-root i-root name)
      (seq blind k rndx)
      (b-s b-k b-d bundle-data)
      (resp query-response)
    )
    (trace
      (Client2Keyserver send recv keyserver-ch
        c-id k-id m-root i-root
        r-s r-k t
        b-s b-k
        seq blind k)
      (Client2Database send recv database-ch
        c-id d-id m-root i-root
        r-s2 r-d t2
        b-s b-d
        (exp (gen) (mul seq blind k (rec blind)))
        resp)
    )
    (uniq-orig r-s)
    (uniq-orig r-s2)
    (uniq-gen blind seq)
  )
  (defrole key-server
    (vars
      (keyserver-ch chan)
      (r-s r-k t random256)
      (c-id k-id m-root i-root name)
      (seq blind k rndx)
      (seq-blinded expt)
      (b-s b-k bundle-data)
    )
    (trace
      (Client2Keyserver recv send keyserver-ch
        c-id k-id m-root i-root
        r-s r-k t
        b-s b-k
        seq blind k)
    )
    (uniq-orig t)
    (uniq-gen k)
  )
  (defrole database
    (vars
      (database-ch chan)
      (r-s r-d t random256)
      (c-id d-id m-root i-root name)
      (resp query-response)
      (signed expt)
      (b-s b-d bundle-data)
    )
    (trace
      (Client2Database recv send database-ch
        c-id d-id m-root i-root
        r-s r-d t
        b-s b-d
        (exp (gen) signed)
        resp)
    )
    (uniq-orig t)
  )
  (lang
    (random256 atom)
    (query-response atom)
    (bundle-data atom)
  )
)

;; Authentication query synth-client perspective.
(defskeleton secure-dna-query
  (vars
    (keyserver-ch database-ch chan)
    (c-id k-id d-id m-root i-root name)
    (r-s r-s2 random256)
    (seq blind rndx)
  )
  (defstrandmax synth-client
    (keyserver-ch keyserver-ch) (database-ch database-ch)
    (c-id c-id) (d-id d-id) (k-id k-id) (m-root m-root) (i-root i-root)
    (r-s r-s) (r-s2 r-s2)
    (seq seq) (blind blind)
  )
  (auth keyserver-ch database-ch)
  (conf keyserver-ch database-ch)
  (non-orig
  (privk c-id)
  (privk k-id)
  (privk d-id)
  (privk m-root)
  (privk i-root)
  )
  (uniq-orig r-s r-s2)
  (facts (neq seq blind))
)

;; Authentication query key-server perspective.
(defskeleton secure-dna-query
  (vars
    (keyserver-ch chan)
    (c-id k-id m-root i-root name)
    (r-k t random256)
    (k rndx)
  )
  (defstrandmax key-server
    (keyserver-ch keyserver-ch)
    (c-id c-id) (k-id k-id) (m-root m-root) (i-root i-root)
    (r-k r-k)
    (t t)
    (k k)
  )
  (non-orig (privk c-id) (privk k-id) (privk m-root) (privk i-root))
  (uniq-orig r-k)
  (uniq-orig t)
  (uniq-gen k)
)

;; Authentication query databse perspective.
(defskeleton secure-dna-query
  (vars
    (database-ch chan)
    (c-id d-id m-root i-root name)
    (r-d random256)
  )
  (defstrandmax database
    (database-ch database-ch)
    (c-id c-id) (d-id d-id) (m-root m-root) (i-root i-root)
    (r-d r-d)
  )
  (non-orig (privk c-id) (privk d-id) (privk m-root) (privk i-root))
  (uniq-orig r-d)
)
