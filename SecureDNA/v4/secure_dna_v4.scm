(herald "Secure DNA Query Protocol without Cert. Chaining"
  (comment "This model does not feature any certificate chaining.")
  (algebra diffie-hellman)
)

(defmacro (Token subject-id subject-pubk signer-id data)
  (cat 
    "Token" subject-id subject-pubk signer-id (pubk signer-id) data
    (enc
      (hash "Token" subject-id subject-pubk signer-id (pubk signer-id) data)
      (privk signer-id)
    )
  )
)

(defmacro (ServerMutauthReq
  server-id server-pubk infrastructure-root
  server-nonce client-nonce cookie
  server-bundle)
  (cat cookie server-nonce
    (Token server-id server-pubk infrastructure-root server-bundle)
    (enc
      (hash "server-mutauth" server-nonce client-nonce
      (Token server-id server-pubk infrastructure-root server-bundle))
      (invk server-pubk)
    )
  )
)

(defmacro (ClientMutauthResp
  client-id client-pubk manufacturer-root
  server-nonce client-nonce cookie
  client-bundle)
  (cat cookie "nSeq"
    (enc
      (hash "client-mutauth" server-nonce client-nonce
      (Token client-id client-pubk manufacturer-root client-bundle))
      (invk client-pubk)
    )
  )
)

(defmacro (Client2Keyserver 
  d1 d2 channel
  client-id server-id manufacturer-root infrastructure-root
  client-nonce server-nonce cookie
  client-bundle server-bundle
  client-pubk server-pubk
  sequence blinding key)
  (^
    (d1 channel
      (cat client-nonce "keyserver" server-id
        (Token client-id client-pubk manufacturer-root client-bundle)))
    (d2 channel (ServerMutauthReq
      server-id server-pubk infrastructure-root
      server-nonce client-nonce cookie
      server-bundle))
    (d1 channel (ClientMutauthResp
      client-id client-pubk manufacturer-root
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
  client-pubk database-pubk
  sequence
  resp)
  (^
    (d1 channel
      (cat client-nonce "screen"
        (Token client-id client-pubk manufacturer-root client-bundle)))
    (d2 channel (ServerMutauthReq
      database-id database-pubk infrastructure-root
      database-nonce client-nonce cookie
      database-bundle))
    (d1 channel (ClientMutauthResp
      client-id client-pubk manufacturer-root
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
      (k-pubk d-pubk akey)
    )
    (trace
      (Client2Keyserver send recv keyserver-ch
        c-id k-id m-root i-root
        r-s r-k t
        b-s b-k
	(pubk c-id) k-pubk
        seq blind k)
      (Client2Database send recv database-ch
        c-id d-id m-root i-root
        r-s2 r-d t2
        b-s b-d
	(pubk c-id) d-pubk
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
      (s-pubk akey)
    )
    (trace
      (Client2Keyserver recv send keyserver-ch
        c-id k-id m-root i-root
        r-s r-k t
        b-s b-k
	s-pubk (pubk k-id)
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
      (s-pubk akey)
    )
    (trace
      (Client2Database recv send database-ch
        c-id d-id m-root i-root
        r-s r-d t
        b-s b-d
	s-pubk (pubk d-id)
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

;; Query response agreement goal. (Synthclient perspective)
(defgoal secure-dna-query
  (forall (
      (resp query-response)
      (r-s r-s2 r-k r-d t2 random256)
      (c-id k-id d-id m-root i-root name)
      (keyserver-ch database-ch chan) 
      (seq blind rndx)
      (z strd))
    (implies
      (and 
        (p "synth-client" z 10)
        (p "synth-client" "resp" z resp)
        (p "synth-client" "r-s" z r-s)
        (p "synth-client" "r-s2" z r-s2)
        (p "synth-client" "r-k" z r-k)
        (p "synth-client" "r-d" z r-d)
        (p "synth-client" "t2" z t2)
        (p "synth-client" "c-id" z c-id)
        (p "synth-client" "k-id" z k-id)
        (p "synth-client" "d-id" z d-id)
        (p "synth-client" "m-root" z m-root)
        (p "synth-client" "i-root" z i-root)
        (p "synth-client" "keyserver-ch" z keyserver-ch)
        (p "synth-client" "database-ch" z database-ch)
        (p "synth-client" "seq" z seq)
        (p "synth-client" "blind" z blind)
        (non (privk c-id))
        (non (privk k-id))
        (non (privk d-id))
        (non (privk m-root))
        (non (privk i-root))
        (ugen seq)
        (ugen blind)
        (uniq-at r-s z 0)
        (uniq-at r-s2 z 5)
        (auth keyserver-ch)
        (auth database-ch)
        (conf keyserver-ch)
        (conf database-ch)
        (fact neq seq blind))
      (exists (
          (z-1 strd))
        (and
          (p "database" z-1 5)
          (p "database" "r-s" z-1 r-s2)
          (p "database" "r-d" z-1 r-d)
          (p "database" "t" z-1 t2)
          (p "database" "c-id" z-1 c-id)
          (p "database" "d-id" z-1 d-id)
          (p "database" "m-root" z-1 m-root)
          (p "database" "i-root" z-1 i-root)
          (p "database" "database-ch" z-1 database-ch)
          (p "database" "resp" z-1 resp))))))

;; Query response agreement goal (Database perspective)
(defgoal secure-dna-query
  (forall (
      (resp query-response)
      (r-s r-d t random256)
      (c-id d-id m-root i-root name)
      (database-ch chan) 
      (z strd))
    (implies
      (and 
        (p "database" z 5)
        (p "database" "r-s" z r-s)
        (p "database" "r-d" z r-d)
        (p "database" "t" z t)
        (p "database" "c-id" z c-id)
        (p "database" "d-id" z d-id)
        (p "database" "m-root" z m-root)
        (p "database" "i-root" z i-root)
        (p "database" "database-ch" z database-ch)
        (p "database" "resp" z resp)
        (non (privk c-id))
        (non (privk d-id))
        (non (privk m-root))
        (non (privk i-root))
        (uniq-at t z 1)
        (uniq-at r-d z 1))
      (exists (
          (z-1 strd))
        (and
          (p "synth-client" z-1 10)
          (p "synth-client" "resp" z-1 resp)
          (p "synth-client" "r-s2" z-1 r-s)
          (p "synth-client" "r-d" z-1 r-d)
          (p "synth-client" "t2" z-1 t)
          (p "synth-client" "c-id" z-1 c-id)
          (p "synth-client" "d-id" z-1 d-id)
          (p "synth-client" "m-root" z-1 m-root)
          (p "synth-client" "i-root" z-1 i-root)
          (p "synth-client" "database-ch" z-1 database-ch))))))
