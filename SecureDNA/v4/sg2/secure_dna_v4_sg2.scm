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

(defgoal secure-dna-query
  (forall
    (
      (b-s b-k b-d bundle-data)
      (resp query-response)
      (r-s r-s2 r-k r-d t t2 random256)
      (c-id k-id d-id m-root i-root name)
      (keyserver-ch database-ch chan)
      (seq blind k rndx)
      (z z-0 strd)
    )
    (implies
      (and 
        (p "synth-client" z 10)
        (p "" z-0 2)
        (p "synth-client" "b-s" z b-s)
        (p "synth-client" "b-k" z b-k)
        (p "synth-client" "b-d" z b-d)
        (p "synth-client" "resp" z resp)
        (p "synth-client" "r-s" z r-s)
        (p "synth-client" "r-s2" z r-s2)
        (p "synth-client" "r-k" z r-k)
        (p "synth-client" "r-d" z r-d)
        (p "synth-client" "t" z t)
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
        (p "synth-client" "k" z k)
        (p "" "x" z-0 seq)
        (non (privk c-id))
        (non (privk k-id))
        (non (privk d-id))
        (non (privk m-root))
        (non (privk i-root))
        (ugen seq)
        (ugen blind)
        (uniq r-s)
        (uniq r-s2)
        (auth keyserver-ch)
        (auth database-ch)
        (conf keyserver-ch)
        (conf database-ch)
        (fact neq seq blind))
      (false))))

(defgoal secure-dna-query
  (forall
    (
      (b-s b-k bundle-data)
      (r-s r-k t random256)
      (c-id k-id m-root i-root name)
      (keyserver-ch chan)
      (seq blind k rndx)
      (z z-0 strd)
    )
    (implies
      (and 
        (p "key-server" z 5) 
        (p "" z-0 2)
        (p "key-server" "b-s" z b-s)
        (p "key-server" "b-k" z b-k)
        (p "key-server" "r-s" z r-s)
        (p "key-server" "r-k" z r-k)
        (p "key-server" "t" z t)
        (p "key-server" "c-id" z c-id)
        (p "key-server" "k-id" z k-id)
        (p "key-server" "m-root" z m-root)
        (p "key-server" "i-root" z i-root)
        (p "key-server" "keyserver-ch" z keyserver-ch)
        (p "key-server" "seq" z blind)
        (p "key-server" "blind" z seq)
        (p "key-server" "k" z k)
        (p "" "x" z-0 seq)
        (non (privk c-id))
        (non (privk k-id))
        (non (privk m-root))
        (non (privk i-root))
        (pnon seq)
        (ugen k)
        (uniq t)
        (fact neq seq blind))
      (false))))