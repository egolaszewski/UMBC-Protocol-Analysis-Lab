(herald "Secure DNA Query Protocol without Cert. Chaining"
  (comment "This model does not feature any certificate chaining.")
  (algebra diffie-hellman)
  (limit 50000)
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

(defmacro (Client2KeyserverExemption 
  d1 d2 channel
  client-id server-id manufacturer-root infrastructure-root
  client-nonce server-nonce cookie
  client-bundle server-bundle
  sequence exemptSeq blinding key)
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
    (d1 channel
      (cat cookie (exp (gen) (mul exemptSeq blinding))))
    (d2 channel
      (cat (exp (gen) (mul sequence blinding key))))
    (d2 channel
      (cat (exp (gen) (mul exemptSeq blinding key))))
  )
)

(defmacro (Client2DatabaseExempt 
  d1 d2 channel
  client-id database-id manufacturer-root infrastructure-root biosafety-id
  client-nonce database-nonce cookie
  client-bundle database-bundle exemption-bundle
  sequence exemptSeq resp
  authcode)
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
    (d1 channel
      (cat (Token client-id biosafety-id exemption-bundle)
        authcode exemptSeq))
    (d2 channel
      (cat resp))
  )
)

(defprotocol secure-dna-query diffie-hellman
  (defrole synth-client-exempt
    (vars
      (keyserver-ch database-ch chan) 
      (r-s r-s2 r-k r-d t t2 authcode random256)
      (c-id k-id d-id m-root i-root b-id name)
      (seq exempt blind k rndx)
      (b-s b-k b-d b-bio bundle-data)
      (resp query-response)
    )
    (trace
      (Client2KeyserverExemption send recv keyserver-ch
        c-id k-id m-root i-root
        r-s r-k t
        b-s b-k
        seq exempt blind k)
      (Client2DatabaseExempt send recv database-ch
        c-id d-id m-root i-root b-id
        r-s2 r-d t2
        b-s b-d b-bio
        (exp (gen) (mul seq blind k (rec blind)))
        (exp (gen) (mul exempt blind k (rec blind)))
        resp authcode)
    )
    (uniq-orig r-s)
    (uniq-orig r-s2)
    (pen-non-orig authcode)
    (uniq-gen blind exempt seq)
  )
  (defrole key-server-exempt
    (vars
      (keyserver-ch chan)
      (r-s r-k t random256)
      (c-id k-id m-root i-root name)
      (seq exempt blind k rndx)
      (seq-blinded expt)
      (b-s b-k bundle-data)
    )
    (trace
      (Client2KeyserverExemption recv send keyserver-ch
        c-id k-id m-root i-root
        r-s r-k t
        b-s b-k
        seq exempt blind k)
    )
    (uniq-orig t)
    (uniq-gen k)
  )
  (defrole database-exempt
    (vars
      (database-ch chan)
      (r-s r-d t authcode random256)
      (c-id d-id m-root i-root b-id name)
      (resp query-response)
      (signed exemptSigned expt)
      (b-s b-d b-bio bundle-data)
    )
    (trace
      (Client2DatabaseExempt recv send database-ch
        c-id d-id m-root i-root b-id
        r-s r-d t
        b-s b-d b-bio
        (exp (gen) signed)
        (exp (gen) exemptSigned)
        resp authcode)
    )
    (uniq-orig t)
    (pen-non-orig authcode)
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
      (r-s r-s2 r-k r-d t2 authcode random256)
      (c-id k-id d-id m-root i-root b-id name)
      (keyserver-ch database-ch chan) 
      (seq blind rndx)
      (z strd))
    (implies
      (and 
        (p "synth-client-exempt" z 13)
        (p "synth-client-exempt" "resp" z resp)
        (p "synth-client-exempt" "r-s" z r-s)
        (p "synth-client-exempt" "r-s2" z r-s2)
        (p "synth-client-exempt" "r-k" z r-k)
        (p "synth-client-exempt" "r-d" z r-d)
        (p "synth-client-exempt" "t2" z t2)
        (p "synth-client-exempt" "authcode" z authcode)
        (p "synth-client-exempt" "c-id" z c-id)
        (p "synth-client-exempt" "k-id" z k-id)
        (p "synth-client-exempt" "d-id" z d-id)
        (p "synth-client-exempt" "b-id" z b-id)
        (p "synth-client-exempt" "m-root" z m-root)
        (p "synth-client-exempt" "i-root" z i-root)
        (p "synth-client-exempt" "keyserver-ch" z keyserver-ch)
        (p "synth-client-exempt" "database-ch" z database-ch)
        (p "synth-client-exempt" "seq" z seq)
        (p "synth-client-exempt" "blind" z blind)
        (non (privk c-id))
        (non (privk k-id))
        (non (privk d-id))
        (non (privk b-id))
        (non (privk m-root))
        (non (privk i-root))
        (pnon authcode)
        (ugen seq)
        (ugen blind)
        (uniq-at r-s z 0)
        (uniq-at r-s2 z 7)
        (auth keyserver-ch)
        (auth database-ch)
        (conf keyserver-ch)
        (conf database-ch)
        (fact neq seq blind))
      (exists (
          (z-1 strd))
        (and
          (p "database-exempt" z-1 6)
          (p "database-exempt" "r-s" z-1 r-s2)
          (p "database-exempt" "r-d" z-1 r-d)
          (p "database-exempt" "t" z-1 t2)
          (p "database-exempt" "authcode" z-1 authcode)
          (p "database-exempt" "c-id" z-1 c-id)
          (p "database-exempt" "d-id" z-1 d-id)
          (p "database-exempt" "m-root" z-1 m-root)
          (p "database-exempt" "i-root" z-1 i-root)
          (p "database-exempt" "database-ch" z-1 database-ch)
          (p "database-exempt" "resp" z-1 resp))))))

;; Query response agreement goal (Database perspective)
(defgoal secure-dna-query
  (forall (
      (resp query-response)
      (r-s r-d t authcode random256)
      (c-id d-id b-id m-root i-root name)
      (database-ch chan) 
      (z strd))
    (implies
      (and 
        (p "database-exempt" z 6)
        (p "database-exempt" "r-s" z r-s)
        (p "database-exempt" "r-d" z r-d)
        (p "database-exempt" "t" z t)
        (p "database-exempt" "authcode" z authcode)
        (p "database-exempt" "c-id" z c-id)
        (p "database-exempt" "d-id" z d-id)
        (p "database-exempt" "b-id" z b-id)
        (p "database-exempt" "m-root" z m-root)
        (p "database-exempt" "i-root" z i-root)
        (p "database-exempt" "database-ch" z database-ch)
        (p "database-exempt" "resp" z resp)
        (non (privk c-id))
        (non (privk d-id))
        (non (privk b-id))
        (non (privk m-root))
        (non (privk i-root))
        (pnon authcode)
        (uniq-at t z 1)
        (uniq-at r-d z 1))
      (exists (
          (z-1 strd))
        (and
          (p "synth-client-exempt" z-1 13)
          (p "synth-client-exempt" "resp" z-1 resp)
          (p "synth-client-exempt" "r-s2" z-1 r-s)
          (p "synth-client-exempt" "r-d" z-1 r-d)
          (p "synth-client-exempt" "t2" z-1 t)
          (p "synth-client-exempt" "authcode" z-1 authcode)
          (p "synth-client-exempt" "c-id" z-1 c-id)
          (p "synth-client-exempt" "d-id" z-1 d-id)
          (p "synth-client-exempt" "m-root" z-1 m-root)
          (p "synth-client-exempt" "i-root" z-1 i-root)
          (p "synth-client-exempt" "database-ch" z-1 database-ch))))))