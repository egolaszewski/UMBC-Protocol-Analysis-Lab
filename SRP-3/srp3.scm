(herald
 "SRP protocol with leak of verifier that also allows leak of b"
 (algebra diffie-hellman)
 (bound 40)
 (limit 8000)
 )

(defprotocol srp diffie-hellman
  (defrole client-init
    (vars (s text) (x rndx) (client server name)) 
    (trace
     (init (cat "Client state" s x client server))
     (send (enc "Enroll" s (exp (gen) x) client (ltk client server)))
     )
    (uniq-gen s x)
    )

  (defrole server-init
    (vars (s text) (v mesg) (client server name))
    (trace
     (recv (enc "Enroll" s v client (ltk client server)))
     (init (cat "Server record" s v client server))
     (send v)) ;Leak of the verifier to the intruder
    )

  (defrole client
    (vars (client server name) (a rndx) (b u x expt) (s text))     
    (trace
     (send client)
     (recv s)
     (obsv (cat "Client state" s x client server))
     (send (exp (gen) a))
     (recv (cat (enc (exp (gen) b) (exp (gen) x)) u))
     (send (hash (exp (gen) a)
		 (enc (exp (gen) b) (exp (gen) x)) u
		 (hash (exp (gen) (mul b a)) (exp (gen) (mul b u x)))))
     (recv (hash (exp (gen) a)
		 (hash (exp (gen) a)
		       (enc (exp (gen) b) (exp (gen) x)) u
		       (hash (exp (gen) (mul b a)) (exp (gen) (mul b u x))))
		 (hash (exp (gen) (mul b a)) (exp (gen) (mul b u x))))))
    (uniq-gen a)
    )

  (defrole server
    (vars (client server name) (a expt) (b u rndx) (s text) (v base))
    (trace
     (recv client)
     (obsv (cat "Server record" s v client server))
     (send s)
     (recv (exp (gen) a))
     (send (cat (enc (exp (gen) b) v) u))
     (recv (hash (exp (gen) a)
		 (enc (exp (gen) b) v) u
		 (hash (exp (gen) (mul a b)) (exp v (mul u b)))))
     (send (hash (exp (gen) a)
		 (hash (exp (gen) a)
		       (enc (exp (gen) b) v) u
		       (hash (exp (gen) (mul a b)) (exp v (mul u b))))
		 (hash (exp (gen) (mul a b)) (exp v (mul u b))))))
    (uniq-gen u b)
    )

  (defrule at-most-one-server-init-per-client
    (forall ((z0 z1 strd) (client server name))
            (implies
	     (and (p "server-init" z0 1)
		  (p "server-init" z1 1)
		  (p "server-init" "client" z0 client)
		  (p "server-init" "client" z1 client)
		  (p "server-init" "server" z0 server)
		  (p "server-init" "server" z1 server)
		  )
	     (= z0 z1))))
  
  (comment "This version of the SRP protocol includes the leak of the verifier to the adversary,")
  (comment "but does not require that b is not equal to u. This allows CPSA to explore the possibility")
  (comment "that the adversary can also acquire the value b. This should only be possible if the")
  (comment "authentication mechanism on the server were compromised and can be checked with listener")
  (comment "strands for b in the actual protocol without the leaks."))

(defskeleton srp
  (vars (client server name))
  (defstrand client 7 (server server) (client client))
  (non-orig (ltk client server)))

(defskeleton srp
  (vars (client server name))
  (defstrand server 6 (server server) (client client))
  (non-orig (ltk client server)))



   
