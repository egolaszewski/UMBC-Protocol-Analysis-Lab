(herald
 "SRP protocol with leak of verifier"
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
     (send v)) ; Leak of the verifier to the intruder
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
    (neq (u b)) ; Required to prevent CPSA from exploring cases where b is leaked
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

  (comment "This version of the SRP protocol includes the leak of the verifier to the adversary.") 
  (comment "The leak occurs as an added message in the server-init role in which v is sent. The") 
  (comment "only other change is that a statement that b is not equal to u must be added to the")
  (comment "server role to prevent CPSA from exploring states where b is leaked by being equal to u.")
  (comment "This version is used to prove that leaking the verifier to the adversary does not result")
  (comment "in compromise of the authentication. The adversary would still be required to execute a")
  (comment "dictionary attack to obtain the value x."))

(defskeleton srp
  (vars (client server name))
  (defstrand client 7 (server server) (client client))
  (non-orig (ltk client server)))

(defskeleton srp
  (vars (client server name))
  (defstrand server 6 (server server) (client client))
  (non-orig (ltk client server)))



   
