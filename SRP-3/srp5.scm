(herald
 "SRP protocol without u, but leaking the verifier"
 (algebra diffie-hellman)
 (bound 40)
 (limit 8000)
 )

(defprotocol srp diffie-hellman
  (defrole client-init
    (vars (s text) (x rndx) (client server name)) 
    (trace
     (init (cat "Client state" s x client server))
     (send (enc "Enroll" s (exp (gen) x) client (ltk client server))))
    (uniq-gen s x))

  (defrole server-init
    (vars (s text) (v mesg) (client server name))
    (trace
     (recv (enc "Enroll" s v client (ltk client server)))
     (init (cat "Server record" s v client server))
     (send v)))

  (defrole client
    (vars (client server name) (a rndx) (b x expt) (s text))     
    (trace
     (send client)
     (recv s)
     (obsv (cat "Client state" s x client server))
     (send (exp (gen) a))
     (recv (enc (exp (gen) b) (exp (gen) x)))
     (send (hash (exp (gen) a)
		 (enc (exp (gen) b) (exp (gen) x))
		 (hash (exp (gen) (mul b a)) (exp (gen) (mul b x)))))
     (recv (hash (exp (gen) a)
		 (hash (exp (gen) a)
		       (enc (exp (gen) b) (exp (gen) x)) 
		       (hash (exp (gen) (mul b a)) (exp (gen) (mul b x))))
		 (hash (exp (gen) (mul b a)) (exp (gen) (mul b x))))))
    (uniq-gen a))

  (defrole server
    (vars (client server name) (a expt) (b rndx) (s text) (v base))
    (trace
     (recv client)
     (obsv (cat "Server record" s v client server))
     (send s)
     (recv (exp (gen) a))
     (send (enc (exp (gen) b) v))
     (recv (hash (exp (gen) a)
		 (enc (exp (gen) b) v)
		 (hash (exp (gen) (mul a b)) (exp v (mul b)))))
     (send (hash (exp (gen) a)
		 (hash (exp (gen) a)
		       (enc (exp (gen) b) v)
		       (hash (exp (gen) (mul a b)) (exp v (mul b))))
		 (hash (exp (gen) (mul a b)) (exp v (mul b))))))
    (uniq-gen b))

  (defrule at-most-one-server-init-per-client
    (forall ((z0 z1 strd) (client server name))
            (implies
	     (and (p "server-init" z0 1)
		  (p "server-init" z1 1)
		  (p "server-init" "client" z0 client)
		  (p "server-init" "client" z1 client)
		  (p "server-init" "server" z0 server)
		  (p "server-init" "server" z1 server))
	     (= z0 z1))))
  
  (comment "This version of the SRP protocol without u is intended to verify that leaking the verifier")
  (comment "does not lead to any attacks on the SRP protocol when the value u is not present in the")
  (comment "protocol. CPSA analysis of this protocol is to further prove that u is not needed."))

(defskeleton srp
  (vars (client server name))
  (defstrand client 7 (server server) (client client))
  (non-orig (ltk client server)))

(defskeleton srp
  (vars (client server name))
  (defstrand server 6 (server server) (client client))
  (non-orig (ltk client server)))

   
