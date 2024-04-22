(herald "Needham-Schroeder Public-Key Protocol"
	(comment "Bound.")
  (bound 12)
	(limit 4000)
  ;; (try-old-strands)
  (check-nonces))

(defmacro (InitCtx name version init resp)
  (hash name version init resp))

(defmacro (SignCtx ctx name)
  (enc ctx (privk name)))

(defmacro (AppendCtx signedctx r type vars)
  (hash signedctx r type vars))

(defprotocol ns-bound basic
  (defrole init
    (vars (a b name) (n1 n2 text) (r1 r2 r3 data))
    (trace
      (send (cat
        (enc n1 a (pubk b))
        (SignCtx (AppendCtx (SignCtx (InitCtx "ns-pk" "flawed" a b) a) r1 "ns-1" (cat n1 a)) a)
      ))
      (recv (cat
        (enc n1 n2 (pubk a))
        (SignCtx (AppendCtx (SignCtx (AppendCtx (SignCtx (InitCtx "ns-pk" "flawed" a b) a) r1 "ns-1" (cat n1 a)) a) r2 "ns-2" (cat n2)) b)
      ))
      (send (cat
        (enc n2 (pubk b))
        (SignCtx (AppendCtx (SignCtx (AppendCtx (SignCtx (AppendCtx (SignCtx (InitCtx "ns-pk" "flawed" a b) a) r1 "ns-1" (cat n1 a)) a) r2 "ns-2" n2) b) r3 "ns-3" "empty") a)
      ))
      (recv
        (SignCtx (SignCtx (AppendCtx (SignCtx (AppendCtx (SignCtx (AppendCtx (SignCtx (InitCtx "ns-pk" "flawed" a b) a) r1 "ns-1" (cat n1 a)) a) r2 "ns-2" n2) b) r3 "ns-3" "empty") a) b)
      )
    )
  )
  (defrole resp
    (vars (b a name) (n2 n1 text) (r1 r2 r3 data))
    (trace
      (recv (cat
        (enc n1 a (pubk b))
        (SignCtx (AppendCtx (SignCtx (InitCtx "ns-pk" "flawed" a b) a) r1 "ns-1" (cat n1 a)) a)
      ))
      (send (cat
        (enc n1 n2 (pubk a))
        (SignCtx (AppendCtx (SignCtx (AppendCtx (SignCtx (InitCtx "ns-pk" "flawed" a b) a) r1 "ns-1" (cat n1 a)) a) r2 "ns-2" (cat n2)) b)
      ))
      (recv (cat
        (enc n2 (pubk b))
        (SignCtx (AppendCtx (SignCtx (AppendCtx (SignCtx (AppendCtx (SignCtx (InitCtx "ns-pk" "flawed" a b) a) r1 "ns-1" (cat n1 a)) a) r2 "ns-2" n2) b) r3 "ns-3" "empty") a)
      ))    
      (send
        (SignCtx (SignCtx (AppendCtx (SignCtx (AppendCtx (SignCtx (AppendCtx (SignCtx (InitCtx "ns-pk" "flawed" a b) a) r1 "ns-1" (cat n1 a)) a) r2 "ns-2" n2) b) r3 "ns-3" "empty") a) b)
      )
    )
  )  
  (comment "Needham-Schroeder"))

;;; The initiator point-of-view
(defskeleton ns-bound
  (vars (a b name) (n1 text) (r1 r3 data))
  (defstrandmax init (a a) (b b) (n1 n1) (r1 r1) (r3 r3))
  (non-orig (privk b) (privk a))
  (uniq-orig n1)
  (uniq-gen r1 r3)
  (comment "Initiator point-of-view"))

;;; The responder point-of-view
(defskeleton ns-bound
  (vars (a b name) (n2 text) (r2 data))
  (defstrandmax resp (a a) (b b) (n2 n2) (r2 r2))
  (non-orig (privk a) (privk b))
  (uniq-orig n2)
  (uniq-gen r2)
  (comment "Responder point-of-view"))

;;; Bound initiator context goal.
(defgoal ns-bound
  (forall ((n1 n2 text) (r1 r3 data) (a b name) (z strd))
    (implies
      (and
        (p "init" z 4)
        (p "init" "a" z a)
        (p "init" "b" z b)
        (p "init" "n1" z n1)
        (p "init" "n2" z n2)
        (p "init" "r1" z r1)
        (p "init" "r3" z r3)
        (non (privk a))
        (non (privk b))
        (uniq-at n1 z 0)
        (ugen r1)
        (ugen r3))
    (exists ((z-0 strd))
      (and 
        (p "resp" z-0 4)
        (p "resp" "a" z-0 a)
        (p "resp" "b" z-0 b)
        (p "resp" "n1" z-0 n1)
        (p "resp" "n2" z-0 n2))))))   

;;; Bound responder context goal.
(defgoal ns-bound
  (forall ((n1 n2 text) (r2 data) (a b name) (z strd))
    (implies
      (and
        (p "resp" z 4)
        (p "resp" "a" z a)
        (p "resp" "b" z b)
        (p "resp" "n1" z n1)
        (p "resp" "n2" z n2)
        (p "resp" "r2" z r2)
        (non (privk a))
        (non (privk b))
        (uniq-at n2 z 1)
        (ugen r2))
    (exists ((z-0 strd))
      (and 
        (p "init" z-0 3)
        (p "init" "a" z-0 a)
        (p "init" "b" z-0 b)
        (p "init" "n1" z-0 n1)
        (p "init" "n2" z-0 n2))))))