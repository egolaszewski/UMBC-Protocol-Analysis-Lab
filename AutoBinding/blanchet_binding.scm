(herald "Blanchet's Simple Example Protocol"
  (comment "There is a flaw in this protocol by design"))

(defmacro (InitCtx name version init resp)
  (hash name version init resp))

(defmacro (SignCtx ctx name)
  (enc ctx (privk name)))

(defmacro (AppendCtx signedctx r type vars)
  (hash signedctx r type vars))

(defprotocol blanchet-bound basic
  (defrole init
    (vars (a b name) (s skey) (d text) (r1 r2 data))
    (trace
     (send (cat
      (enc (enc s (privk a)) (pubk b))
      (SignCtx (AppendCtx (SignCtx (InitCtx "bsp" "flawed" a b) a) r1 "bsp-1" s) a)
     ))
     (recv (cat
      (enc d s)
      (SignCtx (AppendCtx (SignCtx (AppendCtx (SignCtx (InitCtx "bsp" "flawed" a b) a) r1 "bsp-1" s) a) r2 "bsp-2" d) b)
     ))
     (send
      (SignCtx (SignCtx (AppendCtx (SignCtx (AppendCtx (SignCtx (InitCtx "bsp" "flawed" a b) a) r1 "bsp-1" s) a) r2 "bsp-2" d) b) a)
     )
    ))
  (defrole resp
    (vars (a b name) (s skey) (d text) (r1 r2 data))
    (trace
     (recv (cat
      (enc (enc s (privk a)) (pubk b))
      (SignCtx (AppendCtx (SignCtx (InitCtx "bsp" "flawed" a b) a) r1 "bsp-1" s) a)
     ))
     (send (cat
      (enc d s)
      (SignCtx (AppendCtx (SignCtx (AppendCtx (SignCtx (InitCtx "bsp" "flawed" a b) a) r1 "bsp-1" s) a) r2 "bsp-2" d) b)
     ))
     (recv
      (SignCtx (SignCtx (AppendCtx (SignCtx (AppendCtx (SignCtx (InitCtx "bsp" "flawed" a b) a) r1 "bsp-1" s) a) r2 "bsp-2" d) b) a)
     )
    ))
  (comment "Blanchet's protocol"))

;;; Bound initiator context goal.
(defgoal blanchet-bound
  (forall ((a b name) (s skey) (d text) (r1 r2 data) (z strd))
    (implies
      (and
        (p "init" z 3)
        (p "init" "a" z a)
        (p "init" "b" z b)
        (p "init" "s" z s)
        (p "init" "d" z d)
        (p "init" "r1" z r1)
        (p "init" "r2" z r2)
        (non (privk a))
        (non (privk b))
        (ugen s)
        (ugen r1)
      )
    (exists ((z-0 strd))
      (and 
        (p "resp" z-0 2)
        (p "resp" "a" z-0 a)
        (p "resp" "b" z-0 b)
        (p "resp" "s" z-0 s)
        (p "resp" "d" z-0 d)
        (p "resp" "r1" z-0 r1)
        (p "resp" "r2" z-0 r2)
      )))))
      
;;; Bound responder context goal.
(defgoal blanchet-bound
  (forall ((a b name) (s skey) (d text) (r1 r2 data) (z strd))
    (implies
      (and
        (p "resp" z 3)
        (p "resp" "a" z a)
        (p "resp" "b" z b)
        (p "resp" "s" z s)
        (p "resp" "d" z d)
        (p "resp" "r1" z r1)
        (p "resp" "r2" z r2)
        (non (privk a))
        (non (privk b))
        (ugen d)
        (ugen r2)
      )
    (exists ((z-0 strd))
      (and 
        (p "init" z-0 3)
        (p "init" "a" z-0 a)
        (p "init" "b" z-0 b)
        (p "init" "s" z-0 s)
        (p "init" "d" z-0 d)
        (p "init" "r1" z-0 r1)
        (p "init" "r2" z-0 r2)
      )))))