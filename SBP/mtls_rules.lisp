;; This macrofile contains rules to control the CPSA analysis.

;; The following macro defines a set of rules that constrain CPSA from
;; considering the case where clients could also server as servers. This is
;; necessary to prevent CPSA from using one client's certificate as a server's
;; certificate for another client. Such an analysis is endless as CPSA continues
;; to add clients that cannot be completed, but can receive a certificate from
;; another client in place of the server's certificate.

(defmacro (clients-distinct-from-servers-rules)
    (^
       (defrule clients-servers-distinct1
	 (forall
	  ((z z-0 strd) (c name))
	  (implies
	   (and
	    (p "clienta" "c" z c)
	    (p "clienta" "s" z-0 c))
	   (false))))

       (defrule clients-servers-distinct2
	 (forall
	  ((z z-0 strd) (c name))
	  (implies
	   (and
	    (p "clienta" "c" z c)
	    (p "clientr" "s" z-0 c))
	   (false))))

       (defrule clients-servers-distinct3
	 (forall
	  ((z z-0 strd) (c name))
	  (implies
	   (and
	    (p "clientr" "c" z c)
	    (p "clientr" "s" z-0 c))
	   (false))))

       (defrule clients-servers-distinct4
	 (forall
	  ((z z-0 strd) (c name))
	  (implies
	   (and
	    (p "clientr" "c" z c)
	    (p "clienta" "s" z-0 c))
	   (false))))))

