(herald "Model of C2PA Generation and Verification -- Includes our fix, countersigning of timestamp and a flag to indicate a timestamp should be attached in the claim signature."
	)

;; Definition of a claim signature

(defmacro (claimsignature assertions asset signer)
  (enc (hash assertions (hash asset)) (privk signer)))

;; Definition of a manifest

(defmacro (manifest assertions asset signer)
  (cat (claimsignature assertions asset signer) assertions (hash asset)))

;; Definition of a timestamp

(defmacro (timestamp assertions asset signer time timeauthority)
  (cat (hash (claimsignature assertions asset signer))
       time
       (enc (hash (hash (claimsignature assertions asset signer)) time)
	    (privk timeauthority))))

;; C2PA protocol definition

(defprotocol c2pa basic

  ;; The first two generator roles, generator0 and generator1, and associated
  ;; validator roles, model the C2PA protocol as defined in the specification.  

  (defrole generator0 ;; Generator providing no timestamp with manifest.
    (vars (gen name) (media data) (assertions text))
    (trace
     (send (cat media (manifest assertions media gen)))
     )
    )

  (defrole generator1 ;; Generator providing timestamp from TSA with manifest.
    (vars (gen tsa name) (media data) (assertions time text))
    (trace
     (send (hash (claimsignature assertions media gen)))
     (recv (timestamp assertions media gen time tsa))
     (send (cat media
		(manifest assertions media gen)
		(timestamp assertions media gen time tsa)))
     )
    )

  ;; Generator providing countersigned timestamp (our fix).
  ;; To prevent the timestamp from being removed, it was necessary to include
  ;; with the assertions a flag, "TS" in our model, that a timestamp should
  ;; accompany the manifest. Otherwise the timestamp can be removed and the
  ;; claim signature will still be valid.
  
  (defrole generator2 
    (vars (gen tsa name) (media data) (assertions time text))
    (trace
     (send (hash (claimsignature (cat assertions "TS") media gen)))
     (recv (timestamp (cat assertions "TS") media gen time tsa))
     (send (cat media
		(manifest (cat assertions "TS") media gen)
		(timestamp (cat assertions "TS") media gen time tsa)
		(enc (hash (timestamp (cat assertions "TS") media gen time tsa))
		     (privk gen))))
     )
    )

  ;; Generators that use C2PA Manifests to add timestamps and guarantee that
  ;; the generator signs the timestamp it requested for the asset.
  
  ;; This generator only adds the timestamp as part of the current manifest to
  ;; produce a timestamp that is signed by the generator that requested it.
  ;; This role is used to illustrates that simply using the manifest mechanism
  ;; to add the timestamp is insufficient, as the timestamp manifest can simply
  ;; be removed. This also highlights that it is possible to remove manifests if
  ;; there have been no actual changes to invalidate assertions made in earlier
  ;; manifests.
  
  (defrole generator3 ;; Generator providing timestamp manifest.
    (vars (gen tsa name) (media data) (assertions time text))
    (trace
     (send (hash (claimsignature assertions media gen)))
     (recv (timestamp assertions media gen time tsa))
     (send (cat media
		(manifest assertions media gen) ;; Original Manifest
		(manifest
		 (cat
		  (timestamp assertions media gen time tsa)
		  (manifest assertions media gen))
		 media
		 gen))) ;; Timestamp Manifest w/ reference to original
     )
    )

  ;; Generator providing timestamp manifest

  ;; This generator includes a flag in the parent manifest (our fix) to
  ;; indicate that a manifest including a timestamp should be provided. This is
  ;; necessary to prevent the timestamp from being removed and the remaining
  ;; manifest still being valid.
  
  (defrole generator4 
    (vars (gen tsa name) (media data) (assertions time text))
    (trace
     (send (hash (claimsignature (cat assertions "TS") media gen)))
     (recv (timestamp (cat assertions "TS") media gen time tsa))
     (send (cat media
		(manifest (cat assertions "TS") media gen) ;; Original Manifest
		(manifest
		 (cat
		  (timestamp (cat assertions "TS") media gen time tsa)
		  (manifest (cat assertions "TS") media gen))
		 media
		 gen))) ;; Timestamp Manifest w/ reference to original
     )
    )
  
  (defrole TSA ;; Trusted Timestamp Authority
    (vars (msg mesg) (time text) (tsa name))
    (trace
     (recv msg)
     (send (cat msg time (enc (hash msg time) (privk tsa))))
     )
    (uniq-orig time)
    )

  (defrole validator0 ;; validator receiving manifest with no timestamp
    (vars (gen name) (media data) (assertions text))
    (trace
     (recv (cat media (manifest assertions media gen)))
     )
    )  

  (defrole validator1 ;; validator receiving manifest with timestamp (ts)
    (vars (gen tsa name) (media data) (assertions time text))
    (trace
     (recv (cat media
		(manifest assertions media gen)
		(timestamp assertions media gen time tsa)))
     )
    )
 
  (defrole validator2 ;; validator receiving manifest with countersigned ts
                      ;; (our fix)
    (vars (gen tsa name) (media data) (assertions time text))
    (trace
     (recv (cat media
		(manifest (cat assertions "TS") media gen)
		(timestamp (cat assertions "TS") media gen time tsa)
		(enc (hash (timestamp (cat assertions "TS") media gen time tsa))
		     (privk gen))))
     )
    )

  (defrole validator3 ;; validator receiving timestamp as new manifest
    (vars (gen tsa name) (media data) (assertions time text))
    (trace
     (recv (cat media
		(manifest assertions media gen) ;; Original Manifest
		(manifest
		 (cat
		  (timestamp assertions media gen time tsa)
		  (manifest assertions media gen))
		 media
		 gen))) ;; Timestamp Manifest w/ reference to original
     )
    )
 
  (defrole validator4 ;; validator receiving timestamp as new manifest (our fix)
    (vars (gen tsa name) (media data) (assertions time text))
    (trace
     (recv (cat media
		(manifest (cat assertions "TS") media gen) ;; Original Manifest
		(manifest
		 (cat
		  (timestamp (cat assertions "TS") media gen time tsa)
		  (manifest (cat assertions "TS") media gen))
		 media
		 gen))) ;; Timestamp Manifest w/ reference to original
     )
    )
  )
 
;; Analysis of Security Goal 1, 2, and 5 (Theorem 1) from each validator's
;; perspective. As SG2 is true if SG5 is true, given that SG2 is a weaker
;; version of SG4, we have simplified the analysis of SG2 and SG5 by not
;; modeling the asset as different components, some of which may not be
;; covered by the signature. As CPSA does not support branching, we must
;; specify the theorem for each validator role. It is true for all shapes
;; produced by each validator role.

;; Validator that does not receive a timestamp
(defgoal c2pa
  (forall ((media data) (assertions text) (gen name) (z strd))
    (implies
      (and (p "validator0" z 1) (p "validator0" "media" z media)
        (p "validator0" "assertions" z assertions)
        (p "validator0" "gen" z gen) (non (privk gen)))
      (or
       (exists ((z-0 strd))
               (and (p "generator0" z-0 1) (p "generator0" "media" z-0 media)
		    (p "generator0" "assertions" z-0 assertions)
		    (p "generator0" "gen" z-0 gen) (prec z-0 0 z 0)))
       (exists ((z-0 strd))
               (and (p "generator1" z-0 1) (p "generator1" "media" z-0 media)
		    (p "generator1" "assertions" z-0 assertions)
		    (p "generator1" "gen" z-0 gen) (prec z-0 0 z 0)))
       (exists ((z-0 strd))
	       (and (p "generator2" z-0 3) (p "generator2" "media" z-0 media)
		    (p "generator2" "assertions" z-0 assertions)
		    (p "generator2" "gen" z-0 gen) (prec z-0 2 z 0)))
       (exists ((z-0 strd))
	       (and (p "generator3" z-0 3) (p "generator3" "media" z-0 media)
		    (p "generator3" "assertions" z-0 assertions)
		    (p "generator3" "gen" z-0 gen) (prec z-0 2 z 0)))
       (exists ((z-0 strd))
	       (and (p "generator4" z-0 3) (p "generator4" "media" z-0 media)
		    (p "generator4" "assertions" z-0 assertions)
		    (p "generator4" "gen" z-0 gen) (prec z-0 2 z 0))))))
  (comment "Analysis of Security Goal 1 (SG1)"))

;; Validator receiving TSA Timestamp as specified in C2PA
(defgoal c2pa
  (forall ((media data) (assertions text) (gen tsa name) (z strd))
    (implies
      (and (p "validator1" z 1) (p "validator1" "media" z media)
        (p "validator1" "assertions" z assertions)
        (p "validator1" "gen" z gen) (p "validator1" "tsa" z tsa)
	(non (privk gen)) (non (privk tsa)))
      (or
       (exists ((z-0 strd))
               (and (p "generator0" z-0 1) (p "generator0" "media" z-0 media)
		    (p "generator0" "assertions" z-0 assertions)
		    (p "generator0" "gen" z-0 gen) (prec z-0 0 z 0)))
       (exists ((z-0 strd))
	       (and (p "generator1" z-0 3) (p "generator1" "media" z-0 media)
		    (p "generator1" "assertions" z-0 assertions)
		    (p "generator1" "gen" z-0 gen) (prec z-0 2 z 0)))
       (exists ((z-0 strd))
	       (and (p "generator2" z-0 3) (p "generator2" "media" z-0 media)
		    (p "generator2" "assertions" z-0 assertions)
		    (p "generator2" "gen" z-0 gen) (prec z-0 2 z 0)))
       (exists ((z-0 strd))
	       (and (p "generator3" z-0 3) (p "generator3" "media" z-0 media)
		    (p "generator3" "assertions" z-0 assertions)
		    (p "generator3" "gen" z-0 gen) (prec z-0 2 z 0)))
       (exists ((z-0 strd))
	       (and (p "generator4" z-0 3) (p "generator4" "media" z-0 media)
		    (p "generator4" "assertions" z-0 assertions)
		    (p "generator4" "gen" z-0 gen) (prec z-0 2 z 0))))))
  (comment "Analysis of Security Goal 1 (SG1)"))

;; Validator receiving TSA Timestamp Countersigned by Generator (our fix)
(defgoal c2pa
  (forall ((media data) (assertions text) (gen tsa name) (z strd))
    (implies
      (and (p "validator2" z 1) (p "validator2" "media" z media)
        (p "validator2" "assertions" z assertions)
        (p "validator2" "gen" z gen)  (p "validator2" "tsa" z tsa)
	(non (privk gen)) (non (privk tsa)))
      (or
       (exists ((z-0 strd))
               (and (p "generator0" z-0 1) (p "generator0" "media" z-0 media)
		    (p "generator0" "assertions" z-0 assertions)
		    (p "generator0" "gen" z-0 gen) (prec z-0 0 z 0)))
       (exists ((z-0 strd))
	       (and (p "generator1" z-0 3) (p "generator1" "media" z-0 media)
		    (p "generator1" "assertions" z-0 assertions)
		    (p "generator1" "gen" z-0 gen) (prec z-0 2 z 0)))
       (exists ((z-0 strd))
	       (and (p "generator2" z-0 3) (p "generator2" "media" z-0 media)
		    (p "generator2" "assertions" z-0 assertions)
		    (p "generator2" "gen" z-0 gen) (prec z-0 2 z 0)))
       (exists ((z-0 strd))
	       (and (p "generator3" z-0 3) (p "generator3" "media" z-0 media)
		    (p "generator3" "assertions" z-0 assertions)
		    (p "generator3" "gen" z-0 gen) (prec z-0 2 z 0)))
       (exists ((z-0 strd))
	       (and (p "generator4" z-0 3) (p "generator4" "media" z-0 media)
		    (p "generator4" "assertions" z-0 assertions)
		    (p "generator4" "gen" z-0 gen) (prec z-0 2 z 0))))))
  (comment "Analysis of Security Goal 1 (SG1)"))

;; Validator receiving TSA Timestamp in current manifest
(defgoal c2pa
  (forall ((media data) (assertions text) (gen tsa name) (z strd))
    (implies
      (and (p "validator3" z 1) (p "validator3" "media" z media)
        (p "validator3" "assertions" z assertions)
        (p "validator3" "gen" z gen)  (p "validator3" "tsa" z tsa)
	(non (privk gen)) (non (privk tsa)))
      (or
       (exists ((z-0 strd))
               (and (p "generator0" z-0 1) (p "generator0" "media" z-0 media)
		    (p "generator0" "assertions" z-0 assertions)
		    (p "generator0" "gen" z-0 gen) (prec z-0 0 z 0)))
       (exists ((z-0 strd))
	       (and (p "generator1" z-0 3) (p "generator1" "media" z-0 media)
		    (p "generator1" "assertions" z-0 assertions)
		    (p "generator1" "gen" z-0 gen) (prec z-0 2 z 0)))
       (exists ((z-0 strd))
	       (and (p "generator2" z-0 3) (p "generator2" "media" z-0 media)
		    (p "generator2" "assertions" z-0 assertions)
		    (p "generator2" "gen" z-0 gen) (prec z-0 2 z 0)))
       (exists ((z-0 strd))
	       (and (p "generator3" z-0 3) (p "generator3" "media" z-0 media)
		    (p "generator3" "assertions" z-0 assertions)
		    (p "generator3" "gen" z-0 gen) (prec z-0 2 z 0)))
       (exists ((z-0 strd))
	       (and (p "generator4" z-0 3) (p "generator4" "media" z-0 media)
		    (p "generator4" "assertions" z-0 assertions)
		    (p "generator4" "gen" z-0 gen) (prec z-0 2 z 0))))))
  (comment "Analysis of Security Goal 1 (SG1)"))

;; Validator receiving TSA Timestamp in current manifest with TS flag in the
;; original manifest to indicate a manifest should include a timestamp (our fix)
(defgoal c2pa
  (forall ((media data) (assertions text) (gen tsa name) (z strd))
    (implies
      (and (p "validator4" z 1) (p "validator4" "media" z media)
        (p "validator4" "assertions" z assertions)
        (p "validator4" "gen" z gen)  (p "validator4" "tsa" z tsa)
	(non (privk gen)) (non (privk tsa)))
      (or
       (exists ((z-0 strd))
               (and (p "generator0" z-0 1) (p "generator0" "media" z-0 media)
		    (p "generator0" "assertions" z-0 assertions)
		    (p "generator0" "gen" z-0 gen) (prec z-0 0 z 0)))
       (exists ((z-0 strd))
	       (and (p "generator1" z-0 3) (p "generator1" "media" z-0 media)
		    (p "generator1" "assertions" z-0 assertions)
		    (p "generator1" "gen" z-0 gen) (prec z-0 2 z 0)))
       (exists ((z-0 strd))
	       (and (p "generator2" z-0 3) (p "generator2" "media" z-0 media)
		    (p "generator2" "assertions" z-0 assertions)
		    (p "generator2" "gen" z-0 gen) (prec z-0 2 z 0)))
       (exists ((z-0 strd))
	       (and (p "generator3" z-0 3) (p "generator3" "media" z-0 media)
		    (p "generator3" "assertions" z-0 assertions)
		    (p "generator3" "gen" z-0 gen) (prec z-0 2 z 0)))
       (exists ((z-0 strd))
	       (and (p "generator4" z-0 3) (p "generator4" "media" z-0 media)
		    (p "generator4" "assertions" z-0 assertions)
		    (p "generator4" "gen" z-0 gen) (prec z-0 2 z 0))))))
  (comment "Analysis of Security Goal 1 (SG1)"))


;; Analysis of Proposition 1 from the perspective of validator's that receive
;; timestamps. This Proposition must be validated for each validator that
;; receives a timestamp.

;; Validator receiving TSA timestamp as specified in C2PA
(defgoal c2pa
  (forall ((media data) (assertions time text) (gen tsa name) (z strd))
    (implies
      (and (p "validator1" z 1) (p "validator1" "media" z media)
        (p "validator1" "assertions" z assertions)
        (p "validator1" "time" z time) (p "validator1" "gen" z gen)
        (p "validator1" "tsa" z tsa) (non (privk gen)) (non (privk tsa)))
      (exists ((z-0 z-1 strd))
              (and (p "generator1" z-0 3) (p "TSA" z-1 2)
		   (p "generator1" "media" z-0 media)
		   (p "generator1" "assertions" z-0 assertions)
		   (p "generator1" "time" z-0 time)
		   (p "generator1" "gen" z-0 gen) (p "generator1" "tsa" z-0 tsa)
		   (p "TSA" "time" z-1 time) (p "TSA" "tsa" z-1 tsa)
		   (prec z-0 2 z 0) (prec z-1 1 z-0 1)
		   (uniq-at time z-1 1)))))
    (comment "Analysis of Proposition 1"))

;; Validator receiving TSA Timestamp Countersigned by Generator (our fix)
(defgoal c2pa
  (forall ((media data) (assertions time text) (gen tsa name) (z strd))
    (implies
      (and (p "validator2" z 1) (p "validator2" "media" z media)
        (p "validator2" "assertions" z assertions)
        (p "validator2" "time" z time) (p "validator2" "gen" z gen)
        (p "validator2" "tsa" z tsa) (non (privk gen)) (non (privk tsa)))
      (exists ((z-0 z-1 strd))
              (and (p "generator2" z-0 3) (p "TSA" z-1 2)
		   (p "generator2" "media" z-0 media)
		   (p "generator2" "assertions" z-0 assertions)
		   (p "generator2" "time" z-0 time)
		   (p "generator2" "gen" z-0 gen) (p "generator2" "tsa" z-0 tsa)
		   (p "TSA" "time" z-1 time) (p "TSA" "tsa" z-1 tsa)
		   (prec z-0 2 z 0) (prec z-1 1 z-0 1)
		   (uniq-at time z-1 1)))))
    (comment "Analysis of Proposition 1"))

;; Validator receiving TSA Timestamp in current manifest
(defgoal c2pa
  (forall ((media data) (assertions time text) (gen tsa name) (z strd))
    (implies
      (and (p "validator3" z 1) (p "validator3" "media" z media)
        (p "validator3" "assertions" z assertions)
        (p "validator3" "time" z time) (p "validator3" "gen" z gen)
        (p "validator3" "tsa" z tsa) (non (privk gen)) (non (privk tsa)))
      (exists ((z-0 z-1 strd))
              (and (p "generator3" z-0 3) (p "TSA" z-1 2)
		   (p "generator3" "media" z-0 media)
		   (p "generator3" "assertions" z-0 assertions)
		   (p "generator3" "time" z-0 time)
		   (p "generator3" "gen" z-0 gen) (p "generator3" "tsa" z-0 tsa)
		   (p "TSA" "time" z-1 time) (p "TSA" "tsa" z-1 tsa)
		   (prec z-0 2 z 0) (prec z-1 1 z-0 1)
		   (uniq-at time z-1 1)))))
    (comment "Analysis of Proposition 1"))

;; Validator receiving TSA Timestamp in current manifest with timestamp flag in
;; the parent manifest (our fix)
(defgoal c2pa
  (forall ((media data) (assertions time text) (gen tsa name) (z strd))
    (implies
      (and (p "validator4" z 1) (p "validator4" "media" z media)
        (p "validator4" "assertions" z assertions)
        (p "validator4" "time" z time) (p "validator4" "gen" z gen)
        (p "validator4" "tsa" z tsa) (non (privk gen)) (non (privk tsa)))
      (exists ((z-0 z-1 strd))
              (and (p "generator4" z-0 3) (p "TSA" z-1 2)
		   (p "generator4" "media" z-0 media)
		   (p "generator4" "assertions" z-0 assertions)
		   (p "generator4" "time" z-0 time)
		   (p "generator4" "gen" z-0 gen) (p "generator4" "tsa" z-0 tsa)
		   (p "TSA" "time" z-1 time) (p "TSA" "tsa" z-1 tsa)
		   (prec z-0 2 z 0) (prec z-1 1 z-0 1)
		   (uniq-at time z-1 1)))))
    (comment "Analysis of Proposition 1"))

;; Analysis of Propostion 2. This analysis requires an alteration of the
;; original model of the C2PA protocol to remove strands with generator traces
;; that do not produce a timestamp, those strands created by the generator0
;; role. The simple modification is to comment out the generator0 role. As the
;; proposition states, there should not exist any shapes that satisfy validator0
;; from generator strands that provide a timestamps. generator0 strands do not
;; provide a timestamp.

;; The modified C2PA protocol definition to remove generator0 strands

(defprotocol c2pa_reduced basic

  ;; The first two generator roles, generator0 and generator1, and associated
  ;; validator roles, model the C2PA protocol as defined in the specification

  ;; commenting out role generator0. It is the only role that creates manifests
  ;; without a timestamp in the C2PA protocol

  ;; (defrole generator0 ;; generator providing no timestamp with manifest
  ;;   (vars (gen name) (media data) (assertions text))
  ;;   (trace
  ;;    (send (cat media (manifest assertions media gen)))
  ;;    )
  ;;   )

  (defrole generator1 ;; generator providing timestamp from TSA with manifest
    (vars (gen tsa name) (media data) (assertions time text))
    (trace
     (send (hash (claimsignature assertions media gen)))
     (recv (timestamp assertions media gen time tsa))
     (send (cat media
		(manifest assertions media gen)
		(timestamp assertions media gen time tsa)))
     )
    )

  ;;
  ;; Generator providing countersigned timestamp (our fix)
  ;; To prevent the timestamp from being removed, it was necessary to include
  ;; with the assertions a flag, "TS" in our model, that a timestamp should
  ;; accompany the manifest. Otherwise the timestamp can be removed and the
  ;; claim signature will still be valid.
  
  (defrole generator2 
    (vars (gen tsa name) (media data) (assertions time text))
    (trace
     (send (hash (claimsignature (cat assertions "TS") media gen)))
     (recv (timestamp (cat assertions "TS") media gen time tsa))
     (send (cat media
		(manifest (cat assertions "TS") media gen)
		(timestamp (cat assertions "TS") media gen time tsa)
		(enc (hash (timestamp (cat assertions "TS") media gen time tsa))
		     (privk gen))))
     )
    )

  ;; Generators that use C2PA Manifests to add timestamps and guarantee that
  ;; the generator signs the timestamp it requested for the asset.
  
  ;; This generator only adds the timestamp as part of the current manifest to
  ;; produce a timestamp that is signed by the generator that requested it.
  ;; This role is used to illustrates that simply using the manifest mechanism
  ;; to add the timestamp is insufficient, as the timestamp manifest can simply
  ;; be removed. This also highlights that it is possible to remove manifests if
  ;; there have been no actual changes to invalidate assertions made in earlier
  ;; manifests.
  
  (defrole generator3 ;; generator providing timestamp manifest
    (vars (gen tsa name) (media data) (assertions time text))
    (trace
     (send (hash (claimsignature assertions media gen)))
     (recv (timestamp assertions media gen time tsa))
     (send (cat media
		(manifest assertions media gen) ;; Original Manifest
		(manifest
		 (cat
		  (timestamp assertions media gen time tsa)
		  (manifest assertions media gen))
		 media
		 gen))) ;; Timestamp Manifest w/ reference to original
     )
    )

  ;; Generator providing timestamp manifest

  ;; This generator includes a flag in the parent manifest (our fix) to
  ;; indicate that a manifest including a timestamp should be provided. This is
  ;; necessary to prevent the timestamp from being removed and the remaining
  ;; manifest still being valid.
  
  (defrole generator4 
    (vars (gen tsa name) (media data) (assertions time text))
    (trace
     (send (hash (claimsignature (cat assertions "TS") media gen)))
     (recv (timestamp (cat assertions "TS") media gen time tsa))
     (send (cat media
		(manifest (cat assertions "TS") media gen) ;; Original Manifest
		(manifest
		 (cat
		  (timestamp (cat assertions "TS") media gen time tsa)
		  (manifest (cat assertions "TS") media gen))
		 media
		 gen))) ;; Timestamp Manifest w/ reference to original
     )
    )
  
  (defrole TSA ;; Trusted Timestamp Authority
    (vars (msg mesg) (time text) (tsa name))
    (trace
     (recv msg)
     (send (cat msg time (enc (hash msg time) (privk tsa))))
     )
    (uniq-orig time)
    )

  (defrole validator0 ;; validator receiving manifest with no timestamp
    (vars (gen name) (media data) (assertions text))
    (trace
     (recv (cat media (manifest assertions media gen)))
     )
    )  

  (defrole validator1 ;; validator receiving manifest with timestamp (ts)
    (vars (gen tsa name) (media data) (assertions time text))
    (trace
     (recv (cat media
		(manifest assertions media gen)
		(timestamp assertions media gen time tsa)))
     )
    )
 
  (defrole validator2 ;; validator receiving manifest with countersigned ts
    (vars (gen tsa name) (media data) (assertions time text))
    (trace
     (recv (cat media
		(manifest (cat assertions "TS") media gen)
		(timestamp (cat assertions "TS") media gen time tsa)
		(enc (hash (timestamp (cat assertions "TS") media gen time tsa))
		     (privk gen))))
     )
    )

  (defrole validator3 ;; validator receiving timestamp as new manifest
    (vars (gen tsa name) (media data) (assertions time text))
    (trace
     (recv (cat media
		(manifest assertions media gen) ;; Original Manifest
		(manifest
		 (cat
		  (timestamp assertions media gen time tsa)
		  (manifest assertions media gen))
		 media
		 gen))) ;; Timestamp Manifest w/ reference to original
     )
    )
 
  (defrole validator4 ;; validator receiving timestamp as new manifest (fixed)
    (vars (gen tsa name) (media data) (assertions time text))
    (trace
     (recv (cat media
		(manifest (cat assertions "TS") media gen) ;; Original Manifest
		(manifest
		 (cat
		  (timestamp (cat assertions "TS") media gen time tsa)
		  (manifest (cat assertions "TS") media gen))
		 media
		 gen))) ;; Timestamp Manifest w/ reference to original
     )
    )
  )

;; Analysis of Proposition 2. Any shapes that exist with generator strands
;; indicate that the timestamp can be removed in an undetectable manner,
;; invalidating the proposition for the generator strands that produce the
;; shape.

(defgoal c2pa_reduced
  (forall ((media data) (assertions text) (gen name) (z strd))
    (implies
      (and (p "validator0" z 1) (p "validator0" "media" z media)
	(p "validator0" "assertions" z assertions)
	(p "validator0" "gen" z gen)
	(non (privk gen)))
      (false)))
    (comment "Analysis of Proposition 2"))
