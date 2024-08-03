(herald "I2C-Secure" )

(defmacro (xor a b) 
    (cat
        (enc a b) 
        (enc b a)
    )
)

;; helper function
(defmacro (GCM-Encrypt iv cntr k)
    (enc iv cntr k) 
)

(defmacro (len a b)
    (cat 
        (hash a b)
        (hash b a)
    )
)
(defmacro (GCM-Init iv cntr_0 k)
    (GCM-Encrypt iv cntr_0 k)
)

(defmacro (GCM-Block-One iv cntr_1 pt k)
    (xor 
        (GCM-Encrypt iv cntr_1 k)
        pt
    )
    ;; returns MulH vector i.e. (direct ciphertext)
)

(defmacro (GCM-Block-N iv cntr_N pt mulH_prev k)
    (xor 
        (GCM-Block-One iv cntr_N pt k)
        mulH_prev
    )   
    ;; returns ciphertext xor'd w/ previous MulH
)

(defmacro (GCM-Block-Tag mulH_prev c_len gcm_init)
    (xor 
        (xor mulH_prev c_len)
        gcm_init
    )   
    ;; returns message integrity code (called tag)
)

(defprotocol I2C-Secure basic
    ; timekeep roles (not apart of i2c)
    ;; (defrole timeset
    ;;     (vars (clock data))
    ;;     (trace
    ;;     (init (cat clock "0")))
    ;;     (uniq-gen clock)
    ;;     (fn-of (clock-id (clock "global clock")))
    ;; )
    ;; (defrole timetick
    ;;     (vars (state mesg) (clock data))
    ;;     (trace
    ;;     (tran (cat clock state) (cat clock (hash "t" state))))
    ;; )

    ;; primary (master device 1)
    (defrole primary
        (vars (secondary_address name) (secondary_register text) (byte_data cntr_0 cntr_1 cntr_2 iv data) (k skey))
        (trace
            (send "START")                                                              ; Primary takes control of the bus                            
            (send (cat secondary_address "WRITE_REQ"))                                  ; Primary sends a write request for a specific secondary
            (recv "ACK")                                                                ; Secondary acks
            (send (GCM-Block-One iv cntr_1 secondary_register k))                       ; Primary sends a specific register it wishes to write to write to on the secondary
            (recv "ACK")                                                                ; Secondary acks
            (send 
                (GCM-Block-N 
                    iv 
                    cntr_2 
                    byte_data 
                    (GCM-Block-One iv cntr_1 secondary_register k)                      ; mulH_prev
                    k
                )
            )                                                                           ; Primary sends data to be written to register 
            (recv "ACK")                                                                ; Secondary acks
            ; Secondary sends "TAG"                             
            (send 
                (GCM-Block-Tag 
                    (GCM-Block-N                                                        ; mulH_prev
                        iv 
                        cntr_2 
                        byte_data 
                        (GCM-Block-One iv cntr_1 secondary_register k)                  ; mulH_prev_prev
                        k
                    ) 
                    (len secondary_register byte_data)                                  ; c_len
                    (GCM-Init iv cntr_0 k) ; gcm_init
                )
            )                                                                     
            (recv "ACK")                                                                ; Secondary acks
            (send "STOP")                                                               ; Primary pulls the SDA SDL high (stop condtion)
        )

        ;; assumptions
        ;; (facts (neq cntr_0 cntr_1))
        ;; (facts (neq cntr_1 cntr_2))
        ;; (facts (neq cntr_0 cntr_2))

        ;; (uniq-gen k iv)
        ;; (non-orig k iv cntr_0 cntr_1 cntr_2)
    )
    ;; secondary (slave device 2)
    (defrole secondary
        (vars (secondary_address name) (secondary_register text) (byte_data cntr_0 cntr_1 cntr_2 iv data) (k skey))
        (trace
            (recv "START")                                                              ; Primary takes control of the bus                            
            (recv (cat secondary_address "WRITE_REQ"))                                  ; Primary sends a write request for a specific secondary
            (send "ACK")                                                                ; Secondary acks
            (recv (GCM-Block-One iv cntr_1 secondary_register k))                       ; Primary sends a specific register it wishes to write to write to on the secondary
            (send "ACK")                                                                ; Secondary acks
            (recv 
                (GCM-Block-N 
                    iv 
                    cntr_2 
                    byte_data 
                    (GCM-Block-One iv cntr_1 secondary_register k)                      ; mulH_prev
                    k
                )
            )                                                                           ; Primary sends data to be written to register 
            (send "ACK")                                                                ; Secondary acks
            ; Secondary sends "TAG"                             
            (recv 
                (GCM-Block-Tag 
                    (GCM-Block-N                                                        ; mulH_prev
                        iv 
                        cntr_2 
                        byte_data 
                        (GCM-Block-One iv cntr_1 secondary_register k)                  ; mulH_prev_prev
                        k
                    ) 
                    (hash byte_data )                                                   ; c_len -- for now we can represent the length of the data as a cat of the ciphertext
                    (GCM-Init iv cntr_0 k) ; gcm_init
                )
            )                                                                     
            (send "ACK")                                                                ; Secondary acks
            (recv "STOP")                                                               ; Primary pulls the SDA SDL high (stop condtion)
        )
    )
)

(defskeleton I2C-Secure
  (vars (secondary_address name) (secondary_register text) (byte_data cntr_0 cntr_1 cntr_2 iv data) (k skey)) 
  (defstrand primary 10 (secondary_address secondary_address) (secondary_register secondary_register) (byte_data byte_data) (cntr_0 cntr_0) (cntr_1 cntr_1) (cntr_2 cntr_2) (iv iv) (k k))

   ;; assumptions
   (facts (neq cntr_0 cntr_1))
   (facts (neq cntr_1 cntr_2))
   (facts (neq cntr_0 cntr_2))
   
   (uniq-gen k iv cntr_0 cntr_1 cntr_2)
   (pen-non-orig k iv cntr_0 cntr_1 cntr_2)
)

(defprotocol I2C basic
    (defrole primary
        (vars (secondary_address secondary_register name) (byte_data clock data))
        (trace
            (send "START")                              ; Primary takes control of the bus                            
            (send (cat secondary_address "WRITE_REQ"))  ; Primary sends a write request for a specific secondary
            (recv "ACK")                                ; Secondary acks
            (send secondary_register)                   ; Primary sends a specific register it wishes to write to write to on the secondary
            (recv "ACK")                                ; Secondary acks
            (send byte_data)                            ; Primary sends data to be written to register 
            (recv "ACK")                                ; Secondary confirms it had recieved the data
            (send "STOP")                               ; Primary pulls the SDA SDL high (stop condtion)
        )
    )
    ;; secondary (slave device 2)
    (defrole secondary
        (vars (secondary_address secondary_register name) (byte_data clock data))
        (trace
            (recv "START")                              ; Primary takes control of the bus                            
            (recv (cat secondary_address "WRITE_REQ"))  ; Primary sends a write request for a specific secondary
            (send "ACK")                                ; Secondary acks
            (recv secondary_register)                   ; Primary sends a specific register it wishes to write to write to on the secondary
            (send "ACK")                                ; Secondary acks
            (recv byte_data)                            ; Primary sends data to be written to register 
            (send "ACK")                                ; Secondary confirms it had recieved the data
            (recv "STOP")                               ; Primary pulls the SDA SDL high (stop condtion)
        )
    )
)


;; (defskeleton I2C
;;   (vars (secondary_address name)) 
;;   (defstrand primary 5 (secondary_address secondary_address))
;; )
