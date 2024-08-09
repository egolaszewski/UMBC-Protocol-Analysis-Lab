(herald "I2C-Secure" (limit 80000))

;; Helper Macros ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defmacro (xor a b) 
    (cat
        (enc a b) 
        (enc b a)
    )
)

;; AES-GCM Macros ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; (defmacro (GCM-GF128-MulH-AAD h auth_data)
;;     ; H (h) = (enc 0^128 k) hash of key
;;     ; A (auth_data) = Data which is only authenticated (not encrypted?)
    
;;     (hash h auth_data) ; using hash to representThe Galois Field multiplication operation, 
;;                        ; typically written as H×XH×X or MulH(X)MulH(X), takes these two 
;;                        ; 128-bit inputs and performs a multiplication in GF(2128)GF(2128).

;;     ;; returns authenticated MultH (but not encrypted), this can be xor'd with ciphertext1
;; )

(defmacro (GCM-GF128-MulH h x)
    ; note that the multH_prev can be ct if there is no ADD provided
    ; note that x can be any value (ciphertext, or the previous output of another GCM-GF128-MulH)
    (hash h x) ; represents multiplication
)

(defmacro (GCM-H zero_vector k)
    (enc zero_vector k)
    ;; returns H vector: encryption of a 0^128 bit vector by skey k 
)

(defmacro (GCM-Counter-Encrypt iv cntr k)
    (enc 
        (hash iv cntr) ; represents multiplication
        k
    )
    ;; returns the encryption of (IV || CNTR) under skey "k"
)

(defmacro (GCM-Block-Encrypt iv cntr pt k)
    (xor 
        (GCM-Counter-Encrypt iv cntr k)
        pt
    )
    ;; returns MulH vector i.e. (direct ciphertext)
)

(defmacro (GCM-Tag mulH_prev h data_len iv cntr_init k)
    ; Note the data length includes the mulitplication of the cipher length and authentication data: len(A) || len(C)
    (xor
        (GCM-GF128-MulH
            h
            (xor mulH_prev data_len)
        )
        (GCM-Counter-Encrypt iv cntr_init k) ; E(K,Y0)
    )   
    ;; returns MAC "TAG"
)

;; I2C-Secure Implementation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defprotocol I2C-Secure basic
    ;; Primary device on a serial bus
    (defrole primary
        (vars 
            (secondary_address name)
            (secondary_register text)
            (byte_data cntr_init iv data)
            (k skey)
            (len_secondary_address len_byte_data c_len)
            (zero_vector vector)
        )
        (trace
            ; Primary takes control of the bus 
            (send "START")                           
            
            ; Primary sends a write request for a specific secondary
            (send (cat secondary_address "WRITE_REQ"))                                  
            
            ; Secondary sends ack
            (recv "ACK")                                                                
            
            ; Primary sends a specific register that it wishes to write to
            (send                                                                
                (GCM-Block-Encrypt ;ct1
                    iv 
                    (hash (hash cntr_init)) ; increment counter
                    secondary_register 
                    k
                )
            )

            ; Secondary sends ack
            (recv "ACK")

            ; Primary sends data to be written to register 
            (send 
                (GCM-Block-Encrypt ; ct2
                    iv 
                    (hash (hash (hash cntr_init))) ; increment counter
                    byte_data 
                    k
                )
            )

            ; Secondary sends ack                                                          
            (recv "ACK")

            ; Primary sends "TAG"                             
            (send
                (GCM-Tag
                    (GCM-GF128-MulH ; multH_2
                        (GCM-H zero_vector k) ; h
                        (xor
                            (GCM-Block-Encrypt iv (hash (hash (hash cntr_init))) byte_data k) ; ct2
                            (GCM-GF128-MulH ; multH_1
                                (GCM-H zero_vector k) ; h
                                (GCM-Block-Encrypt iv (hash (hash cntr_init)) secondary_register k) ; ct1
                            )
                        )
                    )
                    (GCM-H zero_vector k) ; h
                    (cat len_secondary_address len_byte_data) ; represents an addition of data lengths: len(C)
                    iv 
                    cntr_init 
                    k
                )
            )
            
            ; Secondary acks                                                              
            (recv "ACK")

            ; Primary pulls the SDA SDL high (stop condtion)
            (send "STOP")
        )
    )

    ;; Secondary device on a serial bus
    (defrole secondary
        (vars 
            (secondary_address name)
            (secondary_register text)
            (byte_data cntr_init iv data)
            (k skey)
            (len_secondary_address len_byte_data c_len)
            (zero_vector vector)
        )
        (trace
            ; Primary takes control of the bus 
            (recv "START")                           
            
            ; Primary sends a write request for a specific secondary
            (recv (cat secondary_address "WRITE_REQ"))                                  
            
            ; Secondary sends ack
            (send "ACK")                                                                
            
            ; Primary sends a specific register that it wishes to write to
            (recv                                                                
                (GCM-Block-Encrypt ;ct1
                    iv 
                    (hash (hash cntr_init)) ; increment counter
                    secondary_register 
                    k
                )
            )

            ; Secondary sends ack
            (send "ACK")

            ; Primary sends data to be written to register 
            (recv 
                (GCM-Block-Encrypt ; ct2
                    iv 
                    (hash (hash (hash cntr_init))) ; increment counter
                    byte_data 
                    k
                )
            )

            ; Secondary sends ack                                                          
            (send "ACK")

            ; Primary sends "TAG"                             
            (recv
                (GCM-Tag
                    (GCM-GF128-MulH ; multH_2
                        (GCM-H zero_vector k) ; h
                        (xor
                            (GCM-Block-Encrypt iv (hash (hash (hash cntr_init))) byte_data k) ; ct2
                            (GCM-GF128-MulH ; multH_1
                                (GCM-H zero_vector k) ; h
                                (GCM-Block-Encrypt iv (hash (hash cntr_init)) secondary_register k) ; ct1
                            )
                        )
                    )
                    (GCM-H zero_vector k) ; h
                    (cat len_secondary_address len_byte_data) ; represents an addition of data lengths: len(C)
                    iv 
                    cntr_init 
                    k
                )
            )
            
            ; Secondary acks                                                              
            (send "ACK")

            ; Primary pulls the SDA SDL high (stop condtion)
            (recv "STOP")
        )
    )
    (lang
        (c_len atom)
        (vector atom)
    )
)

(defskeleton I2C-Secure
    (vars (zero_vector vector) (secondary_address name) (secondary_register text) (byte_data cntr_init iv data) (k skey)) 
    (defstrand primary 10 (zero_vector zero_vector) (secondary_address secondary_address) (secondary_register secondary_register) (byte_data byte_data) (cntr_init cntr_init) (iv iv) (k k))
    (defstrand secondary 10 (zero_vector zero_vector) (secondary_address secondary_address) (secondary_register secondary_register) (byte_data byte_data) (cntr_init cntr_init) (iv iv) (k k))
   
    ; Assumptions
    (pen-non-orig k iv cntr_init)

    (comment "[N_EXEC] Normal Execution of Protocol")
)

(defskeleton I2C-Secure
    (vars (zero_vector vector) (secondary_address name) (secondary_register text) (byte_data cntr_init iv data) (k skey)) 
    (defstrand primary 10 (zero_vector zero_vector) (secondary_address secondary_address) (secondary_register secondary_register) (byte_data byte_data) (cntr_init cntr_init) (iv iv) (k k))
   
    ; Assumptions
    (pen-non-orig k iv cntr_init)  ; Assume the advesary doesn't know key, iv, or the init-counter value

    (comment "[P_POV] Primary's Perspective")
)

(defskeleton I2C-Secure
    (vars (zero_vector vector) (secondary_address name) (secondary_register text) (byte_data cntr_init iv data) (k skey)) 
    (defstrand secondary 10 (zero_vector zero_vector) (secondary_address secondary_address) (secondary_register secondary_register) (byte_data byte_data) (cntr_init cntr_init) (iv iv) (k k))
   
    ; Assumptions
    (pen-non-orig k iv cntr_init)  ; Assume the advesary doesn't know key, iv, or the init-counter value

    (comment "[S_POV] Secondary's Perspective")
)

(defskeleton I2C-Secure
    (vars (zero_vector vector) (secondary_address name) (secondary_register text) (byte_data cntr_init iv data) (k skey)) 
    (defstrand primary 10 (zero_vector zero_vector) (secondary_address secondary_address) (secondary_register secondary_register) (byte_data byte_data) (cntr_init cntr_init) (iv iv) (k k))
    (defstrand secondary 10 (zero_vector zero_vector) (secondary_address secondary_address) (secondary_register secondary_register) (byte_data byte_data) (cntr_init cntr_init) (iv iv) (k k))

    ; Assumptions
    (pen-non-orig k iv)        ; Assume the advesary doesn't know key, iv

    (comment "[PS_POV_CNTR_NOTFRESH] Secondary's Perspective: cntr_init is not fresh")
)

(defskeleton I2C-Secure
    (vars (zero_vector vector) (secondary_address name) (secondary_register text) (byte_data cntr_init iv data) (k skey)) 
    (defstrand primary 10 (zero_vector zero_vector) (secondary_address secondary_address) (secondary_register secondary_register) (byte_data byte_data) (cntr_init cntr_init) (iv iv) (k k))
    (defstrand secondary 10 (zero_vector zero_vector) (secondary_address secondary_address) (secondary_register secondary_register) (byte_data byte_data) (cntr_init cntr_init) (iv iv) (k k))

    ; Assumptions
    (pen-non-orig k iv)        ; Assume the advesary doesn't know key, iv

    (comment "[PS_POV_CNTR&K_NOTFRESH] Secondary's Perspective: cntr_init is not fresh")
)


;; I2C Implementation ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; (defprotocol I2C basic
;;     (defrole primary
;;         (vars (secondary_address secondary_register name) (byte_data clock data))
;;         (trace
;;             (send "START")                              ; Primary takes control of the bus                            
;;             (send (cat secondary_address "WRITE_REQ"))  ; Primary sends a write request for a specific secondary
;;             (recv "ACK")                                ; Secondary acks
;;             (send secondary_register)                   ; Primary sends a specific register it wishes to write to write to on the secondary
;;             (recv "ACK")                                ; Secondary acks
;;             (send byte_data)                            ; Primary sends data to be written to register 
;;             (recv "ACK")                                ; Secondary confirms it had recieved the data
;;             (send "STOP")                               ; Primary pulls the SDA SDL high (stop condtion)
;;         )
;;     )
;;     ;; secondary (slave device 2)
;;     (defrole secondary
;;         (vars (secondary_address secondary_register name) (byte_data clock data))
;;         (trace
;;             (recv "START")                              ; Primary takes control of the bus                            
;;             (recv (cat secondary_address "WRITE_REQ"))  ; Primary sends a write request for a specific secondary
;;             (send "ACK")                                ; Secondary acks
;;             (recv secondary_register)                   ; Primary sends a specific register it wishes to write to write to on the secondary
;;             (send "ACK")                                ; Secondary acks
;;             (recv byte_data)                            ; Primary sends data to be written to register 
;;             (send "ACK")                                ; Secondary confirms it had recieved the data
;;             (recv "STOP")                               ; Primary pulls the SDA SDL high (stop condtion)
;;         )
;;     )
;; )

;; (defskeleton I2C
;;   (vars (secondary_address name)) 
;;   (defstrand primary 5 (secondary_address secondary_address))
;; )
