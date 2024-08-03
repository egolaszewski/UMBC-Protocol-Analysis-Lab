(herald "AES-GCM")


;; NOTE:
; VARIABLE - iv (type data): init vector (init all zeros, 128 bit vector)
; VARIABLE - counter (type data):
; VARIABLE -k (type skey): Secretly sharedkey
; RETURN-INFO - Mul(H)_Init

(defmacro (xor a b) 
    (cat
        (enc a b) 
        (enc b a)
    )
)

;; helper function
(defmacro (GCM-Encrypt iv cntr k)
    (enc 
        (cat iv cntr_0)
        k
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

