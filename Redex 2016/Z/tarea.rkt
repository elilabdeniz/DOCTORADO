#|(define-language PCF
    (M ::=
       N O X L
       (µ (X : T) L)
       (M M ...)
       (if0 M M M))
    (X ::= variable-not-otherwise-mentioned)
    (L ::= (? ([X : T] ...) M))
    (V ::= N O L)
    (N ::= number)
    (O ::= O1 O2)
    (O1 ::= add1 sub1)
    (O2 ::= + *)
    (T ::= num (T ... -> T)))

(define-extended-language PCFT PCF
    (G ::= ((X T) ...)))

(define-language REDEX)


(define-judgment-form REDEX
    #:mode (lookup I I O)
    #:contract (lookup ((any any) ...) any any)
    [(lookup (_ ... (any any_0) _ ...) any any_0)])


(define-metafunction REDEX
    ext1 : ((any any) ...) (any any) -> ((any any) ...)
    [(ext1 (any_0 ... (any_k any_v0) any_1 ...) (any_k any_v1))
     (any_0 ... (any_k any_v1) any_1 ...)]
    [(ext1 (any_0 ...) (any_k any_v1))
     ((any_k any_v1) any_0 ...)])


(define-metafunction REDEX
    ext : ((any any) ...) (any any) ... -> ((any any) ...)
    [(ext any) any]
    [(ext any any_0 any_1 ...)
     (ext1 (ext any any_1 ...) any_0)])

#|(define-metafunction REDEX
    unique : any ... -> boolean
    [(unique any_!_1 ...) #t]
    [(unique _ ...) #f])|#

(define-relation REDEX
    unique ? any × ...
    [(unique any_!_1 ...)])



(define-judgment-form PCFT
    #:mode (? I I I O)
    #:contract (? G M : T)
    [(lookup G X T)
     -------------- var
     (? G X : T)]
    [------------- num
     (? G N : num)]
    [----------------------- op1
     (? G O1 : (num -> num))]
    [--------------------------- op2
     (? G O2 : (num num -> num))]
    [(? G M_1 : num)
     (? G M_2 : T)
     (? G M_3 : T)
     --------------------------- if0
     (? G (if0 M_1 M_2 M_3) : T)]
    [(? (ext G (X T)) L : T)
     ----------------------- µ
     (? G (µ (X : T) L) : T)]
    [(? G M_0 : (T_1 ..._1 -> T))
     (? G M_1 : T_1) ...
     ----------------------- app
     (? G (M_0 M_1 ..._1) : T)]
    [(unique X ...)
     (? (ext G (X T) ...) M : T_n)
     ------------------------------------------ ?
     (? G (? ([X : T] ...) M) : (T ... -> T_n))])


(define r
    (reduction-relation
     PCF #:domain M
     (--> (µ (X : T) M)
          (subst (X (µ (X : T) M)) M)
          µ)
  
     (--> ((? ([X : T] ...) M_0) M ...)
          (subst (X M) ... M_0)
          ß)
  
     (--> (O N_0 ...) N_1
          (judgment-holds (d (O N_0 ...) N_1))
          d)
  
     (--> (if0 0 M_1 M_2) M_1 if-t)
     (--> (if0 N M_1 M_2) M_2
          (side-condition (not (zero? (term N))))
          if-f)))

(define-judgment-form PCF
    #:mode (d I O)
    #:contract (d (O N ...) N)
    [(d (+ N_0 N_1) ,(+ (term N_0) (term N_1)))]
    [(d (* N_0 N_1) ,(* (term N_0) (term N_1)))]
    [(d (sub1 N) ,(sub1 (term N)))]
    [(d (add1 N) ,(add1 (term N)))])

(define-extended-language PCFv PCF
  (E ::= hole
     (V ... E M ...)
     (if0 E M M)))

(define v
  (extend-reduction-relation
   r PCF #:domain M
   (--> ((? ([X : T] ...) M_0) V ...)
        (subst (X V) ... M_0)
        ß)))

(define -->v
  (context-closure v PCFv E))

(define-extended-language PCF? PCF
    (V ::= N O (L ?) ((µ (X : T) L) ?))
    (? ::= ((X V) ...)))




(define-judgment-form PCF?
    #:mode (? I I I O)
    #:contract (? M ? : V)
  
    [(? N ? : N)]
    [(? O ? : O)]
    [(? L ? : (L ?))]
    [(? (µ (X_f : T_f) L) ? : ((µ (X_f : T_f) L) ?))]
  
    [(lookup ? X V)
     --------------
     (? X ? : V)]
  
    [(? M_0 ? : N)
     (where M ,(if (zero? (term N)) (term M_1) (term M_2)))
     (? M ? : V)
     ---------------------------
     (? (if0 M_0 M_1 M_2) ? : V)]
  
    [(? M_0 ? : O)
     (? M_1 ? : N)
     ...
     (d (O N ...) N_1)
     -----------------------
     (? (M_0 M_1 ...) ? : N_1)]
  
    [(? M_0 ? : ((? ([X_1 : T] ...) M) ?_1))
     (? M_1 ? : V_1)
     ...
     (? M (ext ?_1 (X_1 V_1) ...) : V)
     -----------------------------------
     (? (M_0 M_1 ...) ? : V)]
  
    [(? M_0 ? : (name f ((µ (X_f : T_f) (? ([X_1 : T] ...) M)) ?_1)))
     (? M_1 ? : V_1)
     ...
     (? M (ext ?_1 (X_f f) (X_1 V_1) ...) : V)
     -----------------------------------------
     (? (M_0 M_1 ...) ? : V)])|#

;--------------------------------------------------------------------------------------------------------------------
;--------------------------------------------------------------------------------------------------------------------