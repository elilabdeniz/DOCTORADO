#lang racket 
(require redex)
(require pict)
(require "subst.rkt")

#|(define-language PCF
    (M ::=
       N O X L
       (μ (X : T) L)
       (M M ...)
       (if0 M M M))
    (X ::= variable-not-otherwise-mentioned)
    (L ::= (λ ([X : T] ...) M))
    (V ::= N O L)
    (N ::= number)
    (O ::= O1 O2)
    (O1 ::= add1 sub1)
    (O2 ::= + *)
    (T ::= num (T ... -> T)))

(define-extended-language PCFT PCF
    (Γ ::= ((X T) ...)))

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
    unique ⊆ any × ...
    [(unique any_!_1 ...)])



(define-judgment-form PCFT
    #:mode (⊢ I I I O)
    #:contract (⊢ Γ M : T)
    [(lookup Γ X T)
     -------------- var
     (⊢ Γ X : T)]
    [------------- num
     (⊢ Γ N : num)]
    [----------------------- op1
     (⊢ Γ O1 : (num -> num))]
    [--------------------------- op2
     (⊢ Γ O2 : (num num -> num))]
    [(⊢ Γ M_1 : num)
     (⊢ Γ M_2 : T)
     (⊢ Γ M_3 : T)
     --------------------------- if0
     (⊢ Γ (if0 M_1 M_2 M_3) : T)]
    [(⊢ (ext Γ (X T)) L : T)
     ----------------------- μ
     (⊢ Γ (μ (X : T) L) : T)]
    [(⊢ Γ M_0 : (T_1 ..._1 -> T))
     (⊢ Γ M_1 : T_1) ...
     ----------------------- app
     (⊢ Γ (M_0 M_1 ..._1) : T)]
    [(unique X ...)
     (⊢ (ext Γ (X T) ...) M : T_n)
     ------------------------------------------ λ
     (⊢ Γ (λ ([X : T] ...) M) : (T ... -> T_n))])


(define r
    (reduction-relation
     PCF #:domain M
     (--> (μ (X : T) M)
          (subst (X (μ (X : T) M)) M)
          μ)
  
     (--> ((λ ([X : T] ...) M_0) M ...)
          (subst (X M) ... M_0)
          β)
  
     (--> (O N_0 ...) N_1
          (judgment-holds (δ (O N_0 ...) N_1))
          δ)
  
     (--> (if0 0 M_1 M_2) M_1 if-t)
     (--> (if0 N M_1 M_2) M_2
          (side-condition (not (zero? (term N))))
          if-f)))

(define-judgment-form PCF
    #:mode (δ I O)
    #:contract (δ (O N ...) N)
    [(δ (+ N_0 N_1) ,(+ (term N_0) (term N_1)))]
    [(δ (* N_0 N_1) ,(* (term N_0) (term N_1)))]
    [(δ (sub1 N) ,(sub1 (term N)))]
    [(δ (add1 N) ,(add1 (term N)))])

(define-extended-language PCFv PCF
  (E ::= hole
     (V ... E M ...)
     (if0 E M M)))

(define v
  (extend-reduction-relation
   r PCF #:domain M
   (--> ((λ ([X : T] ...) M_0) V ...)
        (subst (X V) ... M_0)
        β)))

(define -->v
  (context-closure v PCFv E))

(define-extended-language PCF⇓ PCF
    (V ::= N O (L ρ) ((μ (X : T) L) ρ))
    (ρ ::= ((X V) ...)))




(define-judgment-form PCF⇓
    #:mode (⇓ I I I O)
    #:contract (⇓ M ρ : V)
  
    [(⇓ N ρ : N)]
    [(⇓ O ρ : O)]
    [(⇓ L ρ : (L ρ))]
    [(⇓ (μ (X_f : T_f) L) ρ : ((μ (X_f : T_f) L) ρ))]
  
    [(lookup ρ X V)
     --------------
     (⇓ X ρ : V)]
  
    [(⇓ M_0 ρ : N)
     (where M ,(if (zero? (term N)) (term M_1) (term M_2)))
     (⇓ M ρ : V)
     ---------------------------
     (⇓ (if0 M_0 M_1 M_2) ρ : V)]
  
    [(⇓ M_0 ρ : O)
     (⇓ M_1 ρ : N)
     ...
     (δ (O N ...) N_1)
     -----------------------
     (⇓ (M_0 M_1 ...) ρ : N_1)]
  
    [(⇓ M_0 ρ : ((λ ([X_1 : T] ...) M) ρ_1))
     (⇓ M_1 ρ : V_1)
     ...
     (⇓ M (ext ρ_1 (X_1 V_1) ...) : V)
     -----------------------------------
     (⇓ (M_0 M_1 ...) ρ : V)]
  
    [(⇓ M_0 ρ : (name f ((μ (X_f : T_f) (λ ([X_1 : T] ...) M)) ρ_1)))
     (⇓ M_1 ρ : V_1)
     ...
     (⇓ M (ext ρ_1 (X_f f) (X_1 V_1) ...) : V)
     -----------------------------------------
     (⇓ (M_0 M_1 ...) ρ : V)])|#

;--------------------------------------------------------------------------------------------------------------------
;--------------------------------------------------------------------------------------------------------------------
(define-language OL
  (M ::= NV
         V)
  (NV ::=
         X
         (M M)
         (mlet (X T) = M in M)
         (M :: T)
         ;(add1 t)
         ;(not t)
         )
  (V ::= B N L O) 
  (B ::= true false)
  (N ::= number)
  (L ::= (λ (X T) M))
  (O ::= OB ON)
  (OB ::= OB1)
  (ON ::= ON1)
  (OB1 ::= not)
  (ON1 ::= add1)
  (T (→ T T) num bool)
  (X ::= variable-not-otherwise-mentioned))
;--------------------------------------------------------------------------------------------------------------------
(define-extended-language OL⇓ OL
    (V ::= B N O (L ρ))
    (ρ ::= ((X (V ...)) ...)))
;--------------------------------------------------------------------------------------------------------------------
(define-extended-language OLρ OL⇓
    (C ::=
       V
       (M ρ)
       (C :: T)
       (mlet (X T) = C in C)
       (C C))
    (E ::= hole (V E)))
;--------------------------------------------------------------------------------------------------------------------
(define vρ
    (reduction-relation
     OLρ #:domain C
     (--> (B ρ) B ρ-bool)
     (--> (N ρ) N ρ-num)
     (--> (O ρ) O ρ-op)
     ;-------------------------------------
     (--> ((M1 M2) ρ) ((M1 ρ) (M2 ρ)) ρ-app)
     (--> ((M :: T) ρ) ((M ρ) :: T) ρ-asc)
     (--> ((mlet (X T) = M1 in M2) ρ) (mlet (X T) = (M1 ρ) in (M2 ρ)) ρ-let)
     (--> (X ρ) V
          (judgment-holds (lookup ρ X V))
          ρ-x)
     ;-------------------------------------
     (--> (((λ (X : T) M) ρ) V)
          ((subst (X V) M ) ρ)
          app)
     
     (--> (OB V ...) V_1
          (judgment-holds (δB (O V ...) V_1))
          δB)
     
     (--> (ON V ...) V_1
          (judgment-holds (δN (O V ...) V_1))
          δN)
     
     (--> (V :: T) V asc)
     
     (--> (mlet (X T) = V in (M  ρ))
          (M (ext ρ (X V)))
          let)
     ;-------------------------------------
     ))

(define-judgment-form OL
    #:mode (δN I O)
    #:contract (δN (O N ...) N)
    [(δN (add1 N) ,(add1 (term N)))])

(define-judgment-form OL
    #:mode (δB I O)
    #:contract (δB (O B ...) B)
    [(δB (not B) ,(not (term B)))])

(define-language REDEX)


(define-judgment-form REDEX
    #:mode (lookup I I O)
    #:contract (lookup ((any any) ...) any any)
    [(lookup (_ ... (any any_0) _ ...) any any_0)])


(define-metafunction REDEX
    ext1 : ((any any) ...) (any any) -> ((any any) ...)
    [(ext1 (any_0 ... (any_k (any_v0 ...)) any_1 ...) (any_k any_v1))
     (any_0 ... (any_k (any_v1 any_v0 ...)) any_1 ...)]
    [(ext1 (any_0 ...) (any_k any_v1))
     ((any_k (any_v1)) any_0 ...)])


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
    unique ⊆ any × ...
    [(unique any_!_1 ...)])
