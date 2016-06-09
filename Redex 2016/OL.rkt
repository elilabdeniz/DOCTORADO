#lang racket 
(require redex) 
(require pict)

(define-language PCF
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

(define-metafunction REDEX
    unique : any ... -> boolean
    [(unique any_!_1 ...) #t]
    [(unique _ ...) #f])

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
     (⇓ (M_0 M_1 ...) ρ : V)])


(define-language OverloadingLambda
  (t ::= nv
         v)
  (nv ::=
         x
         (t t)
         (+ t t) 
         (olet (x T) = t in t)
         (t :: T))
  (v ::= true
         flase
         number
        (λ (x T) t))
  (T (→ T T) num bool)
  (x ::= variable-not-otherwise-mentioned))

(define-extended-language OverloadingLambdaT OverloadingLambda
    (Γ ::= ((x T) ...)))

#|(define-language L 
  (e (e e) 
     (λ (x t) e) 
     x 
     (amb e ...) 
     number 
     (+ e ...) 
     (if0 e e e) 
     (fix e)) 
  (t (→ t t) num) 
  (x variable-not-otherwise-mentioned))

(define-extended-language L+Γ L 
  [Γ · (x : t Γ)]) 


(define-judgment-form 
 L+Γ
  #:mode (types I I O) 
  #:contract (types Γ e t) 
  
  [(types Γ e_1 (→ t_2 t_3)) 
   (types Γ e_2 t_2) 
   ------------------------- 
   (types Γ (e_1 e_2) t_3)] 
  
  [(types (x : t_1 Γ) e t_2) 
   ----------------------------------- 
   (types Γ (λ (x t_1) e) (→ t_1 t_2))] 
  
  [(types Γ e (→ (→ t_1 t_2) (→ t_1 t_2))) 
   --------------------------------------- 
   (types Γ (fix e) (→ t_1 t_2))] 
  
  [--------------------- 
   (types (x : t Γ) x t)] 
  
  [(types Γ x_1 t_1) 
   (side-condition (different x_1 x_2)) 
   ------------------------------------ 
   (types (x_2 : t_2 Γ) x_1 t_1)] 
  
  [(types Γ e num) ... 
   ----------------------- 
   (types Γ (+ e ...) num)] 
  
  [-------------------- 
   (types Γ number num)] 
  
  [(types Γ e_1 num) 
   (types Γ e_2 t) 
   (types Γ e_3 t) 
   ----------------------------- 
   (types Γ (if0 e_1 e_2 e_3) t)] 
  
  [(types Γ e num) ... 
   -------------------------- 
   (types Γ (amb e ...) num)])

(define-metafunction L+Γ
  [(different x_1 x_1) #f] 
  [(different x_1 x_2) #t])

(define-extended-language Ev L+Γ
  (p (e ...))
  (P (e ... E e ...))
  (E (v E)
     (E e)
     (+ v ... E e ...)
     (if0 E e e)
     (fix E)
     hole)
  (v (λ (x t) e)
     (fix v)
     number))

(define-metafunction Ev
  Σ : number ... -> number
  [(Σ number ...)
   ,(apply + (term (number ...)))])


(require redex/tut-subst)
(define-metafunction Ev
  subst : x v e -> e
  [(subst x v e)
   ,(subst/proc x? (list (term x)) (list (term v)) (term e))])
(define x? (redex-match Ev x))

(define red
  (reduction-relation
   Ev
   #:domain p
   (--> (in-hole P (if0 0 e_1 e_2))
        (in-hole P e_1)
        "if0t")
   (--> (in-hole P (if0 v e_1 e_2))
        (in-hole P e_2)
        (side-condition (not (equal? 0 (term v))))
        "if0f")
   (--> (in-hole P ((fix (λ (x t) e)) v))
        (in-hole P (((λ (x t) e) (fix (λ (x t) e))) v))
        "fix")
   (--> (in-hole P ((λ (x t) e) v))
        (in-hole P (subst x v e))
        "βv")
   (--> (in-hole P (+ number ...))
        (in-hole P (Σ number ...))
        "+")
   (--> (e_1 ... (in-hole E (amb e_2 ...)) e_3 ...)
        (e_1 ... (in-hole E e_2) ... e_3 ...)
        "amb")))

(define (types? e)
  (not (null? (judgment-holds (types · ,e t)
                              t))))
 
(define v? (redex-match Ev v))
 
(define (reduces? e)
  (not (null? (apply-reduction-relation
               red
               (term (,e))))))

(define (progress-holds? e)
  (if (types? e)
      (or (v? e)
          (reduces? e))
      #t))

(redex-check Ev e (progress-holds? (term e)))|#
