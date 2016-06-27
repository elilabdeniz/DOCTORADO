#lang play 
(require redex)
(require pict)
(require "subst.rkt")

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
  (V ::= B N CH L O) 
  (B ::= #t #f)
  (CH ::= char)
  (N ::= number)
  (L ::= (λ (X T) M))
  (O ::= OB ON)
  (OB ::= OB1)
  (ON ::= ON1)
  (OB1 ::= not)
  (ON1 ::= add1)
  (T (→ T T) num bool char)
  (X ::= variable-not-otherwise-mentioned))
;--------------------------------------------------------------------------------------------------------------------
(define-extended-language OL⇓ OL
    (W ::= B N CH O (L ρ))
    (ρ ::= ((X ((T W) ...)) ...)))
;--------------------------------------------------------------------------------------------------------------------
(define-extended-language OLρ OL⇓
    (C ::=
       W
       (M ρ)
       (C :: T)
       (mlet (X T) = C in C)
       (C C))
    (E ::= hole (E C) (W E) (E :: T) (mlet (X T) = E in C)))
;--------------------------------------------------------------------------------------------------------------------
(define-extended-language OLρI OLρ
    (CI ::= (C I) W)
    (I ::= (→ I I) T *))
;--------------------------------------------------------------------------------------------------------------------
(define-extended-language OLT OL
    (Γ  ::= ((X T) ...))
    (A  ::= ((X (T ...)) ...))
    (T* ::= (T ...)))
;--------------------------------------------------------------------------------------------------------------------
(define-judgment-form OLT
    #:mode (⊢ I I I I O)
    #:contract (⊢ A Γ M : T*)
    [(lookup Γ X T)
     -------------- var_1
     (⊢ A Γ X : (T))]

    [(lookup A X M)
     -------------- var_2
     (⊢ A Γ X : M)]
  
    [------------- num
     (⊢ A Γ N : (num))]
  
    [------------- bool
     (⊢ A Γ B : (bool))]
  
    [----------------------- opB1
     (⊢ A Γ OB1 : (→ bool bool))]
  
    [--------------------------- opN1
     (⊢ A Γ ON1 : (→ num num))]
  
    [(⊢ A Γ M_1 : T_1*)
     (⊢ A Γ M_1 : T_2*)
     ----------------------- app
     (⊢ A Γ (M_1 M_2) : T_2*)]

    [(⊢ A Γ M : T*)
    (side-condition (esta? T* T))
    ----------------------- asc
    (⊢ A Γ (M :: T) : T)]

     [(⊢ A Γ M_1 : T_1*)
     (side-condition (esta? T_1* T_1))
     (⊢ (ext A (X T_1)) Γ M_2 : T_2*)
     ----------------------- let
     (⊢ A Γ (mlet (X T_1) = M_1 in M_2) : T_2*)]
  
    [(unique X)
     (⊢ A (extT Γ (X T)) M : T*)
     ------------------------------------------ λ
     (⊢ A Γ (λ (X T) M) : (→ T T*))])
;--------------------------------------------------------------------------------------------------------------------
(define value? (redex-match OLρI  W))

(define (is-value? t)
        (redex-match? OLρI  W t))
;--------------------------------------------------------------------------------------------------------------------
(define vρ
    (reduction-relation
     OLρI #:domain CI
     (--> ((B ρ) I) B ρ-bool)
     (--> ((N ρ) I) N ρ-num)
     (--> ((CH ρ) I) CH ρ-char)
     (--> ((O ρ) I) O ρ-op)
     (--> (((λ (X T) M) ρ) I) ((λ (X T) M) ρ) ρ-abs)
     ;-------------------------------------
     (--> (((M_1 M_2) ρ) I) (((M_1 ρ) (M_2 ρ)) I) ρ-app)
     (--> (((M :: T) ρ) I) (((M ρ) :: T) I) ρ-asc)
     (--> (((mlet (X T) = M_1 in M_2) ρ) I) ((mlet (X T) = (M_1 ρ) in (M_2 ρ)) I) ρ-let)
     (--> ((X ρ) I) W
          (judgment-holds (lookup2 ρ X I W))
          ρ-x)
     ;-------------------------------------
     (--> ((((λ (X T) M) ρ) W) I)
          (((subst (X W) M ) ρ) I)
          app)
     
     (--> ((OB W ...) I) W_1
          (judgment-holds (δB (OB W ...) W_1))
          δB)
     
     (--> ((ON W ...) I) W_1
          (judgment-holds (δN (ON W ...) W_1))
          δN)
     
     (--> ((W :: T) I) W asc)
     
     (--> ((mlet (X T) = W in (M  ρ)) I)
          ((M (ext ρ (X (T W)))) I)
          let
          (side-condition (not (is-value? (term M)))))
     ;-------------------------------------
     (--> ((mlet (X T) = C_1 in C_2) I)
          ((mlet (X T) =  (configuration ,(apply-reduction-relation vρ (term (C_1 T)))) in C_2) I)
          let_1
          (side-condition (not (is-value? (term C_1)))))
      (--> ((C :: T) T)
           (((configuration ,(apply-reduction-relation vρ (term (C T)))) :: T) T)
           asc_1
           (side-condition (not (is-value? (term C)))))
      (--> ((C_1 C_2) I)
           (((configuration ,(apply-reduction-relation vρ (term (C_1 (→ * I))))) C_2) I)
           app_1
           (side-condition (not (is-value? (term C_1)))))
      
      (--> ((((λ (X T) M) ρ) C_2) I)
           ((((λ (X T) M) ρ) (configuration ,(apply-reduction-relation vρ (term (C_2 T))))) I)
           app_2
           (side-condition (not (is-value? (term C_2)))))

      (--> ((O C_2) I)
           ((O (configuration ,(apply-reduction-relation vρ (term (C_2 (typi O)))))) I)
           app_2O
           (side-condition (not (is-value? (term C_2)))))
     ;-------------------------------------
     ))
;--------------------------------------------------------------------------------------------------------------------
(define-metafunction OLρI
  [(configuration ((C I))) C]
  [(configuration (CI)) CI])

(define-metafunction OLρI
    [(typi add1) num]
    [(typi not) bool])
;--------------------------------------------------------------------------------------------------------------------
(define-judgment-form OL
    #:mode (δN I O)
    #:contract (δN (O N ...) N)
    [(δN (add1 N) ,(add1 (term N)))])

(define-judgment-form OL
    #:mode (δB I O)
    #:contract (δB (O B ...) B)
    [(δB (not B) ,(not (term B)))])

(define-metafunction OLρI
  [(consistentType? T T) #t]
  [(consistentType? T *) #t]
  [(consistentType? (→ T_1 T_2) (→ I_1 I_2)) ,(and (term (consistentType? T_1 I_1)) (term (consistentType? T_2 I_2)))]
  [(consistentType? T I) #f])

(define-metafunction OLT
  [(esta? (_ ... T _ ...) T) #t]
  [(esta? T* T) #f])
;--------------------------------------------------------------------------------------------------------------------
(define-language REDEX)

(define-relation REDEX
    unique ⊆ any × ...
    [(unique any_!_1 ...)])

(define-judgment-form REDEX
    #:mode (lookup I I O)
    #:contract (lookup ((any any) ...) any any)
    [(lookup (_ ... (any any_0) _ ...) any any_0)])

(define-judgment-form REDEX
    #:mode (lookup2 I I I O)
    #:contract (lookup2 ((any any) ...) any any any)
    [(side-condition (consistentType? any_i any_ip))
     -----------------------------------------
     (lookup2(_ ... (any_x (_ ... (any_i any_v) _ ...)) _ ...) any_x any_ip any_v)])
;--------------------------------------------------------------------------------------------------------------------
(define-metafunction REDEX
    ext1 : ((any (any ...)) ...) (any any) -> ((any (any ...)) ...)
    [(ext1 (any_0 ... (any_x (any_v0 ...)) any_1 ...) (any_x any_p))
     (any_0 ... (any_x (any_p any_v0 ...)) any_1 ...)]
    [(ext1 (any_0 ...) (any_x any_p))
     ((any_x (any_p)) any_0 ...)])

(define-metafunction REDEX
    ext : ((any any) ...) (any any) ... -> ((any any) ...)
    [(ext any) any]
    [(ext any any_0 any_1 ...)
     (ext1 (ext any any_1 ...) any_0)])

 (define-metafunction REDEX
    extT1 : ((any any) ...) (any any) -> ((any any) ...)
    [(extT1 (any_0 ... (any_k any_v0) any_1 ...) (any_k any_v1))
     (any_0 ... (any_k any_v1) any_1 ...)]
    [(extT1 (any_0 ...) (any_k any_v1))
     ((any_k any_v1) any_0 ...)])

 (define-metafunction REDEX
    extT : ((any any) ...) (any any) ... -> ((any any) ...)
    [(extT any) any]
    [(extT any any_0 any_1 ...)
     (extT1 (exTt any any_1 ...) any_0)])
;--------------------------------------------------------------------------------------------------------------------
#|

(define-metafunction REDEX
    lookup1 : ((any any) ...) any -> any
    [(lookup1 (_ ... (any any_0) _ ...) any) any_0])




#|(define-metafunction REDEX
    unique : any ... -> boolean
    [(unique any_!_1 ...) #t]
    [(unique _ ...) #f])|#



(traces vρ (term (((mlet (z (→ num (→ num num))) = (λ (u_1 num) (λ (u_2 num) ((add1 3) :: num))) in 
(mlet (z (→ bool (→ bool bool))) = (λ (a_1 bool) (λ (a_2 bool) (not #t)))  in 
(mlet (y bool) = #t in 
(mlet (y num) = 1 in 
(mlet (x (→ bool bool)) = (λ (a_3 bool) (not #t)) in 
(mlet (x (→ char char)) = (λ (a_4 char) (add1 1)) in 
(mlet (t char) = 2 in 
(mlet (t bool) = #f in ((z y)(x t)))))))))) () ) bool)))

|#