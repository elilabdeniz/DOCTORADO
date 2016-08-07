#lang racket 
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
         (mlet (X) = M in M)
         ;(mlet (X T) = M in M)
         ;(M :: T)
         ;(add1 t)
         ;(not t)
         )
  (V ::= B N CH L O) 
  (B ::= #t #f)
  (CH ::= char)
  (N ::= number)
  (L ::= (λ (X) M))
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
    (ρ ::= ((X (W ...)) ...)))
;--------------------------------------------------------------------------------------------------------------------
(define-extended-language OLρ OL⇓
    (C ::=
       W
       (M ρ)
       ;(C :: T)
       (mlet (X) = C in C)
       (C C)
       ER )
    (ER ::= typeerror)
    (E ::= hole (E C) (W E)
       ;(E :: T)
       (mlet (X) = E in C)))
;--------------------------------------------------------------------------------------------------------------------
(define vρ
    (reduction-relation
     OLρ #:domain C
     (--> (B ρ) B ρ-bool)
     (--> (N ρ) N ρ-num)
     (--> (CH ρ) CH ρ-char)
     (--> (O ρ) O ρ-op)
     ;-------------------------------------
     (--> ((M_1 M_2) ρ) ((M_1 ρ) (M_2 ρ)) ρ-app)
     ;(--> ((M :: T) ρ) ((M ρ) :: T) ρ-asc)
     (--> ((mlet (X) = M_1 in M_2) ρ) (mlet (X) = (M_1 ρ) in (M_2 ρ)) ρ-let)
     (--> (X ρ) W
          (judgment-holds (lookup2 ρ X W))
          ρ-x)
     ;-------------------------------------
     (--> (((λ (X) M) ρ) W)
          ((subst (X W) M ) ρ)
          app)
     
     (--> (OB B) W_1
          (judgment-holds (δB (OB B) W_1))
          δB)

     (--> (ON N) W_1
          (judgment-holds (δN (add1 N) W_1))
          δN)
     
     ;(--> (OB W ...) W_1
      ;    (judgment-holds (δB (OB W ...) W_1))
       ;   δB)
     
     ;(--> (ON W ...) W_1
      ;    (judgment-holds (δN (ON W ...) W_1))
       ;   δN)
     
     ;(--> (W :: T) W asc)
     
     (--> (mlet (X) = W in (M  ρ))
          (M (ext ρ (X W)))
          let)

     (--> (mlet (X) = ER in (M  ρ))
          ER
          letErro)
     
     (--> (ER C)
          ER
          AppErr1)
     
     (--> (W ER)
          ER
          AppErr2)

     (--> (OB W) typeerror
          δBErr
          (side-condition (not (is-bool? (term W)))))

     (--> (ON W) typeerror
          δNErr
          (side-condition (not (is-num? (term W)))))
     
     ;-------------------------------------
     ))
;--------------------------------------------------------------------------------------------------------------------

(define -->vρ
    (context-closure vρ OLρ E))

(define-metafunction OLρ
    injρ : M -> C
    [(injρ M) (M ())])
;--------------------------------------------------------------------------------------------------------------------
(define-judgment-form OL
    #:mode (δN I O)
    #:contract (δN (O N ...) N)
    [(δN (add1 N) ,(add1 (term N)))])

(define-judgment-form OL
    #:mode (δB I O)
    #:contract (δB (O B ...) B)
    [(δB (not B) ,(not (term B)))])
;--------------------------------------------------------------------------------------------------------------------
(define-language REDEX)

(define-judgment-form REDEX
    #:mode (lookup2 I I O)
    #:contract (lookup2 ((any any) ...) any any)
    [(lookup2(_ ... (any (_ ... any_v _ ...)) _ ...) any any_v)])
;--------------------------------------------------------------------------------------------------------------------
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

(define (is-bool? t)
        (redex-match? OLρ  B t))

(define (is-num? t)
        (redex-match? OLρ  N t))
;--------------------------------------------------------------------------------------------------------------------
#|(define-judgment-form REDEX
    #:mode (lookup I I O)
    #:contract (lookup ((any any) ...) any any)
    [(lookup (_ ... (any any_0) _ ...) any any_0)])



(define-judgment-form REDEX
    #:mode (choose I O)
    #:contract (choose (any ...) any)
    [(choose (_ ... any_v _ ...) any_v)])

(define-metafunction REDEX
    lookup1 : ((any any) ...) any -> any
    [(lookup1 (_ ... (any any_0) _ ...) any) any_0])




#|(define-metafunction REDEX
    unique : any ... -> boolean
    [(unique any_!_1 ...) #t]
    [(unique _ ...) #f])|#

(define-relation REDEX
    unique ⊆ any × ...
    [(unique any_!_1 ...)])


(apply-reduction-relation* -->vρ  (term ((mlet (z ) = (λ (u_1 ) (λ (u_2) (add1 3))) in 
(mlet (z ) = (λ (a_1 ) (λ (a_2 ) (not #t)))  in 
(mlet (y ) = #t in 
(mlet (y ) = 1 in 
(mlet (x ) = (λ (a_3 ) (not #t)) in 
(mlet (x ) = (λ (a_4 ) (add1 1)) in 
(mlet (t ) = 2 in 
(mlet (t ) = #f in ((z y)(x t)))))))))) () )))

(apply-reduction-relation* -->vρ  (term ((mlet (x ) = (λ (a_3 ) (not #t)) in 
(mlet (x ) = 2 in 
(mlet (x ) = #f in x))) () )))

(apply-reduction-relation* -->vρ  (term ((mlet (x ) = 2 in 
(mlet (x ) = #f in
      ((λ (a_3 ) x) 5))) () )))

(apply-reduction-relation*  -->vρ  (term ((mlet (x ) = 2 in 
(mlet (x ) = #f in
      (add1 x))) () )))

|#
