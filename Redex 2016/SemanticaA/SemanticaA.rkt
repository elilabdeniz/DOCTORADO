#lang racket 
(require redex)
(require pict)
(require "subst.rkt")
;--------------------------------------------------------------------------------------------------------------------
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
  (CH ::= string)
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
;--------------------------------------------------------------------------------------------------------------------
(define-extended-language OLρ OL
  (C ::=
     W
     (M ρ)
     ;L
     ;(C :: T)
     (mlet (X) = C in C)
     (C C)
     ;(C ρ)
     ER )
    (ER ::= typeerror nameerror)
    (W ::= B N CH O (L ρ))
    ;(W ::= B N CH O (L ρ) ((λ (X) C) ρ))
    (ρ ::= ((X (W ...)) ...))
    (E ::= hole (E C) (W E)
       ;(E :: T)
       (mlet (X) = E in C)))
;--------------------------------------------------------------------------------------------------------------------
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

     ;(--> ((L ρ_1) ρ_2) (L (unirEnv ρ_1 ρ_2)) ρ-abs1)
     ;(--> (((λ (X) C) ρ_1) ρ_2) ((λ (X) C) (unirEnv ρ_1 ρ_2)) ρ-abs2)
     
     ;(--> ((C_1 C_2) ρ) ((C_1 ρ) (C_2 ρ)) ρ-Capp)
     ;(--> ((M :: T) ρ) ((M ρ) :: T) ρ-asc)
     ;(--> ((mlet (X) = C_1 in C_2) ρ) (mlet (X) = (C_1 ρ) in (C_2 ρ)) ρ-Clet)
     
     (--> (X ρ) W
          (judgment-holds (lookup2 ρ X W))
          ρ-x)

     (--> (X ρ) nameerror
          ρ-xErr
          (side-condition  (term  (predicado1 ρ X))))
     ;-------------------------------------
     (--> (((λ (X) M) ρ) W)
          (M (ext ρ (X W)))
          ;((subst (X W) M ) ρ)
          app)
     
     (--> (OB B) W_1 (judgment-holds (δB (OB B) W_1)) δB)

     (--> (ON N) W_1 (judgment-holds (δN (add1 N) W_1)) δN) 
     
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

     ;(--> (mlet (X) = W in (C  ρ))
          ;(C (ext ρ (X W)))
          ;letC)

     (--> (mlet (X) = ER in C)
          ER
          letErr1)
     
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

     (--> (W_1 W_2) typeerror
          AppErr
          (side-condition (not  (is-closure1? (term W_1))))
          (side-condition (not (is-operator? (term W_1)))))
     
     ;-------------------------------------
     ))
;--------------------------------------------------------------------------------------------------------------------
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



(define-metafunction OLρ
    [(predicado1(_ ... (any_x any_y) _ ...) any_x) #f]
    [(predicado1 any any_x) #t])


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


(define (is-closure1? t)
        (redex-match? OLρ  (L ρ) t))

;(define (is-closure2? t)
        ;(redex-match? OLρ  ((λ (X) C) ρ) t))


(define (is-operator? t)
        (redex-match? OLρ  O t))


(define (is-bool? t)
        (redex-match? OLρ  B t))

(define (is-num? t)
        (redex-match? OLρ  N t))

(define-metafunction OLρ
    [(unirEnv any ()) any]
    [(unirEnv any ((any_x any_y) any_sig ...)) (unirEnv (unirEnvAux any (any_x any_y))(any_sig ...))]
  )

(define-metafunction OLρ
    [(unirEnvAux (any_1 ... (any_x any_z) any_2 ...) (any_x any_y)) (any_1 ... (any_x (unirEnvAux2 any_z any_y)) any_2 ...)]
    [(unirEnvAux (any ...) any_1) (any_1 any ...)]
  )

(define-metafunction OLρ
    [(unirEnvAux2 any ()) any]
    [(unirEnvAux2 any (any_1 any_2 ...)) (unirEnvAux2 (unirEnvAux3 any any_1) (any_2 ...))]
  )

(define-metafunction OLρ
    [(unirEnvAux3 () any_v) (any_v)]
    [(unirEnvAux3 (any_v any_sig ...) any_v) (any_v any_sig ...)]
    [(unirEnvAux3 (any_w any_sig ...) any_v) (concat any_w (unirEnvAux3 (any_sig ...) any_v))]
  )

(define-metafunction OLρ
    [(concat any ()) (any)]
    [(concat any (any_w any_sig ...)) (any any_w any_sig ...)])

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


(apply-reduction-relation* -->vρ  (term ((mlet (z ) = (λ (u_1 )  (add1 u_1)) in 
(mlet (z ) = (λ (a_1 )  (not a_1))  in  
(mlet (x ) = (λ (a_3 ) (not #t)) in 
(mlet (x ) = (λ (a_4 ) (add1 1)) in  (z x))))) () )))

(apply-reduction-relation* -->vρ  (term
                                     (
(mlet (z) =  (λ (u_1 )  ((λ (a_5 )  a_5) u_1)) in 
(mlet (z ) = (λ (a_1 )  ((λ (a_5 )  a_5) a_1))  in  
(mlet (x ) = (λ (a_3 )  (not #t)) in 
(mlet (x ) = (λ (a_4 )  (add1 1)) in  (z x))))) () )))

(apply-reduction-relation* -->vρ  (term ((mlet (x ) = (λ (a_3 ) (not a_3)) in 
(mlet (x ) = 2 in 
(mlet (x ) = #f in (x x)))) () )))

(apply-reduction-relation* -->vρ  (term
((mlet(x ) = (λ (a_3 ) (not #t)) in 
(mlet (y ) = (λ (a_3 ) (mlet (t ) = (λ (a_5 ) (not #t)) in a_3)) in 
 (y x))) () )))

 (redex-match? OLρ  (C C) (term
 (((λ (a_5)  #t)
  ()) (((λ (a_3)  #t) ())()))))

 (redex-match? OLρ  (W C) (term
 (((λ (a_5)  #t)
  ()) (((λ (a_3)  #t) ())()))))

(render-reduction-relation	 	vρ	 
 	 	"SemanticaA.pdf"	 
 	 	#:style  'horizontal-side-conditions-same-line)

(render-language	 	OLρ	 
 	 	"SemanticaALanE.pdf"	 
 	 )
|#
