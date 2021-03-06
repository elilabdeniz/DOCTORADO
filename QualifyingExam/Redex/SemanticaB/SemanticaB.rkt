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
  (T fun num bool str)
  (X ::= variable-not-otherwise-mentioned))
;--------------------------------------------------------------------------------------------------------------------
(define-extended-language OL⇓ OL
    (W ::= B N CH O (L ρ))
    ;(WW :: = W (WW ρ))
    ;(MM ::=
     ;   WW
      ;  X        
       ;(MM MM)
       ;(mlet (X) = MM in MM))
       
    (ρ ::= ((X (W ...)) ...)))
;--------------------------------------------------------------------------------------------------------------------
(define-extended-language OLρ OL⇓
     (C ::=
       W
       (M ρ)
       ;L
       ;(C :: T)
       (mlet (X) = C in C)
       (C C)
       ;(C ρ)
       ER )
    (ER ::= nameerror typeerror dispatcherror)
    (E ::= hole (E C) (W E)
       ;(E :: T)
       (mlet (X) = E in C)))
;--------------------------------------------------------------------------------------------------------------------
(define-extended-language OLρT OLρ
  (Γ  ::= ((X T) ...))
  (T* ::= (T ...)))
;--------------------------------------------------------------------------------------------------------------------
(define-extended-language OLρI OLρT
    (CI ::= (C I) W)
    (I ::= (→ I I) T *))
;--------------------------------------------------------------------------------------------------------------------
(define-extended-language OLT OL
    (Γ  ::= ((X T) ...))
    (A  ::= ((X (T ...)) ...))
    (T* ::= (T ...)))
;--------------------------------------------------------------------------------------------------------------------
;--------------------------------------------------------------------------------------------------------------------
(define vρ
    (reduction-relation
     OLρT #:domain C
     (--> (B ρ) B ρ-bool)
     
     (--> (N ρ) N ρ-num)
     
     (--> (CH ρ) CH ρ-str)
     
     (--> (O ρ) O ρ-op)
     
     ;(--> (((λ (X T) M) ρ) I) ((λ (X T) M) ρ) ρ-abs)
     ;-------------------------------------
     (--> ((M_1 M_2) ρ) ((M_1 ρ) (M_2 ρ)) ρ-app)
     
     ;(--> ((M :: T) ρ) ((M ρ) :: T) ρ-asc)
     
     (--> ((mlet (X) = M_1 in M_2) ρ) (mlet (X) = (M_1 ρ) in (M_2 ρ)) ρ-let)
     
     (--> (X ρ) W
          (judgment-holds (lookup7 ρ X W))
          ρ-x
          ;(side-condition(term (construirEnvCond ρ)))
          )

     (--> (X ρ) nameerror
          ρ-xErr
          (side-condition  (term  (predicado1 ρ X))))
     ;-------------------------------------

      (--> (((λ (X) M) ρ) W)
          (M (ext ρ (X W)))
          ;((subst (X W) M ) ρ)
          app)
     
     ;(--> ((X_1 ρ_1) (X_2 ρ_2)) 
          ;(W_1 W_2)
          ;(judgment-holds (lookup3 ρ_1 X_1 W_1 T_1))
          ;(judgment-holds (lookup4 ρ_2 X_2 T_1 W_2))
          ;app11)
     
     ;(--> (((λ (X T) M) ρ) (X_2 ρ_2)) 
          ;(((λ (X T) M) ρ) W_2)
          ;(judgment-holds (lookup4 ρ_2 X_2 T W_2))
         ;app12)
     
     (--> ((X_1 ρ_1) W_2) 
          (W_1 W_2)
          (judgment-holds (lookup6 ρ_1 X_1 fun W_1))
          app13)
     
     ;(--> (OB W ...) W_1
          ;(judgment-holds (δB (OB W ...) W_1))
          ;δB)
     
     ;(--> (ON W ...) W_1
          ;(judgment-holds (δN (ON W ...) W_1))
          ;δN)

     (--> (OB (X_2 ρ_2)) W_2
         (judgment-holds (lookup6 ρ_2 X_2 bool W_1))
          (judgment-holds (δB (OB  W_1) W_2))          
          δB1)
     
     (--> (ON (X_2 ρ_2)) W_2
          (judgment-holds (lookup6 ρ_2 X_2 num W_1))
          (judgment-holds (δN (ON W_1) W_2))
          δN1)

     
     (--> (OB B) W_1
          (judgment-holds (δB (OB B) W_1))
          δB)

     (--> (ON N) W_1
          (judgment-holds (δN (ON N) W_1))
          δN)
     
     ;(--> (W :: T) W asc)
     
     ;(--> ((X ρ) :: T) W
          ;(judgment-holds (lookup4 ρ X T W))
          ;asc11)
     
     (--> (mlet (X) = W in (M  ρ))
          (M (ext ρ (X  W)))
          let
          ;(side-condition (definido? ρ))  
          ;(side-condition (not (is-value? (term M))))
          )

     ;(--> (mlet (X) = (X_1 ρ_1) in (M  ρ))
          ;(M (ext ρ (X (T W))))
          ;(judgment-holds (lookup4 ρ_1 X_1 T W))
          ;let11
          ;(side-condition (definido? ρ))  
          ;(side-condition (not (is-value? (term M))))
          ;)
     ;-------------------------------------
     (--> (mlet (X) = C_1 in C_2)
          (mlet (X) =  C_3 in C_2)
          (judgment-holds (escoger ,(apply-reduction-relation vρ (term C_1)) C_3))
          let_1
          (side-condition (not (is-value? (term C_1))))
          ;(side-condition (not (is-variable? (term (primero  C_1)))))
          (side-condition (term (novacio? ,(apply-reduction-relation vρ (term C_1))))))

     ;(--> (C :: T)
           ;(C_3 :: T)
           ;(judgment-holds (escoger ,(apply-reduction-relation vρ (term C)) C_3))
           ;asc_1
           ;(side-condition (not (is-value? (term C))))
           ;(side-condition (not (is-variable? (term (primero  C)))))
           ;(side-condition (term (novacio? ,(apply-reduction-relation vρ (term C ))))))

      (--> (C_1 C_2)
           (C_3 C_2)
           (judgment-holds (escoger ,(apply-reduction-relation vρ (term C_1)) C_3))
           app_1
           (side-condition (not (is-value? (term C_1))))
           (side-condition (not (is-variable? (term (primero  C_1)))))
           (side-condition (term (novacio? ,(apply-reduction-relation vρ (term C_1 ))))))
      
      (--> (((λ (X) M) ρ) C_2)
           (((λ (X) M) ρ) C_3)
           (judgment-holds (escoger ,(apply-reduction-relation vρ (term C_2)) C_3))
           app_2
           (side-condition (not (is-value? (term C_2))))
           ;(side-condition (not (is-variable? (term (primero C_2)))))
           (side-condition (term (novacio? ,(apply-reduction-relation vρ (term C_2 ))))))

      (--> ((X ρ) C_2)
           ((X ρ)  C_3)
           (judgment-holds (escoger ,(apply-reduction-relation vρ (term C_2)) C_3))
           app_3
           (side-condition (not (is-value? (term C_2))))
           ;(side-condition (not (is-variable?  (term (primero C_2)))))
           (side-condition (term (novacio? ,(apply-reduction-relation vρ (term C_2 ))))))

      (--> (O C_2)
           (O C_3)
           (judgment-holds (escoger ,(apply-reduction-relation vρ (term C_2)) C_3))
           app_2O
           (side-condition (not (is-value? (term C_2))))
           (side-condition (not (is-variable? (term (primero  C_2)))))
           (side-condition (term (novacio? ,(apply-reduction-relation vρ (term C_2 )))))
           )

      (--> (mlet (X) = ER in C)
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

     (--> (W_1 W_2) typeerror
          AppErr
          (side-condition (not (or (is-closure1? (term W_1)) (is-closure2? (term W_1)))))
          (side-condition (not (is-operator? (term W_1)))))


     (--> ((X_1 ρ_1) W_2) dispatcherror
          app13Err
          (side-condition  (term  (predicado ρ_1 X_1 fun))))

     (--> (OB (X_2 ρ_2)) dispatcherror          
          δB1Err
          (side-condition  (term  (predicado ρ_2 X_2 bool))))
     
     (--> (ON (X_2 ρ_2)) dispatcherror
          δN1Err
         (side-condition  (term  (predicado ρ_2 X_2 num))))


     (--> ((X_1 ρ_1) W_2) nameerror
          app13NErr
          (side-condition  (term  (predicado1 ρ_1 X_1))))

     (--> (OB (X_2 ρ_2)) nameerror          
          δB1NErr
          (side-condition  (term  (predicado1 ρ_2 X_2))))
     
     (--> (ON (X_2 ρ_2)) nameerror
          δN1NErr
         (side-condition  (term  (predicado1 ρ_2 X_2))))

     
     ;-------------------------------------
     ))
;--------------------------------------------------------------------------------------------------------------------

;--------------------------------------------------------------------------------------------------------------------
(define value? (redex-match OLρI  W))

(define (is-value? t)
        (redex-match? OLρT  W t))

(define (is-variable? t)
        (redex-match? OLρT  X t))

;--------------------------------------------------------------------------------------------------------------------
(define-metafunction OLρI
  [(tipoConf (C I)) I]
  [(tipoConf any) any])

(define-metafunction OLρT
  [(configuration ((C I))) C]
  [(configuration (any)) any])

(define-metafunction OLρI
  [(configuration1 (C ρ)) C]
  [(configuration1 any) any])

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

(define-metafunction OLT
  [(minsel ((→ T_1 T_2) any ...) (any_3 ... T_1 any_4 ...) (any_0 ... (→ T_1 T_2) any_1 ...))
   ,(if (term (propiedad (→ T_1 T_2) (any_0 ... any_1 ...) (any_3 ... T_1 any_4 ...)))
        (term (concat (→ T_1 T_2) (minsel (any ...) (any_3 ... T_1 any_4 ...) (any_0 ... (→ T_1 T_2) any_1 ...))))
        (term (minsel (any ...) (any_3 ... T_1 any_4 ...) (any_0 ... (→ T_1 T_2) any_1 ...))))]
  [(minsel ((→ T_1 T_2) any ...) any_2 any_1) (minsel (any ...) any_2 any_1)]
  [(minsel (any_0 any_1 ...) any_3 any_2) (minsel (any_1 ...) any_3 any_2)]
  [(minsel () any_2 any_1) ()])

(define-metafunction OLT
  [(propiedad (→ T_1 T_2) any_1 any_2) ,(not (term (isin? T_2 (codominio any_1))))])

(define-metafunction OLT
  [(distribuir T_1 ()) ()]
   [(distribuir T_1 (T_2 T_3 ...)) (concat (→ T_1 T_2) (distribuir T_1 (T_3 ...)))])

(define-metafunction OLρI
  [(consistentType? T T) #t]
  [(consistentType? T *) #t]
  [(consistentType? (→ T_1 T_2) (→ I_1 I_2)) ,(and (term (consistentType? T_1 I_1)) (term (consistentType? T_2 I_2)))]
  ;[(consistentType? T I) #f]
  [(consistentType? any_0 any_1) #f])

(define-metafunction OLT
  [(esta? (_ ... T _ ...) T) #t]
  [(esta? T* T) #f])



(define-metafunction OLρT
    [(predicado1(_ ... (any_x any_y) _ ...) any_x) #f]
    [(predicado1 any any_x) #t])

#|(define-metafunction OLρT
  [(construirEnvCond ((X ((T W) ...)) any_0 ...)) ,(and (term (construirEnvAuxCond ((T W) ...)))
                                                      (term (construirEnvCond (any_0 ...))) (term (noisin? X (sacar (any_0 ...)))))]
  [(construirEnvCond ()) #t])

(define-metafunction OLρT
  [(construirEnvAuxCond  ((T W) any_0 ...)) ,(and   (judgment-holds (types () W : (_ ... T_1 _ ...))) (term (esta?  ,(first (ObtTypes (term W))) T))
                                                      (term (construirEnvAuxCond (any_0 ...))) (term (noisin? T (sacar (any_0 ...)) )))]
  [(construirEnvAuxCond ()) #t])

;(define-metafunction OLρT
  ;[(construirEnvAuxCond  ((T W) any_0 ...)) ,(and  (term (esta?  ,(first (ObtTypes (term W))) T))
                                                      ;(term (construirEnvAuxCond (any_0 ...))) (term (noisin? T (sacar (any_0 ...)) )))]
  ;[(construirEnvAuxCond ()) #t])


;(define-metafunction OLρT
  ;[(construirEnvAuxCond  ((T W) any_0 ...)) ,(and   (judgment-holds (types () W : (_ ... T _ ...)))
                                                      ;(term (construirEnvAuxCond (any_0 ...))) (term (noisin? T (sacar (any_0 ...)) )))]
  ;[(construirEnvAuxCond ()) #t])

(define-metafunction OLρT
  [(construirEnv ((X ((T W) ...)) any_0 ...)) (concat (X (construirEnvAux ((T W) ...)))
                                                      (construirEnv (any_0 ...)))]
  [(construirEnv ()) ()])

(define-metafunction OLρT
  [(construirEnvAux  ((T W) any_0 ...)) (concat  T
                                                      (construirEnvAux (any_0 ...)))]
  [(construirEnvAux ()) ()])|#


#|(define-metafunction OLρT
  [(construirEnv ((X ((T W) ...)) any_0 ...)) (concat (X (construirEnvAux ((T W) ...)))
                                                      (construirEnv (any_0 ...)))]
  [(construirEnv ()) ()])  

(define-metafunction OLρT
  [(construirEnvAux  ((T W) any_0 ...)) (concat  ,(first(first (judgment-holds (types () W : (T)) (T))))
                                                      (construirEnvAux (any_0 ...)))]
  [(construirEnvAux ()) ()])|#

(define-metafunction OLT
  [(codominio ()) ()]
  [(codominio ((→ T_1 T_2) any ...)) (concat T_2 (codominio (any ...)))]
  [(codominio (any_1 any ...))  (codominio (any ...))])

(define-metafunction OLρT
    [(tagi B) bool]
    [(tagi N) num]
    [(tagi CH) str]
    [(tagi add1) fun]
    [(tagi not) fun]
    [(tagi W) fun]
  )
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
    #:mode (escoger I O)
    #:contract (escoger (any ...) any)
    [(escoger (_ ... any_0 _ ...) any_0)])


(define-judgment-form REDEX
    #:mode (lookup2 I I O)
    #:contract (lookup2 ((any any) ...) any any)
    [(lookup2(_ ... (any (_ ... (any_t any_v) _ ...)) _ ...) any any_v)])

(define-judgment-form REDEX
    #:mode (lookup3 I I O O)
    #:contract (lookup3 ((any any) ...) any any any)
    [(lookup3(_ ... (any (_ ... ((→ any_t1 any_t2) any_v) _ ...)) _ ...) any any_v any_t1)])

(define-judgment-form REDEX
    #:mode (lookup4 I I I O)
    #:contract (lookup4 ((any any) ...) any any any)
    [
     (lookup4(_ ... (any_x (_ ... (any_i any_v) _ ...)) _ ...) any_x any_i any_v)])


(define-judgment-form REDEX
    #:mode (iguales I I)
    #:contract (iguales any any)
    [(iguales num num)]
    [(iguales bool bool)]
    [(iguales str str)]
    [(iguales fun fun)])

(define-judgment-form REDEX
    #:mode (lookup6 I I I O)
    #:contract (lookup6 ((any any) ...) any any any)
    [
     ;(side-condition (noisin? X (sacar Γ)))
     (iguales (tagi any_v) any_s)
     ------------------------------------------------------------------------
     (lookup6(_ ... (any_x (_ ...  any_v _ ...)) _ ...) any_x any_s any_v)])

(define-judgment-form REDEX
    #:mode (lookup5 I I O)
    #:contract (lookup5 ((any any) ...) any any)
    [(lookup5 (_ ... (any (_ ... ((→ any_t1 any_t2) any_v) _ ...)) _ ...) any any_v)])


(define-judgment-form REDEX
    #:mode (lookup7 I I O)
    #:contract (lookup7 ((any any) ...) any any)
    [(lookup7 (_ ... (any_x (_ ...  any_v _ ...)) _ ...) any_x any_v)])


(define-metafunction REDEX
    concat : any (any ...) -> (any ...)
    [(concat any_0 (any_1 ...)) (any_0 any_1 ...)])

(define-metafunction REDEX
    ;isin? : any (any ...) -> bool
    [(isin? any_0 (_ ... any_0 _ ...)) #t]
    [(isin? any_0 any_1) #f])

(define-metafunction REDEX
    ;isin? : any (any ...) -> bool
    [(noisin? any_0 (_ ... any_0 _ ...)) #f]
    [(noisin? any_0 any_1) #t])

(define-metafunction REDEX
    ;isin? : any (any ...) -> bool
    [(novacio? ()) #f]
    [(novacio? (any_0 any_1 ...)) #t])

(define-metafunction REDEX
    ;isin? : any (any ...) -> bool
    [(cantidad ()) 0]
    [(cantidad (any_0 any_1 ...)) ,(+ 1 (term (cantidad (any_1 ...))))])

(define-metafunction REDEX
  [(primero (any_1 any_2)) any_1]
  [(primero any) any])
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
    [(definido? ()) #t]
    [(definido? ((any_x any_y) any_0 ...)) ,(and (term (noisin? any_x (sacar (any_0 ...)) )) (term (definido? (any_0 ...))))])

(define-metafunction REDEX
    [(sacar ()) ()]
    [(sacar ((any_x any_y) any_0 ...)) (concat any_x (sacar  (any_0 ...)))])

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
     (extT1 (extT any any_1 ...) any_0)])

(define (is-bool? t)
        (redex-match? OLρ  B t))

(define (is-num? t)
        (redex-match? OLρ  N t))

(define (is-operator? t)
        (redex-match? OLρ  O t))

(define (is-closure1? t)
        (redex-match? OLρ  (L ρ) t))

(define (is-closure2? t)
        (redex-match? OLρ  ((λ (X) C) ρ) t))

(define-metafunction OLρT
    [(predicado(_ ... (any_x ()) _ ...) any_x any_s) #t]
    [(predicado(_ ... (any_x (any_v any_v1  ...)) _ ...) any_x any_s) ,(if (term (igtag(tagi any_v) any_s))
                                                                     #f
                                                                     (term (predicado((any_x (any_v1  ...))) any_x any_s)))]
    [(predicado any any_x any_s) #f] )

(define-metafunction OLρT
    [(igtag T T) #t]
    [(igtag T_1 T_2) #f]
  )
;--------------------------------------------------------------------------------------------------------------------
#|(define (types? C)
  (judgment-holds (types () ,C : (T))))

(define (ObtTypes C)
  (judgment-holds (types () ,C : T*) T*))
 
(define w? (redex-match OLρI W))

(define (reduces? CI)
  (not (null? (apply-reduction-relation
               vρ
               (term ,CI)))))

(define (progress-holds? CI)
  (define C  (term (configuration1 ,CI)))
  (define I  (term (tipoConf ,CI)))
  (if (types? C)
      (let ((T_1 (first(first (ObtTypes C)))))
            (if (or  (term (consistentType?  ,T_1  ,I)) (equal?  I CI)) 
                 (or (w? C)
          (reduces? (term (,C ,T_1))))
          #t))
      #t)) |#


#|
(apply-reduction-relation* vρ  (term ((mlet (x ) = (λ (a3 ) (not #t)) in 
(mlet (x ) = 2 in 
(mlet (x ) = #f in (not x)))) () )))


(apply-reduction-relation* vρ  (term ((mlet (x ) = (λ (a_3 ) (not #t)) in 
(mlet (x ) = 2 in 
(mlet (x ) = #f in x))) () )))

(apply-reduction-relation* vρ  (term ((mlet (z ) = (λ (u_1 ) (λ (u_2) (add1 3))) in 
(mlet (z ) = (λ (a_1 ) (λ (a_2 ) (not #t)))  in 
(mlet (y ) = #t in 
(mlet (y ) = 1 in 
(mlet (x ) = (λ (a_3 ) (not #t)) in 
(mlet (x ) = (λ (a_4 ) (add1 1)) in 
(mlet (t ) = 2 in 
(mlet (t ) = #f in ((z y)(x t)))))))))) () )))

(apply-reduction-relation* vρ  (term ((mlet (x ) = 2 in 
(mlet (x ) = #f in
      ((λ (a_3 ) x) 5))) () )))

(apply-reduction-relation* vρ  (term ((mlet (x ) = (λ (a3 ) (not #t)) in 
(mlet (x ) = #f in (add1 x))) () )))

(apply-reduction-relation* vρ  (term ((mlet (z ) = (λ (u_1 )  (add1 u_1)) in 
(mlet (z ) = (λ (a_1 )  (not a_1))  in  
(mlet (x ) = (λ (a_3 ) (not #t)) in 
(mlet (x ) = (λ (a_4 ) (add1 1)) in  (z x))))) () )))




(apply-reduction-relation* vρ  (term ((mlet (z ) = (λ (u_1 ) (λ (u_2) (add1 3))) in 
(mlet (z ) = (λ (a_1 ) (λ (a_2 ) (not #t)))  in 
(mlet (y ) = #t in 
(mlet (y ) = 1 in 
(mlet (x ) = (λ (a_3 ) (not #t)) in 
(mlet (x ) = (λ (a_4 ) (add1 1)) in 
(mlet (t ) = 2 in 
(mlet (t ) = #f in ((z y)(x t)))))))))) () )))

(apply-reduction-relation* vρ  (term ((mlet (x ) = (λ (a_3 ) (not #t)) in 
(mlet (x ) = 2 in 
(mlet (x ) = #f in x))) () )))

(apply-reduction-relation* vρ  (term ((mlet (x ) = 2 in 
(mlet (x ) = #f in
      ((λ (a_3 ) x) 5))) () )))

(apply-reduction-relation*  vρ  (term ((mlet (x ) = 2 in 
(mlet (x ) = #f in
      (add1 x))) () )))


(apply-reduction-relation* vρ  (term ((mlet (z ) = (λ (u_1 )  (add1 u_1)) in 
(mlet (z ) = (λ (a_1 )  (not a_1))  in  
(mlet (x ) = (λ (a_3 ) (not #t)) in 
(mlet (x ) = (λ (a_4 ) (add1 1)) in  (z x))))) () )))

(apply-reduction-relation* vρ  (term
                                     (
(mlet (z) =  (λ (u_1 )  ((λ (a_5 )  a_5) u_1)) in 
(mlet (z ) = (λ (a_1 )  ((λ (a_5 )  a_5) a_1))  in  
(mlet (x ) = (λ (a_3 )  (not #t)) in 
(mlet (x ) = (λ (a_4 )  (add1 1)) in  (z x))))) () )))

(apply-reduction-relation* vρ  (term ((mlet (x ) = (λ (a_3 ) (not a_3)) in 
(mlet (x ) = 2 in 
(mlet (x ) = #f in (x x)))) () )))

(apply-reduction-relation* vρ  (term
((mlet(x ) = (λ (a_3 ) (not #t)) in 
(mlet (y ) = (λ (a_3 ) (mlet (t ) = (λ (a_5 ) (not #t)) in a_3)) in 
 (y x))) () )))


(render-reduction-relation	 	vρ	 
 	 	"SemanticaB3.pdf"	 
 	 	#:style  'compact-vertical)

(render-language	 	OLρ	 
 	 	"SemanticaALanE.pdf"	 
 	 )
|#


;--------------------------------------------------------------------------------------------------------------------
(test-->>
   vρ
   (term ((mlet (z ) = (λ (u_1 ) (λ (u_2) (add1 3))) in 
(mlet (z ) = (λ (a_1 ) (λ (a_2 ) (not #t)))  in 
(mlet (y ) = #t in 
(mlet (y ) = 1 in 
(mlet (x ) = (λ (a_3 ) (not #t)) in 
(mlet (x ) = (λ (a_4 ) (add1 1)) in 
(mlet (t ) = 2 in 
(mlet (t ) = #f in ((z y)(x t)))))))))) () ))
    (term #f)(term 4))
;-------------------------------------------------------------------------------------------------------------------

(test-->>
   vρ
  (term ((mlet (x ) = (λ (a_3 ) (not #t)) in 
(mlet (x ) = 2 in 
(mlet (x ) = #f in x))) () ))
  (term #f)
  (term ((λ (a_3) (not #t)) ()))
  (term 2))
;-------------------------------------------------------------------------------------------------------------------
(test-->>
   vρ

   (term ((mlet (x ) = 2 in 
(mlet (x ) = #f in
      ((λ (a_3 ) x) 5))) () ))
   (term #f)
   (term 2)
  )
;-------------------------------------------------------------------------------------------------------------------
  (test-->>
   vρ (term ((mlet (x ) = 2 in 
(mlet (x ) = #f in
      (add1 x))) () ))
(term 3)
  )

;-------------------------------------------------------------------------------------------------------------------

(test-->>
   vρ

   (term ((mlet (z ) = (λ (u_1 )  (add1 u_1)) in 
(mlet (z ) = (λ (a_1 )  (not a_1))  in  
(mlet (x ) = (λ (a_3 ) (not #t)) in 
(mlet (x ) = (λ (a_4 ) (add1 1)) in  (z x))))) () ))
   (term dispatcherror)
  )
;-------------------------------------------------------------------------------------------------------------------
(test-->>
   vρ

   (term
                                     (
(mlet (z) =  (λ (u_1 )  ((λ (a_5 )  a_5) u_1)) in 
(mlet (z ) = (λ (a_1 )  ((λ (a_5 )  a_5) a_1))  in  
(mlet (x ) = (λ (a_3 )  (not #t)) in 
(mlet (x ) = (λ (a_4 )  (add1 1)) in  (z x))))) () ))

   (term ((λ (a_3) (not #t))
   ((z
     (((λ (a_1) ((λ (a_5) a_5) a_1)) ((z (((λ (u_1) ((λ (a_5) a_5) u_1)) ())))))
      ((λ (u_1) ((λ (a_5) a_5) u_1)) ()))))))
   (term ((λ (a_4) (add1 1))
   ((x
     (((λ (a_3) (not #t))
       ((z
         (((λ (a_1) ((λ (a_5) a_5) a_1)) ((z (((λ (u_1) ((λ (a_5) a_5) u_1)) ())))))
          ((λ (u_1) ((λ (a_5) a_5) u_1)) ())))))))
    (z
     (((λ (a_1) ((λ (a_5) a_5) a_1)) ((z (((λ (u_1) ((λ (a_5) a_5) u_1)) ())))))
      ((λ (u_1) ((λ (a_5) a_5) u_1)) ())))))))
;-------------------------------------------------------------------------------------------------------------------


(test-->>
   vρ

   (term
((mlet(x ) = (λ (a_3 ) (not #t)) in 
(mlet (y ) = (λ (a_3 ) (mlet (t ) = (λ (a_5 ) (not #t)) in a_3)) in 
 (y x))) () ))
   (term ((λ (a_3) (not #t)) ())))

;-------------------------------------------------------------------------------------------------------------------
(test-->>
   vρ
   (term ((mlet (x ) = (λ (a3 ) (not #t)) in 
(mlet (x ) = 2 in 
(mlet (x ) = #f in (not x)))) () ))
   (term #t))

;-------------------------------------------------------------------------------------------------------------------
(test-->>
   vρ
    (term ((mlet (x ) = 2 in 
(mlet (x ) = #f in
      (add1 x))) () ))
   (term 3))

;-------------------------------------------------------------------------------------------------------------------
(test-->>
   vρ
   (term ((mlet (x ) = (λ (a_3 ) (not a_3)) in 
(mlet (x ) = 2 in 
(mlet (x ) = #f in (x x)))) () ))
   (term #t)
   (term dispatcherror))

;-------------------------------------------------------------------------------------------------------------------
