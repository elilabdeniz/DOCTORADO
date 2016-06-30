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
  (CH ::= string)
  (N ::= number)
  (L ::= (λ (X T) M))
  (O ::= OB ON)
  (OB ::= OB1)
  (ON ::= ON1)
  (OB1 ::= not)
  (ON1 ::= add1)
  (T (→ T T) num bool str)
  (X ::= variable-not-otherwise-mentioned))
;--------------------------------------------------------------------------------------------------------------------
(define-extended-language OL⇓ OL
    (W ::= B N CH O (L ρ))
    (ρ ::= ((X ((T_1 W_1) (T_2 W_2)...)) ...)))
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
(define-judgment-form OLT
    #:mode (⊢ I I I I O)
    #:contract (⊢ A Γ M : T*)
    [(lookup Γ X T)
     -------------- var_1
     (⊢ A Γ X : (T))]

    [(lookup A X T*)
     -------------- var_2
     (⊢ A Γ X : T*)]
  
    [------------- num
     (⊢ A Γ N : (num))]
  
    [------------- bool
     (⊢ A Γ B : (bool))]
  
    [----------------------- str
     (⊢ A Γ CH : (str))]

   [----------------------- opB1
     (⊢ A Γ OB1 : ((→ bool bool)))]
  
    [--------------------------- opN1
     (⊢ A Γ ON1 : ((→ num num)))]
  
    [(⊢ A Γ M_1 : T*_1)
     (⊢ A Γ M_2 : T*_2)
     (side-condition (novacio? (codominio (minsel T*_1 T*_2 T*_1))))
     -------------------------------------------------------------- app
     (⊢ A Γ (M_1 M_2) :  (codominio (minsel T*_1 T*_2 T*_1)))]

    [(⊢ A Γ M : T*)
    (side-condition (esta? T* T))
    ----------------------- asc
    (⊢ A Γ (M :: T) : (T))]

     [(⊢ A Γ M_1 : T*_1)
     (side-condition (esta? T*_1 T_1))
     (side-condition (definido? A))
     (⊢ (ext A (X T_1)) Γ M_2 : T*_2)
     --------------------------------------- let
     (⊢ A Γ (mlet (X T_1) = M_1 in M_2) : T*_2)]
  
    [(unique X)
     (side-condition (definido? Γ))
     (⊢ A (extT Γ (X T)) M : T*)
     (side-condition (novacio? T*))
     ------------------------------------------ λ
     (⊢ A Γ (λ (X T) M) : (distribuir T T*))])
;--------------------------------------------------------------------------------------------------------------------
(define vρ
    (reduction-relation
     OLρI #:domain CI
     (--> ((B ρ) I) B ρ-bool)
     (--> ((N ρ) I) N ρ-num)
     (--> ((CH ρ) I) CH ρ-str)
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
          ;(side-condition (definido? ρ))
          ;(side-condition (not (is-value? (term M))))
          )
     ;-------------------------------------
     (--> ((mlet (X T) = C_1 in C_2) I)
          ((mlet (X T) =  (configuration ,(apply-reduction-relation vρ (term (C_1 T)))) in C_2) I)
          let_1
          (side-condition (not (is-value? (term C_1))))
          (side-condition (term (novacio? ,(apply-reduction-relation vρ (term (C_1 T)))))))
      (--> ((C :: T) T)
           (((configuration ,(apply-reduction-relation vρ (term (C T)))) :: T) T)
           asc_1
           (side-condition (not (is-value? (term C))))
           (side-condition (term (novacio? ,(apply-reduction-relation vρ (term (C T)))))))
      (--> ((C_1 C_2) I)
           (((configuration ,(apply-reduction-relation vρ (term (C_1 (→ * I))))) C_2) I)
           app_1
           (side-condition (not (is-value? (term C_1))))
           (side-condition (term (novacio? ,(apply-reduction-relation vρ (term (C_1 (→ * I))))))))
      
      (--> ((((λ (X T) M) ρ) C_2) I)
           ((((λ (X T) M) ρ) (configuration ,(apply-reduction-relation vρ (term (C_2 T))))) I)
           app_2
           (side-condition (not (is-value? (term C_2))))
           (side-condition (term (novacio? ,(apply-reduction-relation vρ (term (C_2 T)))))))

      (--> ((O C_2) I)
           ((O (configuration ,(apply-reduction-relation vρ (term (C_2 (typi O)))))) I)
           app_2O
           (side-condition (not (is-value? (term C_2))))
           (side-condition (term (novacio? ,(apply-reduction-relation vρ (term (C_2 (typi O))))))))
     ;-------------------------------------
     ))
;--------------------------------------------------------------------------------------------------------------------
(define-judgment-form OLρT
    #:mode (types I I I O)
    #:contract (types Γ C : T*)
    [(lookup Γ X T)
     -------------------------- var_1
     (types Γ (X ρ) : (T))]

    [(side-condition (construirEnvCond ρ))
     (lookup (construirEnv ρ) X T*)
     (side-condition (novacio? T*))
     -------------------------- var_2
     (types Γ (X ρ) : T*)]
  
    [------------- num
     (types Γ N : (num))]
  
    [------------- bool
     (types Γ B : (bool))]
  
    [----------------------- str
     (types Γ CH : (str))]
    
    [------------- c-num
     (types Γ (N ρ) : (num))]
  
    [------------- c-bool
     (types Γ (B ρ) : (bool))]
  
    [----------------------- c-str
     (types Γ (CH ρ) : (str))]
  
    [----------------------- opB1
     (types Γ OB1 : ((→ bool bool)))]
  
    [--------------------------- opN1
     (types Γ ON1 : ((→ num num)))]

    [----------------------- c-opB1
     (types Γ (OB1 ρ) : ((→ bool bool)))]
  
    [--------------------------- c-opN1
     (types Γ (ON1 ρ) : ((→ num num)))]
  
    [(types Γ ((M_1 ρ) (M_2 ρ)) : T*)
     -------------------------------- app
     (types Γ ((M_1 M_2)  ρ) : T*)]

    [(types Γ C_1 : T*_1)
     (types Γ C_2 : T*_2)
     (side-condition (novacio? (codominio (minsel T*_1 T*_2 T*_1))))
     --------------------------------------------------------------- c-app
     (types Γ (C_1 C_2) : (codominio (minsel T*_1 T*_2 T*_1)))]

    [(types Γ (M ρ) : T*)
    (side-condition (esta? T* T))
    ----------------------- asc
    (types Γ ((M :: T) ρ) : (T))]

    [(types Γ C : T*)
    (side-condition (esta? T* T))
    ----------------------- c-asc
    (types Γ (C :: T) : (T))]

    [(types Γ (mlet (X T_1) = (M_1 ρ) in (M_2 ρ)) : T*)
    ----------------------------------------------------- let
    (types Γ ((mlet (X T_1) = M_1 in M_2) ρ) : T*)]

    [(types Γ C_1 : T*_1)
     (side-condition (esta? T*_1 T_1))
     (side-condition (construirEnvCond ρ))
     (side-condition (definido? ρ))
     (⊢ (ext (construirEnv ρ) (X T_1)) Γ M_2 : T*_2)     
    ------------------------------------------------------ c-let
    (types Γ (mlet (X T_1) = C_1 in (M_2 ρ)) : T*_2)]
  
    [(unique X)
     (side-condition (construirEnvCond ρ))
     (side-condition (definido? Γ))
     (⊢ (construirEnv ρ) (extT Γ (X T)) M : T*)
     (side-condition (novacio? T*))
     ------------------------------------------ λ
     (types Γ ((λ (X T) M) ρ) : (distribuir T T*))])
;--------------------------------------------------------------------------------------------------------------------
(define value? (redex-match OLρI  W))

(define (is-value? t)
        (redex-match? OLρI  W t))
;--------------------------------------------------------------------------------------------------------------------
(define-metafunction OLρI
  [(tipoConf (C I)) I]
  [(tipoConf any) any])

(define-metafunction OLρI
  [(configuration ((C I))) C]
  [(configuration (any)) any])

(define-metafunction OLρI
  [(configuration1 (C I)) C]
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
  [(construirEnvCond ((X ((T W) ...)) any_0 ...)) ,(and (term (construirEnvAuxCond ((T W) ...)))
                                                      (term (construirEnvCond (any_0 ...))))]
  [(construirEnvCond ()) #t])

(define-metafunction OLρT
  [(construirEnvAuxCond  ((T W) any_0 ...)) ,(and  (judgment-holds (types () W : (_ ... T _ ...))) 
                                                      (term (construirEnvAuxCond (any_0 ...))))]
  [(construirEnvAuxCond ()) #t])

(define-metafunction OLρT
  [(construirEnv ((X ((T W) ...)) any_0 ...)) (concat (X (construirEnvAux ((T W) ...)))
                                                      (construirEnv (any_0 ...)))]
  [(construirEnv ()) ()])

(define-metafunction OLρT
  [(construirEnvAux  ((T W) any_0 ...)) (concat  T
                                                      (construirEnvAux (any_0 ...)))]
  [(construirEnvAux ()) ()])


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
;--------------------------------------------------------------------------------------------------------------------
(define (types? C)
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
      #t))


#|
(define (progress-holds? CI)
  (define C  (term (configuration1 ,CI)))
  (define I  (term (tipoConf ,CI)))
  (define T (ObtTypes C))
  (if (and (types? C) (or (term (consistentType? (first(first T)) ,I)) (equal?  I CI)) )
      (or (is-value? C)
          (reduces? (C (first (first T)))))
      #t))


(traces vρ (term (((mlet (z (→ num (→ num num))) = (λ (u_1 num) (λ (u_2 num) ((add1 3) :: num))) in 
(mlet (z (→ bool (→ bool bool))) = (λ (a_1 bool) (λ (a_2 bool) (not #t)))  in 
(mlet (y bool) = #t in 
(mlet (y num) = 1 in 
(mlet (x (→ bool bool)) = (λ (a_3 bool) (not #t)) in 
(mlet (x (→ str str)) = (λ (a_4 str) (add1 1)) in 
(mlet (t str) = 2 in 
(mlet (t bool) = #f in ((z y)(x t)))))))))) () ) bool)))




(judgment-holds (⊢ () () (mlet (z (→ num (→ num num))) = (λ (u1 num) (λ (u2 num) ((add1 3) :: num))) in 
(mlet (z (→ bool (→ bool bool))) = (λ (a1 bool) (λ (a2 bool) (not #t)))  in 
(mlet (y bool) = #t in 
(mlet (y num) = 1 in 
(mlet (x (→ bool bool)) = (λ (a3 bool) (not #t)) in 
(mlet (x (→ str str)) = (λ (a4 str) "abcd") in 
(mlet (t str) = "abc" in 
(mlet (t bool) = #f in ((z y)(x t)))))))))) : T*) T*)

(judgment-holds (⊢ () () (mlet (x (→ bool bool)) = (λ (a3 bool) (not #t)) in
                                 (mlet (x (→ num bool)) = (λ (a3 num) (not #f)) in
                                 (mlet (y num) = 5 in (x y)
                                 ))) : T*) T*)

|#