#lang racket 
(require redex)
(require pict)
(require "subst.rkt")
;Agregar regla para los multivalores en el typing de las configuraciones.
;--------------------------------------------------------------------------------------------------------------------
(define-language OL
  (M ::= NV
         V)
  (NV ::=
         X
         (M M)
         (mlet (X) = M in M)
         (M :: T)
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
;--------------------------------------------------------------------------------------------------------------------
(define-extended-language OLρ OL
     (C ::=
       W
       (M ρ)
       (C :: T)
       (mlet (X) = C in C)
       (C C)
       ER )
  (WWW ::= (mv WW) WW)
  (WW ::= B N CH O (L ρ))
    (W ::= WW (mv WW WW_1 ...))
    (ER ::= nameerror typeerror dispatcherror ambiguityerror)
    (ρ ::= ((X W) ...))
    (E ::= hole (E C) (W E)
       (E :: T)
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
  
    [
     
     (⊢ A Γ M_1 : T*_1)
     (⊢ A Γ M_2 : T*_2)
     (side-condition ,(equal? (term (cantidad (codominio (minsel T*_1 T*_2 T*_1)))) 1))
     -------------------------------------------------------------- app
     (⊢ A Γ (M_1 M_2) :  (codominio (minsel T*_1 T*_2 T*_1)))]

    [(⊢ A Γ M : T*)
    (side-condition (esta? T* T))
    ----------------------- asc
    (⊢ A Γ (M :: T) : (T))]

     [;(⊢ A Γ M_1 : (T_1))
     ;(side-condition (esta? T*_1 T_1))
     (side-condition (definido? A))
     (side-condition (noisin? X (sacar Γ)))
     ;(⊢ (ext A (X T_1)) Γ M_2 : T*_2)
     (⊢ A Γ M_1 : T*_1)
     (side-condition (sinElemRep  (extraerVar (extmult A (X T*_1)) X)))
     (⊢ (extmult A (X T*_1)) Γ M_2 : T*_2)
     --------------------------------------- let
     (⊢ A Γ (mlet (X) = M_1 in M_2) : T*_2)]
  
    [(unique X)
     (side-condition (definido? Γ))
     (⊢ A (extT Γ (X T_1)) M : T*)
     (side-condition (noisin? X (sacar Γ)))
     (side-condition (noisin? X (sacar A)))
     ;(side-condition (is-typefunc? (term T)))
     (side-condition (novacio? T*))
     (side-condition (esta? T* T_2))
     ------------------------------------------ λ
     (⊢ A Γ (λ (X (→ T_1 T_2)) M) : ((→ T_1 T_2)))])
;--------------------------------------------------------------------------------------------------------------------
(define vρ
    (reduction-relation
     OLρT #:domain C
     ;(--> (WW) WW value)
     
     (--> (B ρ) B ρ-bool)
     
     (--> (N ρ) N ρ-num)
     
     (--> (CH ρ) CH ρ-str)
     
     (--> (O ρ) O ρ-op)

     (--> ((mv WW ...) ρ) (mv WW ...) ρ-mvalue)
     
     ;(--> (((λ (X T) M) ρ) I) ((λ (X T) M) ρ) ρ-abs)
     ;-------------------------------------
     (--> ((M_1 M_2) ρ) ((M_1 ρ) (M_2 ρ)) ρ-app)
     
     (--> ((M :: T) ρ) ((M ρ) :: T) ρ-asc)
     
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
      (--> (((λ (X T) M) ρ) W)
          ((M (extEL ρ (X W))) :: (cod T))
          app)

      
     (--> ((mv WW_1 ...) W_2)
          (matchear (sel (mv WW_1 ...) W_2))
          appF
          (side-condition (equal? (term (cantidad (sel (mv WW_1 ...) W_2))) 1)))

     
     (--> (OB W) (aplicar (filter W bool) OB)
          δB
          (side-condition (equal? (term (cantidad (filter W bool))) 2)))

     (--> (ON W) (aplicar (filter W num) ON)
          δN
          (side-condition (equal? (term (cantidad (filter W num))) 2)))
     
     (--> (W :: T) (filter W T) asc
          (side-condition (equal? (term (cantidad (filter W T))) 2)))
     
     (--> (mlet (X) = W in (M  ρ))
          (M (extE ρ (X  W)))
          let
          ;(side-condition (definido? ρ))  
          ;(side-condition (not (is-value? (term M))))
          )
     ;-------------------------------------
     (--> (mlet (X) = C_1 in C_2)
          (mlet (X) =  C_3 in C_2)
          (judgment-holds (escoger ,(apply-reduction-relation vρ (term C_1)) C_3))
          let_1
          (side-condition (not (is-value? (term C_1))))
          ;(side-condition (not (is-variable? (term (primero  C_1)))))
          (side-condition (term (novacio? ,(apply-reduction-relation vρ (term C_1))))))

     (--> (C :: T)
           (C_3 :: T)
           (judgment-holds (escoger ,(apply-reduction-relation vρ (term C)) C_3))
           asc_1
           (side-condition (not (is-value? (term C))))
           ;(side-condition (not (is-variable? (term (primero  C)))))
           (side-condition (term (novacio? ,(apply-reduction-relation vρ (term C ))))))

      (--> (C_1 C_2)
           (C_3 C_2)
           (judgment-holds (escoger ,(apply-reduction-relation vρ (term C_1)) C_3))
           app_1
           (side-condition (not (is-value? (term C_1))))
           ;(side-condition (not (is-variable? (term (primero  C_1)))))
           (side-condition (term (novacio? ,(apply-reduction-relation vρ (term C_1 ))))))

      (--> (W_1 C_2)
           (W_1 C_3)
           (judgment-holds (escoger ,(apply-reduction-relation vρ (term C_2)) C_3))
           app_2
           (side-condition (not (is-value? (term C_2))))
           ;(side-condition (not (is-variable? (term (primero C_2)))))
           (side-condition (term (novacio? ,(apply-reduction-relation vρ (term C_2 ))))))
           ;)
      ;-------------------------------------
      (--> (mlet (X) = ER in C)
          ER
          letErro)
     
     (--> (ER C)
          ER
          AppErr1)
     
     (--> (W ER)
          ER
          AppErr2)
     
     (--> (ER :: T) ER
          AscErr)
     ;-------------------------------------
     (--> (OB WW) typeerror
          δBErr
          (side-condition (not (is-bool? (term WW)))))

     (--> (ON WW) typeerror
          δNErr
          (side-condition (not (is-num? (term WW)))))

     (--> (WW_1 W_2) typeerror
          AppErr
          (side-condition (not  (is-closure1? (term WW_1)) ))
          (side-condition (not (is-operator? (term WW_1)))))
     
     (--> (WW :: T) typeerror
          ascErrT
          (side-condition (not(equal? (term (tagi WW)) (term T)))))

     ;-------------------------------------
     (--> ((mv WW_1 ...) W_2)
          dispatcherror
          appErrD
          (side-condition (equal? (term (cantidad (sel (mv WW_1 ...) W_2))) 0)))

     
     (--> (OB (mv WW ...)) dispatcherror
          δBErrD
          (side-condition (equal? (term (cantidad (filter (mv WW ...) bool))) 1)))

     (--> (ON (mv WW ...)) dispatcherror
          δNErrD
          (side-condition (equal? (term (cantidad (filter (mv WW ...) num))) 1)))
     
    
      (--> ((mv WW ...) :: T) dispatcherror
          AscErrD
          (side-condition (equal? (term (cantidad (filter (mv WW ...) T))) 1)))
     
     (--> ((mv WW_1 ...) W_2)
          ambiguityerror
          appErrA
          (side-condition (> (term (cantidad (sel (mv WW_1 ...) W_2))) 1)))

     (--> (OB W)
          ambiguityerror
          δBErrA
          (side-condition (> (term (cantidad (filter W bool))) 2)))

     (--> (ON W)
          ambiguityerror
          δNErrA
          (side-condition (> (term (cantidad (filter W num))) 2)))
     
     (--> (W :: T)
          ambiguityerror
          ascErrA
          (side-condition (> (term (cantidad (filter W T))) 2)))
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
      (side-condition ,(equal? (term (cantidad (codominio (minsel T*_1 T*_2 T*_1)))) 1))
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

    [(side-condition (noisin? X (sacar Γ)))
     (types Γ (mlet (X) = (M_1 ρ) in (M_2 ρ)) : T*)
    ----------------------------------------------------- let
    (types Γ ((mlet (X) = M_1 in M_2) ρ) : T*)]



  [ (types Γ C_1 : T*_1)
     ;(side-condition (esta? T*_1 T_1))
     (side-condition (construirEnvCond ρ))
     (side-condition (definido? ρ))
     (side-condition (sinElemRep  (extraerVar (extmult (construirEnv ρ) (X T*_1)) X)))
     (⊢ (extmult (construirEnv ρ) (X T*_1)) Γ M_2 : T*_2)     
    ------------------------------------------------------ c-let
    (types Γ (mlet (X) = C_1 in (M_2 ρ)) : T*_2)]
  
    [(unique X)
     (side-condition (construirEnvCond ρ))
     (side-condition (definido? Γ))
     (⊢ (construirEnv ρ) (extT Γ (X T_1)) M : T*)
     (side-condition (noisin? X (sacar Γ)))
     (side-condition (noisin? X (sacar (construirEnv ρ))))
     (side-condition (novacio? T*))
     (side-condition (esta? T* T_2))
     ------------------------------------------ λ
     (types Γ ((λ (X (→ T_1 T_2)) M) ρ) : ((→ T_1 T_2)))])




;--------------------------------------------------------------------------------------------------------------------
(define value? (redex-match OLρI  W))

(define (is-value? t)
        (redex-match? OLρT  W t))

(define (is-typefunc? t)
        (redex-match? OLρT  (→ T_1 T_2) t))

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
  [(construirEnvCond ((X W) any_0 ...)) ,(and (term (construirEnvAuxCond W))
                                                      (term (construirEnvCond (any_0 ...))) (term (noisin? X (sacar (any_0 ...)))))]
  [(construirEnvCond ()) #t])



(define-metafunction OLρT
  [(construirEnvAuxCond  WW) ,(and   (judgment-holds (types () WW : (_ ... T_1 _ ...))) (term (esta?  ,(first (ObtTypes (term WW))) (tagi WW))))]

  [(construirEnvAuxCond  (mv  WW any_0 ...)) ,(and   (judgment-holds (types () WW : (_ ... T_1 _ ...))) (term (esta?  ,(first (ObtTypes (term WW))) (tagi WW)))
                                                      (term (construirEnvAuxCond (mv any_0 ...))) (term (noisin? (tagi WW) (sacartagi (any_0 ...)) )))]
  
  [(construirEnvAuxCond (mv )) #t]

  ;[(construirEnvAuxCond ()) #t]
  )

;(define-metafunction OLρT
  ;[(construirEnvAuxCond  ((T W) any_0 ...)) ,(and  (term (esta?  ,(first (ObtTypes (term W))) T))
                                                      ;(term (construirEnvAuxCond (any_0 ...))) (term (noisin? T (sacar (any_0 ...)) )))]
  ;[(construirEnvAuxCond ()) #t])


;(define-metafunction OLρT
  ;[(construirEnvAuxCond  ((T W) any_0 ...)) ,(and   (judgment-holds (types () W : (_ ... T _ ...)))
                                                      ;(term (construirEnvAuxCond (any_0 ...))) (term (noisin? T (sacar (any_0 ...)) )))]
  ;[(construirEnvAuxCond ()) #t])

(define-metafunction OLρT
  [(construirEnv ((X W) any_0 ...)) (concat (X (construirEnvAux W))
                                                      (construirEnv (any_0 ...)))]
  [(construirEnv ()) ()])

(define-metafunction OLρT
  [(construirEnvAux  WW)  ()]

  [(construirEnvAux  (mv WW any_0 ...)) (concat  (tagi WW)
                                                      (construirEnvAux (mv any_0 ...)))]
  [(construirEnvAux (mv )) ()])


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

(define-metafunction OLT
  [(dominio (→ T_1 T_2)) T_1]
  [(dominio any ) #f])

(define-metafunction OLT
  [(cod (→ T_1 T_2)) T_2]
  [(cod any ) #f])

(define-metafunction OLρT
    [(tagi B) bool]
    [(tagi N) num]
    [(tagi CH) str]
    [(tagi add1) (→ num num)]
    [(tagi not) (→ bool bool)]
    [(tagi ((λ (X T) M) ρ)) T]
    [(tagi (λ (X T) M)) T]
  )
 
(define-metafunction OLρT
    [(predicado1(_ ... (any_x any_y) _ ...) any_x) #f]
    [(predicado1 any any_x) #t])

(define-metafunction OLρT
  [(sel1 () any_v ) ()]
  [(sel1 (any_1 any_2 ...) any_v) ,(if (equal? (term (dominio(tagi any_1))) (term (tagi any_v)) )
                                                                     (term (concat (any_1 any_v) (sel1  (any_2 ...) any_v)))
                                                                     (term (sel1  (any_2 ...) any_v)))])


(define-metafunction OLρT
  [(sel any (mv )) ()]
  [(sel (mv any ...) WW) (sel1 (any ...) WW)]
  [(sel (mv any ...) (mv WW_1 WW_2 ...))  (appeenndd (sel1 (any ...) WW_1) (sel (mv any ...) (mv WW_2 ...)))])
;--------------------------------------------------------------------------------------------------------------------
(define-language REDEX)


(define-metafunction REDEX
    ;appeenndd : any (any ...) -> (any ...)
    [(appeenndd  () any) any]
    [(appeenndd (any_1 any_2 ...) any) (concat any_1 (appeenndd (any_2 ...) any))])




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


(define-judgment-form OLρT
    #:mode (lookup7 I I O)
    #:contract (lookup7 ((any any) ...) any any)
    [(lookup7 (_ ... (any_x WW) _ ...) any_x WW)]
    [(lookup7 (_ ... (any_x (mv WW ...)) _ ...) any_x (mv WW ...))])


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
    ;ext1 : ((any (any ...)) ...) (any any) -> ((any (any ...)) ...)
    [(ext1 (any_0 ... (any_x (any_v0 ...)) any_1 ...) (any_x any_p))
     (any_0 ... (any_x (any_p any_v0 ...)) any_1 ...)]
    [(ext1 (any_0 ...) (any_x any_p))
     ((any_x (any_p)) any_0 ...)])

(define-metafunction REDEX
    ;ext : ((any any) ...) (any any) ... -> ((any any) ...)
    [(ext any) any]
    [(ext any any_0 any_1 ...)
     (ext1 (ext any any_1 ...) any_0)])



(define-metafunction REDEX
  [(sinElemRep ()) #t]
  [(sinElemRep (any any_1 ...)) ,(if (term (isin? any (any_1 ... )))
                                     #f
                                     (term (sinElemRep (any_1 ...)))
                                                                     )])


(define-metafunction REDEX
  [(extraerVar ((any_x any_y) any ... ) any_x) any_y]
  [(extraerVar (any any_1 ...) any_x) (extraerVar (any_1 ...) any_x)])

(define-metafunction REDEX
    ;ext1 : ((any (any ...)) ...) (any any) -> ((any (any ...)) ...)
    [(extmult1 (any_0 ... (any_x (any_v0 ...)) any_1 ...) (any_x any_p))
     (any_0 ... (any_x (appeenndd any_p (any_v0 ...))) any_1 ...)]
    [(extmult1 (any_0 ...) (any_x any_p))
     ((any_x any_p) any_0 ...)])

(define-metafunction REDEX
    ;ext : ((any any) ...) (any any) ... -> ((any any) ...)_in
  
    [(extmult any) any]
    [(extmult any any_0 any_1 ...)
     (extmult1 (extmult any any_1 ...) any_0)])




(define-metafunction OLρT
    ;ext1E : ((any (any ...)) ...) (any any) -> ((any (any ...)) ...)
  
    [(ext1E (any_0 ... (any_x (mv any_v0 ...)) any_1 ...) (any_x WW))
     
     (any_0 ... (any_x (mv WW any_v0 ...)) any_1 ...)]

  [(ext1E (any_0 ... (any_x (mv any_v0 ...)) any_1 ...) (any_x (mv WW ...)))
     
     (any_0 ... (any_x (mv WW ... any_v0 ...)) any_1 ...)]
  
    [(ext1E (any_0 ...) (any_x WW))
     ((any_x (mv WW)) any_0 ...)]
  
    [(ext1E (any_0 ...) (any_x (mv WW ...)))
     ((any_x (mv WW ...)) any_0 ...)])

(define-metafunction OLρT
    ;extE : ((any any) ...) (any any) ... -> ((any any) ...)
    [(extE any) any]
    [(extE any any_0 any_1 ...)
     (ext1E (extE any any_1 ...) any_0)])






(define-metafunction OLρT
    ;ext1EL : ((any (any ...)) ...) (any any) -> ((any (any ...)) ...)
  
    [(ext1EL (any_0 ... (any_x (mv any_v0 ...)) any_1 ...) (any_x WW))
     
     (any_0 ... (any_x (mv WW any_v0 ...)) any_1 ...)]

  [(ext1EL (any_0 ... (any_x (mv any_v0 ...)) any_1 ...) (any_x (mv WW ...)))
     
     (any_0 ... (any_x (mv WW ... any_v0 ...)) any_1 ...)]
  
    [(ext1EL (any_0 ...) (any_x any_p))
     ((any_x any_p) any_0 ...)])

(define-metafunction OLρT
    ;extEL : ((any any) ...) (any any) ... -> ((any any) ...)
    [(extEL any) any]
    [(extEL any any_0 any_1 ...)
     (ext1EL (extEL any any_1 ...) any_0)])




(define-metafunction REDEX
    [(definido? ()) #t]
    [(definido? ((any_x any_y) any_0 ...)) ,(and (term (noisin? any_x (sacar (any_0 ...)) )) (term (definido? (any_0 ...))))])

(define-metafunction REDEX
    [(sacar ()) ()]
    [(sacar ((any_x any_y) any_0 ...)) (concat any_x (sacar  (any_0 ...)))])





(define-metafunction REDEX
    [(sacartagi ()) ()]
    [(sacartagi ( any_x any_0 ...)) (concat (tagi any_x) (sacartagi  (any_0 ...)))])


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
        (redex-match? OLρ  ((λ (X T) C) ρ) t))

(define-metafunction OLρT
    [(predicado(_ ... (any_x ()) _ ...) any_x any_s) #t]
    [(predicado(_ ... (any_x (any_v any_v1  ...)) _ ...) any_x any_s) ,(if (term (igtag(tagi any_v) any_s))
                                                                     #f
                                                                     (term (predicado((any_x (any_v1  ...))) any_x any_s)))]
  [(predicado any any_x any_s) #f])

(define-metafunction OLρT
    [(igtag T T) #t]
    [(igtag T_1 T_2) #f]
  )


(define-metafunction OLρT
    [(filter() T) ()]
    [(filter WW T) ,(if (term (igtag(tagi WW) T))
                                                                     (term (mv WW))
                                                                     (term (mv )))]
    [(filter(WW WW_1 ...) T) ,(if (term (igtag(tagi WW) T))
                                                                     (term (concat WW (filter  (WW_1 ...) T)))
                                                                     (term (filter  (WW_1 ...) T)))]
  [(filter(mv WW WW_1 ...) T) ,(if (term (igtag(tagi WW) T))
                                                                     (term (concat mv (concat WW (filter  (WW_1 ...) T))))
                                                                     (term (concat mv(filter  (WW_1 ...) T))))])

(define-metafunction OLρT
  [(matchear ((WW_1 WW_2))) ((WW_1 WW_2) :: (cod (tagi WW_1)))])


(define-metafunction OLρT
    [(aplicar() O) ()]
    [(aplicar WW O) (aplicar1 WW O)]
    [(aplicar(WW WW_1 ...) O) (concat (aplicar1 WW O) (aplicar (WW_1 ...) O))]
    [(aplicar(mv WW WW_1 ...) O) (concat mv (concat (aplicar1 WW O) (aplicar (WW_1 ...) O)))])

(define-metafunction OLρT
  [(aplicar1  N add1) ,(add1 (term N))]
  [(aplicar1  B not) ,(not (term B))])
;--------------------------------------------------------------------------------------------------------------------
(define (types? C)
  (judgment-holds (types () ,C : (T))))

(define (ObtTypes C)
  (judgment-holds (types () ,C : T*) T*))
 
(define w? (redex-match OLρT WWW))

(define (reduces? C)
  (not (null? (apply-reduction-relation
               vρ
               (term ,C)))))


(define (progress-holds? C)
  ;(define C  (term (configuration1 ,CI)))
  ;(define I  (term (tipoConf ,CI)))
  (if (types? C)
            (or (w? C)
          (reduces? C))
          
      #t))

(define (progress-holds1? M)
  ;(define C  (term (configuration1 ,CI)))
  ;(define I  (term (tipoConf ,CI)))
  (if (types1? M)
      (let ((l (reduces1? M)))
        (and (equal? (length l) 1) (w? (first l))))
       
          
      #t))

(define (types1? M)
  (judgment-holds (types () ,(term (configurationM ,M)) : (T))))


(define (reduces1? M)
   (apply-reduction-relation*
               vρ
               (term (configurationM ,M))))

(define-metafunction OLρT
  [(configurationM M) (M ())])

#|
(apply-reduction-relation* vρ  (term ((mlet (x ) = (λ (a3 (→ bool bool)) (not #t)) in 
(mlet (x ) = 2 in 
(mlet (x ) = #f in (not x)))) () )))


(apply-reduction-relation* vρ  (term ((mlet (x ) = (λ (a_3 (→ bool bool)) (not #t)) in 
(mlet (x ) = 2 in 
(mlet (x ) = #f in x))) () )))

(apply-reduction-relation* vρ  (term ((mlet (z ) = (λ (u_1 (→ num (→ num num))) (λ (u_2 (→ num num)) (add1 3))) in 
(mlet (z ) = (λ (a_1 (→ bool (→ bool bool))) (λ (a_2 (→ bool bool)) (not #t)))  in 
(mlet (y ) = #t in 
(mlet (y ) = 1 in 
(mlet (x ) = (λ (a_3 (→ bool bool)) (not #t)) in 
(mlet (x ) = (λ (a_4 (→ num num)) (add1 1)) in 
(mlet (t ) = 2 in 
(mlet (t ) = #f in ((z y)(x t)))))))))) () )))

(apply-reduction-relation* vρ  (term (
(mlet (z ) = (λ (a_1 (→ bool (→ bool bool))) (λ (a_2 (→ bool bool)) (not #t)))  in 
(mlet (y ) = #t in 
(mlet (y ) = 1 in 
(mlet (x ) = (λ (a_3 (→ bool bool)) (not #t)) in
(mlet (t ) = 2 in 
(mlet (t ) = #f in ((z (y :: bool))(x (t :: bool))))))))) () )))


(apply-reduction-relation* vρ  (term ((mlet (x ) = 2 in 
(mlet (x ) = #f in
      ((λ (a_3 (→  num num )) x) 5))) () )))


(apply-reduction-relation* vρ  (term ((mlet (z ) = (λ (u_1 (→  num num ))  (add1 u_1)) in 
(mlet (z ) = (λ (a_1 (→  bool bool ))  (not a_1))  in  
(mlet (x ) = (λ (a_3 (→  bool bool )) (not #t)) in 
(mlet (x ) = (λ (a_4 (→  num num )) (add1 1)) in  (z x))))) () )))



(apply-reduction-relation* vρ  (term ((mlet (x ) = 2 in 
(mlet (x ) = #f in
      ((λ (a_3 (→  num num )) x) 5))) () )))




(apply-reduction-relation* vρ  (term                                     (
(mlet (z) =  (λ (u_1 (→  (→  str str ) (→  str str ) ))  ((λ (a_5 (→  str str ))  a_5) u_1)) in 
(mlet (z ) = (λ (a_1 (→   (→  bool bool ) (→  bool bool )))  ((λ (a_5 (→  bool bool ))  a_5) a_1))  in  
(mlet (x ) = (λ (a_3 (→  bool bool ))  (not #t)) in 
(mlet (x ) = (λ (a_4 (→  num num ))  (add1 1)) in  (z x))))) () )))

(apply-reduction-relation* vρ  (term ((mlet (x ) = (λ (a_3 ) (not a_3)) in 
(mlet (x ) = 2 in 
(mlet (x ) = #f in (x x)))) () )))

(apply-reduction-relation* vρ  (term
((mlet(x ) = (λ (a_3 (→  bool bool )) (not #t)) in 
(mlet (y ) = (λ (a_3 (→  (→  bool bool ) (→  bool bool ) )) (mlet (t ) = (λ (a_5 (→  bool bool )) (not #t)) in a_3)) in 
 (y x))) () )))










(judgment-holds (⊢ () () (λ (u1 (→ num (→ num num)) ) (λ (u2 (→ num num)) ((add1 3) :: num))) : T*) T*)


(judgment-holds (⊢ () () (mlet (z) = (λ (u1 (→ num (→ num num)) ) (λ (u2 (→ num num)) ((add1 3) :: num))) in 
(mlet (z ) = (λ (a1 (→ bool (→ bool bool))) (λ (a2 (→ bool bool)) (not #t)))  in 
(mlet (y ) = #t in 
(mlet (y ) = 1 in 
(mlet (x ) = (λ (a3 (→ bool bool)) (not #t)) in 
(mlet (x ) = (λ (a4 (→ str str)) "abcd") in 
(mlet (t ) = "abc" in 
(mlet (t ) = #f in ((z y)(x t)))))))))) : T*) T*)


(redex-check OLρT C (progress-holds? (term C)) #:attempts 10000000)


(progress-holds1? (term                                     
(mlet(x ) = (λ (a3 (→ (→  bool bool ) bool)) (a3 #t)) in 
 (x  (λ (a3 (→  bool bool ))
               (mlet (z ) = 4 in (mlet (z ) = #t in z)))))))

|#







;--------------------------------------------------------------------------------------------------------------------
(test-->>
   vρ
   (term ((mlet (z ) = (λ (u1 (→ bool (→  bool bool ) )) (λ (u2 (→  bool bool )) (add1 3))) in 
(mlet (z ) = (λ (a1 (→ num (→  num num ) )) (λ (a2 (→  num num )) (not #t)))  in 
(mlet (y ) = #t in 
(mlet (y ) = 1 in 
(mlet (x ) = (λ (a3 (→  bool bool )) (not #t)) in 
(mlet (x ) = (λ (a4 (→  num num )) (add1 1)) in 
(mlet (t ) = 2 in 
(mlet (t ) = #f in ((z y)(x t)))))))))) () ))
    (term ambiguityerror))
;-------------------------------------------------------------------------------------------------------------------

(test-->>
   vρ
  (term ((mlet (x ) = (λ (a3 (→  bool bool )) (not #t)) in 
(mlet (x ) = 2 in 
(mlet (x ) = #f in x))) () ))
  (term (mv #f 2 ((λ (a3 (→  bool bool )) (not #t)) ()) )))
;-------------------------------------------------------------------------------------------------------------------
(test-->>
   vρ

   (term ((mlet (x ) = 2 in 
(mlet (x ) = #f in
      ((λ (a3 (→  num num )) x) 5))) () ))
   (term (mv 2))
  )
;-------------------------------------------------------------------------------------------------------------------
  (test-->>
   vρ (term ((mlet (x ) = 2 in 
(mlet (x ) = #f in
      (add1 x))) () ))
(term (mv 3))
  )

;-------------------------------------------------------------------------------------------------------------------

(test-->>
   vρ

   (term ((mlet (z ) = (λ (u1 (→  num num ))  (add1 u1)) in 
(mlet (z ) = (λ (a1 (→  bool bool ))  (not a1))  in  
(mlet (x ) = (λ (a3 (→  bool bool )) (not #t)) in 
(mlet (x ) = (λ (a4 (→  num num )) (add1 1)) in  (z x))))) () ))
   (term dispatcherror)
  )
;-------------------------------------------------------------------------------------------------------------------
(test-->>
   vρ

   (term
                                     (
(mlet (z) =  (λ (u1 (→ (→  bool bool ) (→  bool bool )))  ((λ (a5 (→ (→  bool bool ) (→  bool bool )))  a5) u1)) in 
(mlet (z ) = (λ (a1 (→ (→  str str ) (→  str str )))  ((λ (a5 (→ (→  str str ) str))  a5) a1))  in  
(mlet (x ) = (λ (a3  (→  bool bool ) )  (not #t)) in 
(mlet (x ) = (λ (a4 (→  num num ) )  (add1 1)) in  (z x))))) () ))

   (term (mv
 ((λ (a3 (→ bool bool))
    (not #t))
  ((z
    (mv
     ((λ (a1
          (→
           (→ str str)
           (→ str str)))
        ((λ (a5
             (→
              (→ str str)
              str))
           a5)
         a1))
      ((z
        (mv
         ((λ (u1
              (→
               (→ bool bool)
               (→ bool bool)))
            ((λ (a5
                 (→
                  (→
                   bool
                   bool)
                  (→
                   bool
                   bool)))
               a5)
             u1))
          ())))))
     ((λ (u1
          (→
           (→ bool bool)
           (→ bool bool)))
        ((λ (a5
             (→
              (→ bool bool)
              (→ bool bool)))
           a5)
         u1))
      ()))))))))
;-------------------------------------------------------------------------------------------------------------------


(test-->>
   vρ

   (term
((mlet(x ) = (λ (a3 (→  bool bool )) (not #t)) in 
(mlet (y ) = (λ (a3 (→ (→  bool bool ) (→  bool bool ))) (mlet (t ) = (λ (a5 (→  bool bool )) (not #t)) in a3)) in 
 (y x))) () ))
   (term (mv ((λ (a3 (→  bool bool )) (not #t)) ()))))

;-------------------------------------------------------------------------------------------------------------------
(test-->>
   vρ
   (term ((mlet (x ) = (λ (a3 (→  bool bool )) (not #t)) in 
(mlet (x ) = 2 in 
(mlet (x ) = #f in (not x)))) () ))
   (term (mv #t)))

;-------------------------------------------------------------------------------------------------------------------
(test-->>
   vρ
    (term ((mlet (x ) = 2 in 
(mlet (x ) = #f in
      (add1 x))) () ))
   (term (mv 3)))

;-------------------------------------------------------------------------------------------------------------------
(test-->>
   vρ
   (term ((mlet (x ) = (λ (a3 (→  bool bool )) (not a3)) in 
(mlet (x ) = 2 in 
(mlet (x ) = #f in (x x)))) () ))
   (term (mv #t)))

;-------------------------------------------------------------------------------------------------------------------
(test-->>
   vρ
(term ((mlet (z ) = (λ (u1 (→ num (→  num num ))) (λ (u2 (→  num num )) (add1 u2))) in 
(mlet (z ) = (λ (a1 (→ bool (→  bool bool ))) (λ (a2 (→  bool bool )) (not a2 )))  in 
(mlet (y ) = #t in 
(mlet (y ) = 1 in 
(mlet (x ) = (λ (a3 (→  bool bool )) (not a3)) in 
(mlet (x ) = (λ (a4 (→  num num )) (add1 a4)) in 
(mlet (t ) = 2 in 
(mlet (t ) = #f in ((z (y :: bool))(x (t :: bool))))))))))) () ))
(term (mv #f))
   )
;-------------------------------------------------------------------------------------------------------------------

(test-->>
   vρ
   (term ((mlet (x ) = (λ (a3 (→  bool bool )) (not a3)) in 
(mlet (x ) = 2 in 
(mlet (x ) = #f in (x (x :: bool))))) () ))
   (term (mv #t)))

;-------------------------------------------------------------------------------------------------------------------
(test-->>
   vρ
   (term (
(mlet (z ) = (λ (a1 (→ bool (→  bool bool ))) (λ (a2 (→  bool bool )) (not #t)))  in 
(mlet (y ) = #t in 
(mlet (y ) = 1 in 
(mlet (x ) = (λ (a3  (→  bool bool )) (not #t)) in 

(mlet (t ) = 2 in 
(mlet (t ) = #f in ((z (y :: bool))(x (t :: bool))))))))) () ))
   (term (mv #f)))

;-------------------------------------------------------------------------------------------------------------------
(test-->>
   vρ
   (term ((mlet (x ) = 2 in 
(mlet (x ) = #f in
      (mlet (x ) = 3 in
            (mlet (x ) = 4 in 
      (add1 x))))) () ))
   (term ambiguityerror))

;-------------------------------------------------------------------------------------------------------------------
(test-->>
   vρ
   (term ((mlet (x ) = 2 in 
(mlet (x ) = #f in
      ((λ (a3 (→  bool bool )) a3) x))) () ))
   (term (mv #f)))

;-------------------------------------------------------------------------------------------------------------------
(test-->>
   vρ
   (term ((mlet (r ) = #t in
(mlet (r ) = 1 in                                             
(mlet (z ) = (λ (a1 (→ bool (→  bool bool ))) (λ (a2 (→  bool bool )) (not a2)))  in 
(mlet (x ) = (λ (a3 (→  bool bool )) (not a3)) in 
(mlet (y ) = (r :: bool) in 
(mlet (t ) = y in 
 ((z y)(x (t :: bool))))))))) () ))
   (term (mv #t))
   )
;-------------------------------------------------------------------------------------------------------------------
(test-->>
   vρ
   (term ((mlet (x ) = (λ (a3 (→  bool bool )) (not a3)) in 
(mlet (x ) = 2 in 
(mlet (x ) = #f in (x x)))) () ))
   (term (mv #t)))
;-------------------------------------------------------------------------------------------------------------------

(test-->>
   vρ
(term ((mlet (z ) = (λ (u1 (→ num (→  num num ))) (λ (u2 (→  num num )) (add1 u2))) in 
(mlet (z ) = (λ (a1 (→ bool (→  bool bool ))) (λ (a2 (→  bool bool )) (not a2 )))  in 
(mlet (y ) = #t in 
(mlet (y ) = 1 in 
(mlet (x ) = (λ (a3 (→  bool bool )) (not a3)) in 
(mlet (x ) = (λ (a4 (→  num num )) (add1 a4)) in 
(mlet (t ) = 2 in 
(mlet (t ) = #f in ((z y )(x t )))))))))) () ))
(term ambiguityerror)
   )

;-------------------------------------------------------------------------------------------------------------------
(test-->>
   vρ
(term ((mlet(x ) = (λ (a3 (→ (→  bool bool ) bool)) (a3 #t)) in 
 (x  (λ (a3 (→  bool bool ))
               (mlet (z ) = 4 in (mlet (z ) = #t in z))))) ()))
(term (mv #t)))

;-------------------------------------------------------------------------------------------------------------------
(test-equal
   (judgment-holds (⊢ () () (λ (u1 (→ num (→ num num)) ) (λ (u2 (→ num num)) ((add1 3) :: num))) : T*) T*)
   (list (term ((→ num (→ num num))))))
;-------------------------------------------------------------------------------------------------------------------
(test-equal (judgment-holds (⊢ () () (mlet (z) = (λ (u1 (→ num (→ num num)) ) (λ (u2 (→ num num)) ((add1 3) :: num))) in 
(mlet (z ) = (λ (a1 (→ bool (→ bool bool))) (λ (a2 (→ bool bool)) (not #t)))  in 
(mlet (y ) = #t in 
(mlet (y ) = 1 in 
(mlet (x ) = (λ (a3 (→ bool bool)) (not #t)) in 
(mlet (x ) = (λ (a4 (→ str str)) "abcd") in 
(mlet (t ) = "abc" in 
(mlet (t ) = #f in ((z y)(x t)))))))))) : T*) T*)
            (list ))
;-------------------------------------------------------------------------------------------------------------------
(test-equal (judgment-holds (⊢ () () (mlet (z ) = (λ (u1 (→ bool (→  bool bool ) )) (λ (u2 (→  bool bool )) (add1 3))) in 
(mlet (z ) = (λ (a1 (→ num (→  num num ) )) (λ (a2 (→  num num )) (not #t)))  in 
(mlet (y ) = #t in 
(mlet (y ) = 1 in 
(mlet (x ) = (λ (a3 (→  bool bool )) (not #t)) in 
(mlet (x ) = (λ (a4 (→  num num )) (add1 1)) in 
(mlet (t ) = 2 in 
(mlet (t ) = #f in ((z y)(x t)))))))))): T*) T*)

            (list ))
;-------------------------------------------------------------------------------------------------------------------
(test-equal (judgment-holds (⊢ () () (mlet (x ) = (λ (a3 (→  bool bool )) (not #t)) in 
(mlet (x ) = 2 in 
(mlet (x ) = #f in x))) : T*) T*)

            (list (term (bool num (→ bool bool)))))
;-------------------------------------------------------------------------------------------------------------------
(test-equal (judgment-holds (⊢ () () (mlet (x ) = 2 in 
(mlet (x ) = #f in
      ((λ (a3 (→  num num )) x) 5))) : T*) T*)

            (list (term (num))))
;-------------------------------------------------------------------------------------------------------------------
(test-equal (judgment-holds (⊢ () () (mlet (x ) = 2 in 
(mlet (x ) = #f in
      (add1 x))) : T*) T*)

            (list (term (num))))
;-------------------------------------------------------------------------------------------------------------------
(test-equal (judgment-holds (⊢ () () (mlet (z ) = (λ (u1 (→  num num ))  (add1 u1)) in 
(mlet (z ) = (λ (a1 (→  bool bool ))  (not a1))  in  
(mlet (x ) = (λ (a3 (→  bool bool )) (not #t)) in 
(mlet (x ) = (λ (a4 (→  num num )) (add1 1)) in  (z x))))): T*) T*)

            (list ))
;-------------------------------------------------------------------------------------------------------------------
(test-equal (judgment-holds (⊢ () () (mlet (z) =  (λ (u1 (→ (→  bool bool ) (→  bool bool )))  ((λ (a5 (→ (→  bool bool ) (→  bool bool )))  a5) u1)) in 
(mlet (z ) = (λ (a1 (→ (→  str str ) (→  str str )))  ((λ (a5 (→ (→  str str ) str))  a5) a1))  in  
(mlet (x ) = (λ (a3  (→  bool bool ) )  (not #t)) in 
(mlet (x ) = (λ (a4 (→  num num ) )  (add1 1)) in  (z x))))) : T*) T*)

            (list ))
;-------------------------------------------------------------------------------------------------------------------
(test-equal (judgment-holds (⊢ () () (mlet(x ) = (λ (a3 (→  bool bool )) (not #t)) in 
(mlet (y ) = (λ (a3 (→ (→  bool bool ) (→  bool bool ))) (mlet (t ) = (λ (a5 (→  bool bool )) (not #t)) in a3)) in 
 (y x))): T*) T*)

            (list (term ((→ bool bool)))))
;-------------------------------------------------------------------------------------------------------------------
(test-equal (judgment-holds (⊢ () () (mlet (x ) = (λ (a3 (→  bool bool )) (not #t)) in 
(mlet (x ) = 2 in 
(mlet (x ) = #f in (not x)))) : T*) T*)

            (list (term (bool))))
;-------------------------------------------------------------------------------------------------------------------
(test-equal (judgment-holds (⊢ () () (mlet (x ) = 2 in 
(mlet (x ) = #f in
      (add1 x))) : T*) T*)

            (list (term (num))))
;-------------------------------------------------------------------------------------------------------------------
(test-equal (judgment-holds (⊢ () () (mlet (x ) = (λ (a3 (→  bool bool )) (not a3)) in 
(mlet (x ) = 2 in 
(mlet (x ) = #f in (x x)))) : T*) T*)

            (list (term (bool))))
;-------------------------------------------------------------------------------------------------------------------
(test-equal (judgment-holds (⊢ () () (mlet (z ) = (λ (u1 (→ num (→  num num ))) (λ (u2 (→  num num )) (add1 u2))) in 
(mlet (z ) = (λ (a1 (→ bool (→  bool bool ))) (λ (a2 (→  bool bool )) (not a2 )))  in 
(mlet (y ) = #t in 
(mlet (y ) = 1 in 
(mlet (x ) = (λ (a3 (→  bool bool )) (not a3)) in 
(mlet (x ) = (λ (a4 (→  num num )) (add1 a4)) in 
(mlet (t ) = 2 in 
(mlet (t ) = #f in ((z (y :: bool))(x (t :: bool))))))))))) : T*) T*)

            (list (term (bool))))
;-------------------------------------------------------------------------------------------------------------------
(test-equal (judgment-holds (⊢ () () (mlet (x ) = (λ (a3 (→  bool bool )) (not a3)) in 
(mlet (x ) = 2 in 
(mlet (x ) = #f in (x (x :: bool))))) : T*) T*)

            (list (term (bool))))
;-------------------------------------------------------------------------------------------------------------------
(test-equal (judgment-holds (⊢ () () (mlet (z ) = (λ (a1 (→ bool (→  bool bool ))) (λ (a2 (→  bool bool )) (not #t)))  in 
(mlet (y ) = #t in 
(mlet (y ) = 1 in 
(mlet (x ) = (λ (a3  (→  bool bool )) (not #t)) in 

(mlet (t ) = 2 in 
(mlet (t ) = #f in ((z (y :: bool))(x (t :: bool))))))))) : T*) T*)

            (list (term (bool))))
;-------------------------------------------------------------------------------------------------------------------
(test-equal (judgment-holds (⊢ () () (mlet (x ) = 2 in 
(mlet (x ) = #f in
      (mlet (x ) = 3 in
            (mlet (x ) = 4 in 
      (add1 x))))) : T*) T*)

            (list ))
;-------------------------------------------------------------------------------------------------------------------
(test-equal (judgment-holds (⊢ () () (mlet (x ) = 2 in 
(mlet (x ) = #f in
      ((λ (a3 (→  bool bool )) a3) x))) : T*) T*)

            (list (term (bool))))
;-------------------------------------------------------------------------------------------------------------------
(test-equal (judgment-holds (⊢ () () (mlet (x ) = 2 in 
(mlet (x ) = #f in
      ((λ (a3 (→  bool bool )) a3) x))): T*) T*)

            (list (term (bool))))
;-------------------------------------------------------------------------------------------------------------------
(test-equal (judgment-holds (⊢ () () (mlet (x ) = (λ (a3 (→  bool bool )) (not a3)) in 
(mlet (x ) = 2 in 
(mlet (x ) = #f in (x x)))) : T*) T*)

            (list (term (bool))))
;-------------------------------------------------------------------------------------------------------------------

(test-equal (judgment-holds (⊢ () () (mlet (z ) = (λ (u1 (→ num (→  num num ))) (λ (u2 (→  num num )) (add1 u2))) in 
(mlet (z ) = (λ (a1 (→ bool (→  bool bool ))) (λ (a2 (→  bool bool )) (not a2 )))  in 
(mlet (y ) = #t in 
(mlet (y ) = 1 in 
(mlet (x ) = (λ (a3 (→  bool bool )) (not a3)) in 
(mlet (x ) = (λ (a4 (→  num num )) (add1 a4)) in 
(mlet (t ) = 2 in 
(mlet (t ) = #f in ((z y )(x t )))))))))) : T*) T*)

            (list ))
;-------------------------------------------------------------------------------------------------------------------

(test-equal (judgment-holds (⊢ () ()
(mlet(x ) = (λ (a3 (→ (→  bool bool ) bool)) (a3 #t)) in 
 (x  (λ (a3 (→  bool bool ))
               (mlet (z ) = 4 in (mlet (z ) = #t in z)))))
 : T*) T*)
    (list (term (bool))))


















