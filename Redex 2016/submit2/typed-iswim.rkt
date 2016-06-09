#lang play
(require redex)

#|
Instance of ISWIM languaje with function of one and two arguments, and integer and boolean values
|#
(define-language ISWIM-2
  ((N M) V
         (M M)         
         (op1 M)
         (op2 M M)         
         (if M M M)        
         (let/cc : T X M)
         ;now the language has type err refer only to dynamic error (produces by primitive operators)
         ;of course the syntasis allows to explicit throw an error but this program
         ;are rejected by the type-checker, because I didn't give a type to error
         
         ;If we need to throw explicit error in the code, we can give ERROR-TYPE to errors
         ;and we can do ERROR-TYPE consistent with all types
         (err l)
         (pair M M)
         (fst M)
         (snd M)
         (inl M T)
         (inr M T)
         (case M of (inl X => M) (inr X => M))
         )
  ;operations with arity 1
  (op1 add1
       sub1
       iszero
       not)  
  ;operations with arity 2
  (op2 +
       -
       /
       *
       <
       and
       or)
  ((V U W) b
           X
           (λ X : T M)
           (λ↑ X M)
           (pair V V)
           (inl V T)
           (inr V T))
  ;standart context
  (E hole
     (E M)
     (V E)
     (op1 E)
     (op2 E M)
     (op2 V E)
     (if E M M)
     (fst E)
     (snd E)
     (pair E M)
     (pair V E)
     (inl E T)
     (inr E T)
     (case E of (inl X => M) (inr X => M)))
  (b n
     bool)
  (bool boolean)  
  (n number)
  ;using error label with this error for simplicity. The first one and the last one
  ;are not needed with a type-checker
  (l "lambda" "error in δ" "unknow" "constant in position of λ")
  (X variable-not-otherwise-mentioned)  
  ;agregate types to the language
  (T INT BOOL STRING UNIT
     (→ T T)
     (T + T)
     (T * T)
     (↦ T T T);type of binary primitive
     (↦ T T);type of unary primitive
     ⊥);wrapper when apply continuation

#|
ABOUT CALL/CC:
I did implement LET/CC instead of CALL/CC since the difference is only the lambda.
(LET/CC : T k body)
k: has the implicit type (-> T ⊥), so LET/CC has type (-> (-> T ⊥) T) -> T

|#
  
)
;------------------------------------------------------------
;ENVIROMENT OF TYPES

;extension to the ISWIM language to include enviroment terms
(define-extended-language ISWIM-2+Γ ISWIM-2
  [Γ ((X : T) ...)])
  ;[Γ · (x : t Γ)])

;extend-env:: Env Sym Type -> Env
(define-metafunction ISWIM-2+Γ
  extend : Γ X T -> any
  [(extend ([X_0 : T_0] ... [X_i : T_i] [X_i+1 : T_i+1] ...) X_i T)
   ([X_0 : T_0] ... [X_i : T] [X_i+1 : T_i+1] ...)]
  [(extend ([X_1 : T_1] ...) X_0 T_0)
   ([X_0 : T_0] [X_1 : T_1] ...)])

;lookup-env:: Env Sym -> Type
(define-metafunction ISWIM-2+Γ
  lookup : Γ X -> any
  [(lookup ([X_0 : T_0] ... [X_i : T_i] [X_i+1 : T_i+1] ...) X_i) 
   T_i]
  [(lookup Γ X) error])

;typePrimitive:: op2/op1 -> Type
(define-metafunction ISWIM-2+Γ
  [(typePrimitive op2_1) ,(typePrim (term op2_1))]
  [(typePrimitive op1_1) ,(typePrim (term op1_1))])

;typePrim:: op2/op1 - Type
(define (typePrim op)
  (match op
    ['+ (term (↦ INT INT INT))]
    ['- (term (↦ INT INT INT))]
    ['/ (term (↦ INT INT INT))];tipe double
    ['* (term (↦ INT INT INT))]
    ['< (term (↦ INT INT BOOL))]
    ['and (term (↦ BOOL BOOL BOOL))]
    ['or (term (↦ BOOL BOOL BOOL))]
    ['sub1 (term (↦ INT INT))]
    ['add1 (term (↦ INT INT))]
    ['not (term (↦ BOOL BOOL))]
    ['iszero (term (↦ INT BOOL))]))

#|
subtype? T T -> T
Verifies whether first type is subtype of the second type, returning the second argument
|#
(define-metafunction ISWIM-2+Γ
  [(subtype? T_1 T_1) T_1]
  [(subtype? T_1 ⊥) ()]
  [(subtype? ⊥ T_1) T_1]
  [(subtype? T_2 T_1) ()])

#|
commontype T T -> T
Returns the common type
|#
(define-metafunction ISWIM-2+Γ
  [(commontype T_1 T_1) T_1]
  [(commontype T_1 ⊥) T_1]
  [(commontype ⊥ T_1) T_1]
  [(commontype T_2 T_1) ()])


;------------------------------------------------------------

;FV
(define-metafunction ISWIM-2
  FV : term -> any
  [(FV b) ,(set)]
  [(FV X) ,(set (term X))]
  [(FV (λ X M)) ,(set-subtract (term (FV M)) (set (term X)))]
  [(FV (M_1 M_2)) ,(set-union (term (FV M_1))
                              (term (FV M_2)))]
  [(FV (pair M_1 M_2)) ,(set-union (term (FV M_1))
                              (term (FV M_2)))])

;subst
;M X V
;M[x<-V]
;subst: Expr Var Expr -> Expr
;Subst the variable for the third argument in the first argument
(define-metafunction ISWIM-2
  ;subst : M X V -> M
  [(subst (λ X_1 : T_1 any_1) X_1 any_2)
   (λ X_1 : T_1 any_1)]
  [(subst (λ↑ X_1 any_1) X_1 any_2)
   (λ↑ X_1 any_1)]
  [(subst (lec/cc : T_1 X_1 any_1) X_1 any_2)
   (let/cc : T_1 X_1 any_1)]
  [(subst (case (inl any_1) of 
            (inl X_1 => any_2) 
            (inr X_1 => any_3)) X_1 any_4)
   (case (inl any_1) of 
            (inl X_1 => any_2) 
            (inr X_1 => any_3))]
  [(subst (case (inl any_1) of 
            (inl X_1 => any_2) 
            (inr X_2 => any_3)) X_1 any_4)
   (case (inl any_1) of 
     (inl X_1 => any_2) 
     (inr X_5 => (subst (subst-var any_3 X_2 X_5) X_3 any_4)))
   (where X_5 ,(variable-not-in (term (X_3 any_3 any_4))
                                (term X_2)))]
  [(subst (case (inl any_1) of 
            (inl X_1 => any_2) 
            (inr X_2 => any_3)) X_2 any_4)
   (case (inl any_1) of 
     (inl X_4 => (subst (subst-var any_2 X_1 X_4) X_3 any_4)) 
     (inr X_2 => any_3))
   (where X_4 ,(variable-not-in (term (X_3 any_2 any_4))
                                (term X_1)))]
  [(subst (λ X_1 : T_1 any_1) X_2 any_2)
   (λ X_3 : T_1
     (subst (subst-var any_1 X_1 X_3) X_2 any_2))
   (where X_3 ,(variable-not-in (term (X_2 any_1 any_2))
                                (term X_1)))]
  [(subst (λ↑ X_1 any_1) X_2 any_2)
   (λ↑ X_3
     (subst (subst-var any_1 X_1 X_3) X_2 any_2))
   (where X_3 ,(variable-not-in (term (X_2 any_1 any_2))
                                (term X_1)))]
  [(subst (let/cc : T_1 X_1 any_1) X_2 any_2)
   (let/cc : T_1 X_3
     (subst (subst-var any_1 X_1 X_3) X_2 any_2))
   (where X_3 ,(variable-not-in (term (X_2 any_1 any_2))
                                (term X_1)))]
  [(subst (case (inl any_1) of (inl X_1 => any_2) (inr X_2 => any_3)) X_3 any_4)
   (case (inl any_1) of 
     (inl X_4 => (subst (subst-var any_2 X_1 X_4) X_3 any_4)) 
     (inr X_5 => (subst (subst-var any_3 X_2 X_5) X_3 any_4)))
   (where X_4 ,(variable-not-in (term (X_3 any_2 any_4))
                                (term X_1)))
   (where X_5 ,(variable-not-in (term (X_3 any_3 any_4))
                                (term X_2)))]
  [(subst X_1 X_1 any_1) any_1]
  [(subst (any_2 ...) X_1 any_1)
   ((subst any_2 X_1 any_1) ...)]
  [(subst any_2 X_1 any_1) any_2])
 
(define-metafunction ISWIM-2
  [(subst-var (any_1 ...) variable_1 variable_2)
   ((subst-var any_1 variable_1 variable_2) ...)]
  [(subst-var variable_1 variable_1 variable_2) variable_2]
  [(subst-var any_1 variable_1 variable_2) any_1])


;delta as metafunction to use in one variant of the standart-reduction
(define-metafunction ISWIM-2
  [(δ (add1 n_1)) ,(add1 (term n_1))]
  [(δ (sub1 n_1)) ,(sub1 (term n_1))]
  [(δ (iszero n_1)) ,(if (= (term n_1) 0)
                          (term #t)
                          (term #f))]
  
  [(δ (not bool_1)) ,(not (term bool_1))]
  [(δ (+ n_1 n_2)) ,(+ (term n_1) (term n_2))]
  [(δ (- n_1 n_2)) ,(- (term n_1) (term n_2))]
  [(δ (* n_1 n_2)) ,(* (term n_1) (term n_2))]  
  [(δ (/ n_1 n_2)) ,(/ (term n_1) (term n_2))]
  [(δ (< n_1 n_2)) ,(< (term n_1) (term n_2))]
  [(δ (= n_1 n_2)) ,(= (term n_1) (term n_2))]
  [(δ (and bool_1 bool_2)) ,(and (term bool_1) (term bool_2))]
  [(δ (or bool_1 bool_2)) ,(or (term bool_1) (term bool_2))]  
  )
;IMPORTANT!!!. Since the operator expected a value of certain types, there
;are case where δ is no define like (δ (not 0)) in this case an error is returns
(define-metafunction ISWIM-2
  [(δerr (op2_1 (λ X_1 : T_1 M_1) V_1)) (err "lambda")]
  [(δerr (op2_1 V_1 (λ X_1 : T_1 M_1))) (err "lambda")]
  [(δerr (op2_1 V_1 V_2)) ,(with-handlers ([exn:fail?
                                                (λ (e) (term (err "error in δ" )))])
                                 (term (δ (op2_1 V_1 V_2))))]
  [(δerr (op1_1 (λ X_1 : T_1 M_1))) (err "lambda")]
  [(δerr (op1_1 V_1)) ,(with-handlers ([exn:fail?
                                                (λ (e) (term (err "error in δ" )))])
                                 (term (δ (op1_1 V_1))))]
  )
;βv reduction: (λx.M)V βv M[x ← M]
(define βv 
  (reduction-relation
   ISWIM-2
   (--> ((λ X M_1) V_1)
        (subst M_1 X V_1)
        β)))

;Version where the βv and δ in context are used 
(define s->v 
  (reduction-relation
   ISWIM-2
   (--> (in-hole E ((λ X : T M) V))
        (in-hole E (subst M X V)) βv)
   (--> (in-hole E (op1 V_1))
        (in-hole E (δerr (op1 V_1))) δ1)
   (--> (in-hole E (op2 V_1 V_2))
        (in-hole E (δerr (op2 V_1 V_2))) δ2)
   (--> (in-hole E (if V M_1 M_2))
        (in-hole E ,(if (term V) (term M_1) (term M_2))) if)
   ;fst ;apply fst only if V_1 is a value to ensure deterministic
   ;TODO:Implement shortcut
   (--> (in-hole E (fst (pair V_1 V_2)))
        (in-hole E V_1) fst)
   ;snd ;apply fst only if V_2 is a value to ensure deterministic
   ;TODO:Implement shortcut
   (--> (in-hole E (snd (pair V_1 V_2)))
        (in-hole E V_2) snd)
   ;case-inl
   (--> (in-hole E (case (inl V_1 T_1) of (inl X_1 => M_1) (inr X_2 => M_2)))
        (in-hole E (subst M_1 X_1 V_1)) case-inl)
   ;case-inr
   (--> (in-hole E (case (inr V_1 T_1) of (inl X_1 => M_1) (inr X_2 => M_2)))
        (in-hole E (subst M_2 X_2 V_1)) case-inr)
   ;error (is not need with a type-checker
   (--> (in-hole E (b V))
        (in-hole E (err "constant in position of λ")) δerrb)
   ;let-cc
   (--> (in-hole E (let/cc : T_1 X M))
        (in-hole E (subst M X (λ↑ Y (in-hole E Y)))) let)
   ;apply continuation
   (--> (in-hole E ((λ↑ X M) V))
        (in-hole hole (subst M X V)) λ↑)   
   ))

(define err
  (reduction-relation
   ISWIM-2
   (--> (in-hole E (err l_1))
        (in-hole hole (err l_1))
        (side-condition (not (equal? (term E) (term hole)))) 
        err)   
   ))
(define s->v->err  (union-reduction-relations err s->v))


;------------------------------------------------------------
(define-judgment-form
  ISWIM-2+Γ
  #:mode (subtype I I O)
  #:contract (subtype T T T)
   
  [(where T_3 (subtype? T_1 T_2))
    -----------------------
   (subtype T_1 T_2 T_3)])


;TYPE JUDGEMENT
(define-judgment-form
  ISWIM-2+Γ
  #:mode (types I I O)
  #:contract (types Γ M T)
  
  
  ;INT
  [-----------------------
   (types Γ number INT)]
  
  ;BOOL
  [-----------------------
   (types Γ boolean BOOL)]
  
  ;STRING
  [-----------------------
   (types Γ string STRING)]
  
  ;T-VAR
  [(where T (lookup Γ X))
   -----------------------
   (types Γ X T)]
  
  ;T-ABS
  [(types (extend Γ X T_1) M_2 T_2)
   -----------------------
   (types Γ (λ X : T_1 M_2) (→ T_1 T_2))]
  
  ;T-APP
  [(types Γ M_1 (→ T_11 T_12)) 
   (types Γ M_2 T_13)
   (subtype T_13 T_11 _); if T_13 <: T_11 (case (λ x: T x) (k 1)) ; continuation pass as argument
   ----------------------------------
   (types Γ (M_1 M_2) T_12)]
  
  ;T-IF
  [(types Γ M_1 T_0)
   (subtype T_0 BOOL BOOL)
   (types Γ M_2 T_1)
   (types Γ M_3 T_2)
   (where T (commontype T_1 T_2))
   ----------------------------------
   (types Γ (if M_1 M_2 M_3) T)]
  
  ;T-ERROR
  [-----------------------
   (types Γ (err _) ⊥)]
  
  ;T-OP2
  [(where (↦ T_1 T_2 T_3) (typePrimitive op2))
   (types Γ M_1 T_11)
   (types Γ M_2 T_21)
   (subtype T_11 T_1 T_1)
   (subtype T_21 T_2 T_2)
   ----------------------------------
   (types Γ (op2 M_1 M_2) T_3)]
  
  ;T-OP1
  [(where (↦ T_1 T_2) (typePrimitive op1))
   (types Γ M_1 T_11)
   (subtype T_11 T_1 T_1)
   ----------------------------------
   (types Γ (op1 M_1) T_2)]
  
  ;T-PAIR
  [(types Γ M_1 T_1)
   (types Γ M_2 T_2)   
   ----------------------------------
   (types Γ (pair M_1 M_2) (T_1 * T_2))]
  
  ;T-PAIR-FST
  [(types Γ M_1 (T_1 * T_2))   
   ----------------------------------
   (types Γ (fst M_1) T_1)]
  
  ;T-PAIR-SND
  [(types Γ M_1 (T_1 * T_2))   
   ----------------------------------
   (types Γ (snd M_1) T_2)]
  
  ;T-INL
  [(types Γ M_1 T_1)   
   ----------------------------------
   (types Γ (inl M_1 (T_1 + T_2)) (T_1 + T_2))]
  
  ;T-INR
  [(types Γ M_1 T_2)   
   ----------------------------------
   (types Γ (inr M_1 (T_1 + T_2)) (T_1 + T_2))]
  
  ;T-CASE
  [
   (types Γ M_11 (T_1 + T_2))
   (types (extend Γ X_2 T_2) M_2 T_21)
   (types (extend Γ X_1 T_1) M_1 T_11)
   (where T (commontype T_11 T_21))
   ----------------------------------
   (types Γ (case M_11 of (inl X_1 => M_1) (inr X_2 => M_2)) T)]
  
  ;T-LET/CC
  [(types (extend Γ X_1 (→ T_1 ⊥)) M_1 T_2)
   (subtype T_2 T_1 _)
   ----------------------------------
   (types Γ (let/cc : T_1 X_1 M_1) T_1)]
)
;------------------------------------------------------------
;METHODS OF THE PROJECT 2, THEY WERE USED FOR TESTING
;------------------------------------------------------------
#|
is-value? term -> bool
Returns a boolean value indicating if the specified terms is a value of ISWIM
|#
(define (is-value? t)
  (define res (redex-match ISWIM-2 V t))
  (if res #t #f))


#|
eval: term -> Val (number, boolean,'function or 'stuck and in the cases apply-reduction-relation*
detects a reduction cycle: 'diverge)
|#
(define (eval t)
  (define results (apply-reduction-relation* s->v t))
  (if (= (length results) 0)
      ;case where apply-reduction-relation* detects a divergent term
      'diverge
      (let ([res (first results)])
        (match res
          [(list 'λ x b) 'function]
          [(? is-value?) res]
          [_ 'stuck]))))


#|
eval-by-steps: Term Int -> Term
Evals a term with a maximun of reductions steps. If the term does not reduce
after those steps is considered divergent 
|#
(define (eval-by-steps t [reductions 200])
  (define (eval-aux t curStep reductions) 
    (if (= curStep reductions)
        'diverge
        (let ([next-reduction-list (apply-reduction-relation s->v t)])
          (if (= (length next-reduction-list) 0)
              t
              (eval-aux (first next-reduction-list) (add1 curStep) reductions)))))

  (eval-aux t 0 reductions))

#|
eval-same?: term term term -> bool
Checks if two terms have the same result in the same context. This function
does not returns if one of the terms is divergent
|#
(define (eval-same? t1 t2 c)
  (define r1 (eval (plug c t1)))
  (define r2 (eval (plug c t2)))  
  (equal? r1 r2))


#|
eval-same-by-step?: term term term [Int] -> bool
Checks if two terms have the same result in the same context. This function
assumes that if a term consumes more than k reductions steps it is divergent
|#
(define (eval-same-by-steps? t1 t2 c [reductions 200]) 
  (define r1 (eval-by-steps (plug c t1) reductions))
  (define r2 (eval-by-steps (plug c t2) reductions))  
  (equal? r1 r2))



#|
check-equiv: term term -> boolean
Checks that two terms are equivalent (under observational equivalance) using
redex-check to plug the terms in some contexts. If one the terms diverge
the function does not stop
|#
(define (check-equiv t1 t2 [attempts 1000])
  (redex-check ISWIM-2 E (eval-same? t1 t2 (term E)) #:attempts attempts))

#|
check-equiv: term term [Int] -> boolean
Checks that two terms are equivalent (under observational equivalance) using
redex-check to plug the terms in some contexts. This function considers
that terms that needs more that k reductions steps are divergents. 

|#
(define (check-equiv-by-steps t1 t2 [reductions 100])
  (redex-check ISWIM-2 E (eval-same-by-steps? t1 t2 (term E) reductions)))