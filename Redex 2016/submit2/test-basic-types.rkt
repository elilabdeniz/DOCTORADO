#lang play
(require redex)
(require "typed-iswim.rkt")

;---------------------------------------------------------------------------
;BASIC TEST
;INT
(test-equal
 (judgment-holds
  (types () 1 T) T)
  '(INT))

;t-var
(test-equal
(judgment-holds
  (types ((x : INT)) x T) T)
  '(INT))

(test-equal
(judgment-holds
  (types ((x : INT)) X_2 T) T)
  '())

;t-abs
(test-equal
(term (extend ([x : INT]) x BOOL))
'((x : BOOL)))

(test-equal
(judgment-holds
  (types () (λ x : INT x) T) T)
'((→ INT INT)))


(test-equal
(judgment-holds
  (types () (λ x : INT (λ x : BOOL x)) T) T)
'((→ INT (→ BOOL BOOL))))
  

;t-app
(test-equal
(judgment-holds
  (types ()
         ((λ x : INT (λ x : BOOL x)) 1) T) T)
'((→ BOOL BOOL)))
 

(test-equal
(judgment-holds
  (types () ((λ x : INT (λ x : BOOL x)) #t) T) T)
'())
  
;t-if
(test-equal
(judgment-holds
  (types () (if (λ x : INT x) 1 2)  T) T)
  '())

(test-equal 
 (judgment-holds
  (types () (+ 1 (if 1 1 1)) T) T)
 '())

(test-equal
(judgment-holds
  (types () (if ((λ x : BOOL x) #t) 1 2)  T) T)
  '(INT))

;P1
(test-equal
(judgment-holds
  (types () ((λ f : (→ INT INT) (f 0)) (λ g : INT g)) T) T)
  '(INT))


;---------------------------------------------------------------------------
;PRIMITIVE OPERATORS
;---------------------------------------------------------------------------
;+
(test-equal
(judgment-holds
  (types () (+ 1 1) T) T)
  '(INT))

(test-equal
(judgment-holds
  (types () (+ 1 #f) T) T)
  '())

;-
(test-equal
(judgment-holds
  (types () (- 1 1) T) T)
  '(INT))

;/
(test-equal
(judgment-holds
  (types () (/ 1 1) T) T)
  '(INT))

;*
(test-equal
(judgment-holds
  (types () (* 1 1) T) T)
  '(INT))

;<
(test-equal
(judgment-holds
  (types () (< 1 1) T) T)
  '(BOOL))

;and
(test-equal
(judgment-holds
  (types () (and #t #f) T) T)
  '(BOOL))

;or
(test-equal
(judgment-holds
  (types () (or #t #f) T) T)
  '(BOOL))

;not
(test-equal
(judgment-holds
  (types () (not #t) T) T)
  '(BOOL))

;sub1
(test-equal
(judgment-holds
  (types () (sub1 1) T) T)
  '(INT))

;add1
(test-equal
(judgment-holds
  (types () (add1 1) T) T)
  '(INT))

(test-equal
(judgment-holds
  (types () (add1 #f) T) T)
  '())

;iszero
(test-equal
(judgment-holds
  (types () (iszero 1) T) T)
  '(BOOL))

(test-equal
(judgment-holds
  (types () (iszero #t) T) T)
  '())

;---------------------------------------------------------------------------
;PAIR
;---------------------------------------------------------------------------

;pair
(test-equal
(judgment-holds
  (types () (pair 1 #t) T) T)
  '((INT * BOOL)))

;fst
(test-equal
(judgment-holds
  (types () (fst (pair 1 #t)) T) T)
  '(INT))

;snd
(test-equal
(judgment-holds
  (types () (snd (pair 1 #t)) T) T)
  '(BOOL))

;fst
(test-equal
(judgment-holds
  (types () (fst (pair (λ x : INT x) (pair 1 1))) T) T)
  '((→ INT INT)))

;snd
(test-equal
(judgment-holds
  (types () (snd (pair (λ x : INT x) (pair 1 1))) T) T)
  '((INT * INT)))

;---------------------------------------------------------------------------
;SUM
;---------------------------------------------------------------------------

;inl
(test-equal
(judgment-holds
  (types () (inl 1 (INT + BOOL)) T) T)
  '((INT + BOOL)))

;inr
(test-equal
(judgment-holds
  (types () (inr #f (INT + BOOL)) T) T)
  '((INT + BOOL)))

;case
(test-equal 
 (judgment-holds
  (types () (case (inl 1 (INT + INT)) of 
              (inl X => X) 
              (inr Y => Y)) T) T)
 '(INT))

;case
(test-equal 
 (judgment-holds
  (types () (case (inr 1 (INT + INT)) of 
              (inl X => X) 
              (inr Y => Y)) T) T)
 '(INT))

;case
(test-equal 
 (judgment-holds
  (types () (case (inl 1 (INT + BOOL)) of 
              (inl X => X) 
              (inr Y => 1)) T) T)
 '(INT))
;case
(test-equal 
 (judgment-holds
  (types () (case (inl 1 (INT + BOOL)) of 
              (inl X => X) 
              (inr Y => X)) T) T)
 '())


;-----------------------------------------
;SOME EXTRA TEST
;-----------------------------------------
(test-equal 
 (judgment-holds
  (types () (snd (pair (add1 0) 0)) T) T)
 '(INT))


;------------------------------------------
;ERRORS
;------------------------------------------
;case 1: Error has type bottom (⊥)
(test-equal 
 (judgment-holds
  (types () (err "unknow") T) T)
 '(⊥))

;case 2: Error can be argument of a primitive of two arguments
(test-equal 
 (judgment-holds
  (types () (- (err "unknow") 1) T) T)
 '(INT))

;case 3: Error can be argument of a primitive of one argument
(test-equal 
 (judgment-holds
  (types () (sub1 (err "unknow")) T) T)
 '(INT))

;case 3: Error can be condition of a if
(test-equal 
 (judgment-holds
  (types () (+ 1 (if (err "unknow") 2 1)) T) T)
 '(INT))

;case 3: Error can be condition of a if
(test-equal 
 (judgment-holds
  (types () (+ 1 (if #f (err "unknow") 1)) T) T)
 '(INT))

;case 3: Error can be condition of a if
(test-equal 
 (judgment-holds
  (types () (+ 1 (if #f 1 (err "unknow"))) T) T)
 '(INT))

;case 4: Case and error
(test-equal 
 (judgment-holds
  (types () (case (inl 1 (INT + INT)) of 
              (inl X => (err "unknow")) 
              (inr Y => Y)) T) T)
 '(INT))

(test-equal 
 (judgment-holds
  (types () (case (inl 1 (INT + INT)) of 
              (inl X => X) 
              (inr Y => (err "unknow"))) T) T)
 '(INT))


;------------------------------------------
;LET/CC TEST
;------------------------------------------
;case 1;
(test-equal 
 (judgment-holds
  (types () (+ 1 (let/cc : INT k (k 1))) T) T)
 '(INT))

;case 2
(test-equal 
 (judgment-holds
  (types () (and #t (let/cc : INT k (k 1))) T) T)
 '())

;case 3. We  call the continuation were a value is expected
(test-equal 
 (judgment-holds
  (types () (+ 1 (let/cc : INT k (+ 1 (k 1)))) T) T)
 '(INT))
(test-equal 
 (judgment-holds
  (types () (and #f (let/cc : BOOL k (iszero (k #f)))) T) T)
 '(BOOL))

;case 4. We can call continuation inside a IF
(test-equal 
 (judgment-holds
  (types () (and #t ((λ n : INT 
                      (let/cc : BOOL k (if (iszero n)
                                          (k #f)
                                          #t))) 0)) T) T)
 '(BOOL))

(test-equal 
 (judgment-holds
  (types () (and #t ((λ n : INT 
                      (let/cc : BOOL k (and #t (if (iszero n)
                                          (k #f)
                                          #t)))) 0)) T) T)
 '(BOOL))


(test-results)