#lang play
(require redex)
(require "typed-iswim.rkt")


#|
well-typed?:: Term -> Boolean
Checks if a term of ISWIM-2 is well typed
|#
(define (well-typed? t)
  (judgment-holds (types () ,t T)))

#|
progress: Well-Typed-Term -> Boolean
Checks either a term is a (value or error) or it reduces
|#
(define (progress? t)
  (or (or (is-value? t) (equal? t (term (err "error in δ"))))
      (= (length (apply-reduction-relation s->v->err t)) 1)))

#|
preservation:: Well-Typed-Term -> Boolean
Preservation Theorem: If Γ ⊢ t : T and t → t', then Γ ⊢ t' : T .
|#
(define (preservation? t)
  (define reductions (apply-reduction-relation s->v->err t))
  (or (= (length reductions) 0)
      (let* ([type-t (judgment-holds (types () ,t T) T)]  
             [t1 (first reductions)])
        ;this check is to avoid errors, if the t reduces t1, where t1 is not error, then the check is not needed
        (or (equal? t1 (term (err "error in δ")))
            (equal? type-t (judgment-holds (types () ,t1 T) T))))))


#|
well-typed-terms:: [attemps] -> List(Well-Typed-Term)
Returns a list of well typed random terms
|#
(define (well-typed-terms [attempts 10000])
  (define terms (list))
  (redex-check ISWIM-2 M ((λ(t)
                             (begin
                               (set! terms (cons t terms))                               
                               #t)) (term M)) #:attempts attempts)
   (filter well-typed? terms))

#|
random-test:: (Term -> Bool) -> Void
Verify that either well-typed random terms satifies the predicate or not.
|#
(define (random-test pred)
  (define index 0)
  (define fail #t)
  (define terms (well-typed-terms))
  (define result (andmap (λ(x)
            (if (pred x)
                #t
                (begin (set! fail x)
                       (set! index (add1 index))
                       #f))) terms))
  (if result
      (displayln (format "no counterexamples ~a found" (length terms)))
      (begin (displayln (format "found couterexamples after ~a" index))             
             (displayln fail))))

;I found the redex-generator funtion which could be useful to generate well-typed-terms
;but I didn't play enought with it.
#;(define gen-term (redex-generator ISWIM-2+Γ (types Γ M_1 T) 20))


;-----------------------------------------------------------
;RANDOM TESTS

;Check progress
(random-test progress?)
(random-test preservation?)
;-----------------------------------------------------------