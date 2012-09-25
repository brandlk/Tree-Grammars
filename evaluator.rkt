#lang racket

(require "simply-typed.rkt")
(require redex)
(require test-engine/racket-tests)

; simple arithmetic expressions
(define-term arith-expr1
  (ae (ae (Zero) (Succ ae) (Plus ae ae))))

(define-term maybe-val
  (mv (mv (None) (Just n))
      (n (Zero) (Succ n))))

(define-term numbers
  (n (n (Zero) (Succ n))))

; evaluator for simple arithmetic expressions
; this evaluation cannot go wrong, since all syntactically correct terms
; of the embedded langauge are also 'well typed'
(define-term f-eval-arith1
  (eval-arith1 (x : arith-expr1) : numbers
               = (match x : arith-expr1
                   (case (Zero)     -> (Zero))
                   (case (Succ y)   -> (Succ (eval-arith1 y)))
                   (case (Plus y z) -> (plus (eval-arith1 y) (eval-arith1 z))))))

; evaluates number + number
(define-term f-plus
  (plus (x : numbers) (y : numbers) : numbers
        = (match x : numbers
            (case (Zero) -> y)
            (case (Succ x1) -> (plus x1 (Succ y))))))

; test program for eval-arith1
; this program typchecks
(define-term e-arith1
  (Succ (Plus (Succ (Succ (Zero))) (Plus (Succ (Zero)) (Succ (Succ (Zero)))))))
(check-expect
 (judgment-holds
  (types prog-arith1))
 #t)
(define-term prog-arith1
  (f-eval-arith1
   f-plus
   (eval-arith1 e-arith1) : numbers))

; arithmetic expressions containing also Pred
(define-term arith-expr2
  (ae (ae (Zero) (Succ ae) (Pred ae))))

; evaluator for arithmetic expressions with Pred
; this evaluator can only be implemented by a
; partial function, since we can only compute the predessesor
; of a positive number!
; But the fact that the evaluator is partial can be seen in the
; result type.
(define-term f-eval-arith2
  (eval-arith2 (x : arith-expr2) : maybe-val
               = (match x : arith-expr2
                   (case (Zero) -> (Just (Zero)))
                   (case (Succ y) -> (match (eval-arith2 y) : maybe-val
                                       (case (None)   -> (None))
                                       (case (Just z) -> (Just (Succ z)))))
                   (case (Pred y) -> (match (eval-arith2 y) : maybe-val
                                       (case (Just (Succ z)) -> (Just z))
                                       (case z               -> (None)))))))

; test program for arithmetic expressions with Pred
(define-term e-arith21
  (Pred (Succ (Zero))))
(define-term e-arith22
  (Succ (Pred (Zero))))
(check-expect
 (judgment-holds
  (types prog-arith21))
 #t)
(define-term prog-arith21
  (f-eval-arith2
   (eval-arith2 e-arith21) : maybe-val))
(check-expect
 (judgment-holds
  (types prog-arith22))
 #t)
(define-term prog-arith22
  (f-eval-arith2
   (eval-arith2 e-arith22) : maybe-val))

; could we define a total evaluator for arithmetic expressions
; with pred by designing a better grammar?


; expressions containing boolean and arithmetic operations
(define-term b-arith-expr
  (bae (bae (True) (False) (If bae bae bae)
            (Zero) (Succ bae) (Pred bae) (IsZero bae))))
(define-term maybe-bae-val
  (m-bae-val (m-bae-val (None) (Just bae-val))
             (bae-val (Zero) (Succ n) (True) (False))
             (n (Zero) (Succ n))))

; evaluator for b-arith expressions
; partial function, because not all syntactically valid
; terms in the embedded language make sense (we could write
; something like (If (Zero) (Zero) (Zero))
(define-term f-eval-bae
  (eval-bae (x : b-arith-expr) : maybe-bae-val
            = (match x : b-arith-expr
                (case (Zero)              -> (Just (Zero)))
                (case (True)              -> (Just (True)))
                (case (False)             -> (Just (False)))
                (case (If test then else) -> (match (eval-bae test) : maybe-bae-val
                                               (case (Just (True))  -> (eval-bae then))
                                               (case (Just (False)) -> (eval-bae else))
                                               (case y              -> (None))))
                (case (Succ y)            -> (match (eval-bae y) : maybe-bae-val
                                               (case (None)          -> (None))
                                               (case (Just (True))   -> (None))
                                               (case (Just (False))  -> (None))
                                               (case (Just (Zero))   -> (Just (Succ (Zero))))
                                               (case (Just (Succ z)) -> (Just (Succ (Succ z))))))
                (case (Pred y)            -> (match (eval-bae y) : maybe-bae-val
                                               (case (Just (Succ z)) -> (Just (Succ z)))
                                               (case z               -> (None))))
                (case (IsZero y)          -> (match (eval-bae y) : maybe-bae-val
                                               (case (Just (Zero))   -> (Just (True)))
                                               (case (Just (Succ z)) -> (Just (False)))
                                               (case z               -> (None)))))))
; test program for eval-bae
(define-term e-bae
  (If (IsZero (Zero))
      (Zero)
      (If (True) (Succ (Zero)) (Pred (Succ (Zero))))))
(check-expect
 (judgment-holds
  (types p-bae))
 #t)
(define-term p-bae
  (f-eval-bae
   (eval-bae e-bae)  : maybe-bae-val))


; in the case of b-arith expressions we can design a better
; grammar allowing only well typed terms: we define two classes
; of terms: terms of number type and terms of boolean type.
; and then the set of all expressions is defined as the
; union of these two classes

(define-term bae-prods (bae (True) (False) (And be be) (IsZero ae) (Zero) (Succ ae) (Plus ae ae) (If be be be) (If be ae ae)))
(define-term ae-prods (ae (Zero) (Succ ae) (Plus ae ae) (If be ae ae)))
(define-term be-prods (be (True) (False) (And be be) (IsZero ae) (If be be be)))
(define-term better-bae
  (bae bae-prods
       ae-prods
       be-prods))
(define-term better-bae-ae
  (ae bae-prods
      ae-prods
      be-prods))
(define-term better-bae-be
  (be bae-prods
      ae-prods
      be-prods))
(define-term be-val
  (be (be (True) (False))))


(define-term t-bae-val
  (bae-val (bae-val (Zero) (Succ n) (True) (False))
           (n (Zero) (Succ n))))

; a total evaluator for the better version of b-arith expressions
; the evaluator uses the two help-functions eval-be and eval-ae for
; evaluating expressions of the two subclasses of terms respectively
(check-expect (list? (redex-match Simply-Typed f (term f-eval-better-bae))) #t)
(define-term f-eval-better-bae
  (eval-bae (x : better-bae) : t-bae-val
            = (match x : better-bae
                (case (True)     -> (eval-be (True)))
                (case (False)    -> (eval-be (False)))
                (case (Zero)     -> (eval-ae (Zero)))
                (case (And y z)  -> (eval-be (And y z)))
                (case (IsZero y) -> (eval-be (IsZero y)))
                (case (Succ y)   -> (eval-ae (Succ y)))
                (case (Plus y z) -> (eval-ae (Plus y z)))
                (case (If test then else) -> (match (eval-be test) : be-val
                                               (case (True) -> (eval-bae then))
                                               (case (False) -> (eval-bae else)))))))

; evaluator for boolean expressions
(check-expect (list? (redex-match Simply-Typed f (term f-eval-be))) #t)
(define-term f-eval-be
  (eval-be (x : better-bae-be) : be-val
           = (match x : better-bae-be
               (case (True)     -> (True))
               (case (False)    -> (False))
               (case (And y z)  -> (and (eval-be y) (eval-be z)))
               (case y          -> (False))
               (case (IsZero y) -> (match (eval-ae y) : numbers
                                     (case (Zero) -> (True))
                                     (case z      -> (False))))
               (case (If test then else) -> (match (eval-be test) : be-val
                                              (case (True) -> (eval-be then))
                                              (case (False) -> (eval-be else)))))))

; evaluator for arithmetic expressions
(check-expect (list? (redex-match Simply-Typed f (term f-eval-ae))) #t)
(define-term f-eval-ae
  (eval-ae (x : better-bae-ae) : numbers
           = (match x : better-bae-ae
               (case (Zero) -> (Zero))
               (case (Succ y) -> (Succ (eval-ae y)))
               (case (Plus y z) -> (plus (eval-ae y) (eval-ae z)))
               (case (If test then else) -> (match (eval-be test) : be-val
                                              (case (True) -> (eval-ae then))
                                              (case (False) -> (eval-ae else)))))))

; note that we have to duplicate the code evaluating an If-expression
; to all three functions -> can we abstract over that in some way as
; to only write the common parts once?

(check-expect (list? (redex-match Simply-Typed f (term f-and))) #t)
(define-term f-and
  (and (x : be-val) (y : be-val) : be-val
       = (match x : be-val
           (case (False) -> (False))
           (case (True)  -> y))))
           
(define-term e-better-bae
  (If (And (IsZero (Zero)) (IsZero (Succ (Zero))))
      (Plus (Succ (Zero)) (Succ (Zero)))
      (Zero)))

(check-expect (list? (redex-match Simply-Typed p (term p-better-bae))) #t)
(check-expect (judgment-holds (types p-better-bae)) #t)
(define-term p-better-bae
  (f-and
   f-eval-be
   f-eval-ae
   f-plus
   f-eval-better-bae
   (Zero) : numbers))

(test)