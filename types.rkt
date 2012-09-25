#lang racket
(require redex)
(require test-engine/racket-tests)
(provide (all-defined-out))

(caching-enabled? #f)

(define-language Type
  (x (side-condition
      (name x_1 variable-not-otherwise-mentioned)
      (char-lower-case?
       (string-ref (symbol->string (term x_1)) 0))))
  (c (side-condition
      (name x_1 variable-not-otherwise-mentioned)
      (char-upper-case?
       (string-ref (symbol->string (term x_1)) 0))))
  (raw-t (start raw-prod ...))
  (t (start prod ...))
  (start x)
  (nonterm x)
  (raw-prod (nonterm raw-right ...))
  (prod (nonterm right ...))
  (raw-right nonterm
             (c nonterm ...))
  (right (c nonterm ...)))
       

(define-term numbers1
   (n (n (Zero) (Succ n) (Plus n n))))
(define-term numbers2
   (n (n (Zero) (Succ n))))
(define-term deep1
  (t (t (Zero) x (Plus t t) (Succ x))
     (x t (Blubb))))
(define-term deep1-closure
  (t (t (Zero) (Plus t t) (Succ x) (Blubb))
     (x (Blubb) (Zero) (Plus t t) (Succ x))))
(define-term deep2
  (t (t (Zero)) (t x) (t (Plus t t)) (t (Succ x))
     (x t) (x (Blubb))))

(check-expect
 (list?
  (redex-match
   Type t (term numbers1)))
 #t)
(check-expect
 (list?
  (redex-match
   Type t (term numbers2)))
 #t)
(check-expect
 (list?
  (redex-match
   Type raw-t (term deep1)))
 #t)
(check-expect
 (redex-match
  Type t (term deep1))
 #f)

; contains
(check-expect
 (judgment-holds (contains a (a b c)))
 #t)
(check-expect
 (judgment-holds (contains d (a b c)))
 #f)
(define-judgment-form Type
  #:mode (contains I I)
  #:contract (contains any (any ...))
  [(contains any_1 (any_2 ... any_1 any_3 ...))])

; contains-not
(check-expect
 (judgment-holds (contains-not a (a b c)))
 #f)
(check-expect
 (judgment-holds (contains-not d (a b c)))
 #t)
(define-judgment-form Type
  #:mode (contains-not I I)
  #:contract (contains-not any (any ...))
  [(contains-not any_1 ())]
  [(contains-not any_1 (any_2 any_3 ...))
   (where #t (different any_1 any_2))
   (contains-not any_1 (any_3 ...))])

; add : any ... (any ...) -> (any ...)
(check-expect
 (term (add a (a b c)))
 (term (a b c)))
(check-expect
 (term (add d (a b c)))
 (term (d a b c)))
(define-metafunction Type
  add : any ... (any ...) -> (any ...)
  [(add (any_2 ...)) (any_2 ...)]
  [(add any_1 ... any_2 (any_3 ...))
   (add any_1 ... (any_3 ...))
   (judgment-holds (contains any_2 (any_3 ...)))]
  [(add any_1 ... any_2 (any_3 ...))
   (add any_1 ... (any_2 any_3 ...))])

; different : any any -> #t or #f
(check-expect
 (term (different a b))
 (term #t))
(check-expect
 (term (different a a))
 (term #f))
(define-metafunction Type
  different : any any -> #t or #f
  [(different any_1 any_1) #f]
  [(different any_1 any_2) #t])

; cons : any (any ...) -> (any ...)
(check-expect
 (term (cons a (b c d)))
 (term (a b c d)))
(define-metafunction Type
  cons : any (any ...) -> (any ...)
  [(cons any_1 (any_2 ...)) (any_1 any_2 ...)])

; concat : ((any ...) ...) -> (any ...)
(check-expect
 (term (concat ((a b c) (d e f))))
 (term (a b c d e f)))
(check-expect
 (term (concat (() (x))))
 (term (x)))
(define-metafunction Type
  concat : ((any ...) ...) -> (any ...)
  [(concat ((any_1 ...) ...)) (any_1 ... ...)])

; lookup : any ((any any) ...) -> any
(check-expect
 (term (lookup a ((x y) (a b) (c d))))
 (term b))
(define-metafunction Type
  lookup : any ((any any) ...) -> any
  [(lookup any_key ((any_1 any_2) ... (any_key any_val) (any_3 any_4) ...)) any_val])

; without : (any ...) (any ...) -> (any ...)
(check-expect
 (term (without (a b c) (c)))
 (term (a b)))
(define-metafunction Type
  without : (any ...) (any ...) -> (any ...)
  [(without (any_1 ...) ()) (any_1 ...)]
  [(without (any_1 ... any_2 any_3 ...) (any_2 any_4 ...))
   (without (any_1 ... any_3 ...) (any_4 ...))]
  [(without (any_1 ...) (any_2 any_3 ...))
   (without (any_1 ...) (any_3 ...))])

; nonterms: raw-t -> (nonterm ...)
; all nonterminals with a corresponding production in the grammar
(check-expect
 (term (nonterms numbers1))
 (term (n)))
(define-metafunction Type
  nonterms : raw-t -> (nonterm ...)
  [(nonterms (start (nonterm raw-right ...) ...)) (add nonterm ... ())])

; mentioned-nonterms : raw-t -> (nonterm ...)
; the start symbol and all nonterminal used in a right hand side of a production
(check-expect
 (term (mentioned-nonterms deep1))
 (term (x t)))
(define-metafunction Type
  mentioned-nonterms : raw-t -> (nonterm ...)
  [(mentioned-nonterms (start (nonterm_1 raw-right_1 ...) ...))
   (add start (mentioned-nonterms-h (raw-right_1 ... ...)))])

(define-metafunction Type
  mentioned-nonterms-h : (raw-right_1 ...) -> (nonterm ...)
  [(mentioned-nonterms-h ()) ()]
  [(mentioned-nonterms-h (nonterm_1 raw-right_1 ...))
   (add nonterm_1 (mentioned-nonterms-h (raw-right_1 ...)))]
  [(mentioned-nonterms-h ((c_1 nonterm_1 ...) raw-right_1 ...))
   (add nonterm_1 ... (mentioned-nonterms-h (raw-right_1 ...)))])

; startsym: raw-t -> start
(check-expect
 (term (startsym numbers1))
 (term n))
(define-metafunction Type
  startsym : raw-t -> start
  [(startsym (start raw-prod ...)) start])

; rights: raw-t nonterm -> (raw-right ...)
(check-expect
 (term (rights numbers1 n))
 (term ((Zero) (Succ n) (Plus n n))))
(define-metafunction Type
  rights : raw-t nonterm -> (raw-right ...)
  [(rights
    (start (nonterm_1 raw-right_1 ...) ... (nonterm_2 raw-right_2 ...) (nonterm_3 raw-right_3 ...) ...)
    nonterm_2)
   (raw-right_2 ...)])

; filter-nonterm: (raw-right ...) -> (nonterm ...)
(check-expect
 (term (filter-nonterm ((Zero) x a (Succ n) n)))
 (term (x a n)))
(define-metafunction Type
  filter-nonterm : (raw-right ...) -> (nonterm ...)
  [(filter-nonterm ()) ()]
  [(filter-nonterm ((c any ...) raw-right ...))
   (filter-nonterm (raw-right ...))]
  [(filter-nonterm (nonterm raw-right ...))
   (cons nonterm (filter-nonterm (raw-right ...)))])

; filter-c: (raw-right ...) -> (right ...)
(check-expect
 (term (filter-c ((Zero) x a (Succ n) n)))
 (term ((Zero) (Succ n))))
(define-metafunction Type
  filter-c : (raw-right ...) -> (right ...)
  [(filter-c ()) ()]
  [(filter-c ((c nonterm ...) raw-right ...))
   (cons (c nonterm ...) (filter-c (raw-right ...)))]
  [(filter-c (nonterm raw-right ...))
   (filter-c (raw-right ...))])

; closure1: raw-t nonterm (nonterm ...) -> (right ...)
(check-expect
 (term (closure1 deep1 t ()))
 (term ((Zero) (Plus t t) (Succ x) (Blubb))))
(define-metafunction Type
  closure1 : raw-t nonterm (nonterm ...) -> (right ...)
  [(closure1 raw-t nonterm_1 (nonterm ...)) ()
   (side-condition (member (term nonterm_1)
                           (term (nonterm ...))))]
  [(closure1 raw-t nonterm_1 (nonterm ...))
   ((c nonterm_c ...) ... right_new ... ...)
   (where (raw-right ...) (rights raw-t nonterm_1))
   (where (nonterm_new ...) (filter-nonterm (raw-right ...)))
   (where ((c nonterm_c ...) ...) (filter-c (raw-right ...)))
   (where ((right_new ...) ...) ((closure1 raw-t nonterm_new (nonterm_1 nonterm ...)) ...))])

; closure: raw-t -> t
(check-expect
 (term (closure deep1))
 (term deep1-closure))
(define-metafunction Type
  closure : raw-t -> t
  [(closure (name t (start (nonterm raw-right ...) ...)))
   (start (nonterm_1 right_closure ...) ...)
   (where ((nonterm_1 (right_closure ...)) ...) ((nonterm (closure1 t nonterm ())) ...))])
           


; collapse-prods: raw-t -> raw-t
; takes a t with sorted! productions
; collapses multiple productions with the same nonterminal into one
(check-expect
 (term
  (collapse-prods (n (n (Zero)) (n (Succ n)) (n (Plus n n)))))
 (term numbers1))
(define-metafunction Type
  collapse-prods : raw-t -> raw-t
  [(collapse-prods (start raw-prod ...))
   (start raw-prod_new ...)
   (where (raw-prod_new ...) (collapse-prods-h (raw-prod ...)))])
(define-metafunction Type
  collapse-prods-h : (raw-prod ...) -> (raw-prod ...)
  [(collapse-prods-h ((nonterm_1 raw-right_1a ...)
                      (nonterm_1 raw-right_1b ...)
                      (nonterm_2 raw-right_2 ...) ...))
   (collapse-prods-h ((nonterm_1 ,@(append (term (raw-right_1a ...)) (term (raw-right_1b ...))))
                      (nonterm_2 raw-right_2 ...) ...))]
  [(collapse-prods-h ((nonterm_1 raw-right_1 ...)
                      (nonterm_2 raw-right_2 ...) ...))
   (cons (nonterm_1 raw-right_1 ...) (collapse-prods-h ((nonterm_2 raw-right_2 ...) ...)))]
  [(collapse-prods-h ()) ()])

      
; sort-prods: raw-t -> raw-t
; sort productions by nonterminal
(check-expect
 (term
  (sort-prods (n (n) (x) (a) (f))))
 (term (n (a) (f) (n) (x))))
(define-metafunction Type
  sort-prods : raw-t -> raw-t
  [(sort-prods (start raw-prod ...))
   (start ,@(sort (term (raw-prod ...))
                 (lambda (x y)
                   (string<? (symbol->string x) (symbol->string y)))
                 #:key first))])

; add-empty-prods : raw-t -> raw-t
(check-expect
 (term
  (add-empty-prods numbers1))
 (term numbers1))
(check-expect
 (term
  (add-empty-prods (t)))
 (term (t (t))))
(check-expect
 (term
  (add-empty-prods (t (t (Foo x y)) (x (Zero)))))
 (term (t (t (Foo x y)) (x (Zero)) (y))))
(define-metafunction Type
  add-empty-prods : raw-t -> raw-t
  [(add-empty-prods (name t (start_1 raw-prod_1 ...)))
   (start_1 raw-prod_1 ... (nonterm_missing) ...)
   (where (nonterm_missing ...)
          (without (mentioned-nonterms t)
                   (nonterms t)))])

;; clean-grammar : t -> t
;; eliminated 'dead' branches and non-reachable nonterminals
;(define-metafunction Type
;  clean-grammar : t -> t
;  [(clean-grammar t)
;   (delete-non-reachable (delete-dead t))])
;
;(define-metafunction Type
;  delete-dead : t -> t
;  [(delete-dead ())
;   (where (nonterm_empty ...) (empty-prods t))

; normalize: raw-t -> t
; normalizing:
; - collapse multiple productions for the same nonterminal (done)
;   -> first sort the list!
; - compute closure for all nonterminals
; - add missing productions
(check-expect
 (term (normalize deep2))
 (term deep1-closure))
(check-expect
 (term (normalize (t (t (Foo x y)) (x (Zero)))))
 (term (t (t (Foo x y)) (x (Zero)) (y))))
(define-metafunction Type
  normalize : raw-t -> t
  [(normalize raw-t) (closure (add-empty-prods (collapse-prods (sort-prods raw-t))))])

; subtype
(check-expect
 (judgment-holds
  (subtype (normalize numbers2) (normalize numbers1)))
 #t)
(check-expect
 (judgment-holds
  (subtype (normalize numbers1) (normalize numbers2)))
 #f)
(check-expect
 (judgment-holds
  (subtype (start (start (X start))) (normalize numbers1)))
 #t)
; TODO: testcase should work, but does not atm
; e.g. subtyping is not complete...
;(check-expect
; (judgment-holds
;  (subtype numbers1
;           (t (t (Zero) (Succ t1) (Succ t2) (Plus t3 t3))
;              (t1 (Succ t4))
;              (t4 (Blubb) (Zero) (Succ t3) (Plus t3 t3))
;              (t2 (Zero)))))
; #t)
(define-judgment-form Type
  #:mode (subtype I I)
  #:contract (subtype t t)
  [(subtype t_1 t_2)
   (empty t_1)]
  [(subtype t_1 t_2)
   (subtype-h t_1 t_2 ())])

; subtype-h
(check-expect
 (judgment-holds
  (subtype-h (n) (m) ((n m))))
 #t)
(check-expect
 (judgment-holds
  (subtype-h (normalize numbers2) (normalize numbers1) ()))
 #t)
(check-expect
 (judgment-holds
  (subtype-h (normalize numbers1) (normalize numbers2) ()))
 #f)
(define-judgment-form Type
  #:mode (subtype-h I I I)
  #:contract (subtype-h t t ((nonterm nonterm) ...))
  [(subtype-h (start_1 prod_1 ...)
              (start_2 prod_2 ...)
              any_seen)
   (contains (start_1 start_2) any_seen)]
  [(subtype-h (name t_1 (start_1 prod_1 ...))
              (name t_2 (start_2 prod_2 ...))
              any_seen)
   (contains-not (start_1 start_2) any_seen)
   (where (right_1 ...) (rights t_1 start_1))
   (where (right_2 ...) (rights t_2 start_2))
   (match-prod right_1 (right_2 ...) ((x_subgoal1 x_subgoal2) ...)) ...
   (where ((x_sub1 x_sub2) ...) (concat (((x_subgoal1 x_subgoal2) ...) ...)))
   (subtype-h (x_sub1 prod_1 ...) (x_sub2 prod_2 ...) (cons (start_1 start_2) any_seen)) ...])

;; constrain-t-by-t
;(define-metafunction Type
;  constrain-t-by-t : t t (((nonterm nonterm) nonterm) ...) -> (t (((nonterm nonterm) nonterm) ...))
;  [(constrain-t-by-t (start_1 prod_1 ...) (start_2 prod_2 ...)
;                     (((nonterm_1a nonterm_1b) nonterm_1ab) ...
;                      ((start_1 start_2) nonterm_12)
;                      ((nonterm_2a nonterm_2b) nonterm_2ab) ...))
;   (nonterm_12)]
;  [(constrain-t-by-t (name t_1 (start_1 prod_1 ...)) (name t_2 (start_2 prod_2 ...)) (any_seen ...))
;   ((start_new prod_new (start_new (c_non-matched) ...
;   (where start_new (gensym-t (start_1 start_2)))
;   (where (right_1 ...) (rights start_1 t_1))
;   (where (right_2 ...) (rights start_2 t_2))
;   ; constant values
;   (where ((c_constant-1) ...) (filter-constant-right (right_1 ...)))
;   (where ((c_constant-2) ...) (filter-constant-right (right_2 ...)))
;   ; non-constant right sides
;   (where (right_non-constant-1 ...) (without (right_1 ...) ((c_constant-1) ...)))
;   (where (right_non-constant-2 ...) (without (right_2 ...) ((c_constant-2) ...)))
;   (where ((c_non-matched) ...) (without ((c_constant-1) ...) ((c_constant-2) ...)))
;   
;   ; pair each right side of t1 with corresponding right sides of t2
;   (where (((c_1 nonterm_1 ..._1) ((c_2 nonterm_2 ..._1) ...)) ...)
;          ((right_non-constant-1 (filter-matching-right (right_non-constant-2 ...) right_non-constant-1)) ...))
;   (where ((start_news ...) (prod_new ...) any_seen_new)
;          (constrain-many-t-by-many-t (nonterm_1 ...) ((nonterm_2 ...) ...) (prod_1 ...) (prod_2 ...) (((start_1 start_2) start_new) any_seen ...)))])
;
;(define-metafunction Type
;  [(constrain-many-t-by-many-t
;    (nonterm_1 ...) () (prod_1 ...) (prod_2 ...) any_seen)
;   (((nonterm_1 ...) (prod_1 ...) any_seen))]
;  [(constrain-many-t-by-many-t
;    (nonterm_1 ...) ((nonterm_2 ...) (nonterm_3 ...) ...) (prod_1 ...) (prod_2 ...) any_seen)
;   (constrain-many-t-by-many-t (start_new ...) ((nonterm_3 ...) ...) (prod_1 ... 
;   (where ((start_new1 ...) (prod_new ...) any_seen-new) (constrain-many-t-by-t ((nonterm_1 nonterm_2) ...) (prod_1 ...) (prod_2 ...) any_seen))
;   (where ((start_new2
;  
;  ))])
;
;(define-metafunction Type
;  constrain-many-t-by-t : ((nonterm nonterm) ...) (prod ...) (prod ...) (((nonterm nontem) nonterm) ...) -> ((nonterm ...) (prod ...) (((nonterm nonterm) nonterm) ...))
;  [(constrain-many-t-by-t
;    ((nonterm_1 nonterm_2)) (prod_1 ...) (prod_2 ...) any_seen)
;   ((start_new) (prod_new ...) any_new)
;   (where ((start_new prod_new ...) any_new) (constrain-t-by-t (nonterm_1 prod_1 ...) (nonterm_2 prod_2 ...) any_seen))]
;  [(constrain-many-t-by-t
;    ((nonterm_1 nonterm_2) (nonterm_1a nonterm_2a) ...) (prod_1 ...) (prod_2 ...) any_seen)
;   ((start_new1 start_new2 ...) (prod_new2 ...) any_seen_new2)
;  (where ((start_new1 prod_new1 ...) any_seen_new1) (constrain-t-by-t (nonterm_1 prod_1 ...) (nonterm_2 prod_2 ...) any_seen))
;  (where ((start_new2 ...) (prod_new2 ...) any_seen_new2) (constrain-many-t-by-t ((nonterm_1a nonterm_2a) ...) (prod_new1 ...) (prod_2 ...) any_seen_new1))])
;   


; filter-constant-right : (right ...) -> ((c) ...)
(check-expect
 (term (filter-constant-right
        ((Zero) (Succ a) (Plus b c) (Blubb) (Succ x) (Bar))))
 (term ((Zero) (Blubb) (Bar))))
(define-metafunction Type
  filter-constant-right : (right ...) -> ((c) ...)
  [(filter-constant-right ()) ()]
  [(filter-constant-right ((c) right ...))
   (cons (c) (filter-constant-right (right ...)))]
  [(filter-constant-right (right_1 right_2 ...))
   (filter-constant-right (right_2 ...))])

; filter-matching-right : (right ...) (c any ...) -> (right ...)
(check-expect
 (term (filter-matching-right
        ((Zero) (Succ a b) (Blubb x y) (Succ a b c) (Succ u v))
        (Succ x y)))
 (term ((Succ a b) (Succ u v))))
(define-metafunction Type
  filter-matching-right : (right ...) (c any ...) -> (right ...)
  [(filter-matching-right () (c any ...)) ()]
  [(filter-matching-right ((c nonterm_1 ..._1) right ...) (c any ..._1))
   (cons (c nonterm_1 ...) (filter-matching-right (right ...) (c any ...)))]
  [(filter-matching-right ((c_1 nonterm_1 ...) right ...) (c_2 any ...))
   (filter-matching-right (right ...) (c_2 any ...))])

; filter-non-matching-right: (right ...) (c any ...) -> (right ...)
(check-expect
 (term (filter-non-matching-right
        ((Zero) (Succ a b) (Blubb x y) (Succ a b c) (Succ u v))
        (Succ x y)))
 (term ((Zero) (Blubb x y) (Succ a b c))))
(define-metafunction Type
  filter-non-matching-right : (right ...) (c any ...) -> (right ...)
  [(filter-non-matching-right () (c any ...)) ()]
  [(filter-non-matching-right ((c nonterm_1 ..._1) right ...) (c any ..._1))
   (filter-non-matching-right (right ...) (c any ...))]
  [(filter-non-matching-right ((c_1 nonterm_1 ...) right ...) (c_2 any ...))
   (cons (c_1 nonterm_1 ...) (filter-non-matching-right (right ...) (c_2 any ...)))])

; match-prod
(check-expect
 (judgment-holds
  (match-prod (Succ a b c) ((Zero) (Succ x y z)) any)
  any)
 (term (((a x) (b y) (c z)))))
(check-expect
 (judgment-holds
  (match-prod (Zero) ((Blubb) (Bla a b c)) any))
 #f)
(define-judgment-form Type
  #:mode (match-prod I I O)
  #:contract (match-prod right (right ...) ((nonterm nonterm) ...))
  [(match-prod (c_1 nonterm_1a ..._1)
               ((c_2 nonterm_2 ...) ...
                (c_1 nonterm_1b ..._1)
                (c_3 nonterm_3 ...) ...)
               ((nonterm_1a nonterm_1b) ...))])

; union : t ... -> t
(check-expect
 (list?
  (redex-match
   Type
   (start_fresh (start_fresh (Zero) (Foo) (Bar))
                (nonterm_n1 (Zero))
                (nonterm_n2 (Foo))
                (nonterm_n3 (Bar)))
   (term (union (a (a (Zero))) (b (b (Foo))) (c (c (Bar)))))))
 #t)
(check-expect
 (list?
  (redex-match
   Type
   (start_fresh (start_fresh (Zero) (Succ nonterm_n1) (Plus nonterm_n1 nonterm_n1)
                             (Zero) (Succ nonterm_n2))
                (nonterm_n1 (Zero) (Succ nonterm_n1) (Plus nonterm_n1 nonterm_n1))
                (nonterm_n2 (Zero) (Succ nonterm_n2)))
   (term (union numbers1 numbers2))))
 #t)
(define-metafunction Type
  union : t ... -> t
  [(union t_1) t_1]
  [(union t_1 ...)
   (normalize (start_fresh (start_fresh start_1 ...) prod_1 ... ...))
   (where start_fresh ,(gensym))
   (where ((start_1 prod_1 ...) ...) ((rename-t t_1) ...))])

; todo!!! implementation is missing
(define-metafunction Type
  intersect : t ... -> t
  [(intersect t ...) (s (s))])

; gensym-t : any -> x
; does not work together with caching...
(define-metafunction Type
  gensym-t : any -> x
  [(gensym-t any) ,(gensym)])

; rename-t : t -> t
(check-expect
 (list?
  (redex-match
   Type
   (start_fresh (start_fresh (Zero) (Plus start_fresh start_fresh) (Succ nonterm_n1) (Blubb))
                (nonterm_n1 (Blubb) (Zero) (Plus start_fresh start_fresh) (Succ nonterm_n1)))
   (term (rename-t deep1-closure))))
 #t)
(define-metafunction Type
  rename-t : t -> t
  [(rename-t t_1)
   (rename t_1 ((nonterm_1 (gensym-t nonterm_1)) ...))
   (where (nonterm_1 ...) (nonterms t_1))])

; rename : t ((nonterm nonterm) ...) -> t
(check-expect
 (term (rename numbers1 ((n x))))
 (term (x (x (Zero) (Succ x) (Plus x x)))))
(define-metafunction Type
  rename : t ((nonterm nonterm) ...) -> t
  [(rename (start (nonterm_1 right_1 ...) ...) (name map any))
   ((lookup start map) ((lookup nonterm_1 map) (rename-right right_1 map) ...) ...)])

; rename-right : right ((nonterm nonterm) ...) -> right
(check-expect
 (term
  (rename-right (Plus t t) ((t x))))
 (term (Plus x x)))
(define-metafunction Type
  rename-right : right ((nonterm nonterm) ...) -> right
  [(rename-right nonterm_1 (name map any))
   (lookup nonterm_1 map)]
  [(rename-right (c_1 nonterm_1 ...) (name map any))
   (c_1 (lookup nonterm_1 map) ...)])

; empty
(check-expect
 (judgment-holds (empty numbers1))
 #f)
(check-expect
 (judgment-holds
  (empty (x (x (Succ x)))))
 #t)
(define-judgment-form Type
  #:mode (empty I)
  #:contract (empty t)
  [(empty t_1)
   (empty-h t_1 ())])

; empty-h
(check-expect
 (judgment-holds (empty-h numbers1 ()))
 #f)
(check-expect
 (judgment-holds
  (empty-h (x (x (Succ x))) ()))
 #t)
(define-judgment-form Type
  #:mode (empty-h I I)
  #:contract (empty-h t (nonterm ...))
  [(empty-h (start_1 prod_1 ...) any_seen)
   (contains start_1 any_seen)]
  [(empty-h (name t_1 (start_1 prod_1 ...)) any_seen)
   (contains-not start_1 any_seen)
   (where ((c_1 nonterm_1 ...) ...) (rights t_1 start_1))
   (one-empty (nonterm_1 ...) (prod_1 ...) (cons start_1 any_seen)) ...])

(check-expect
 (judgment-holds
  (one-empty (x y z) ((x (Succ x)) (y (Zero)) (z (Blubb))) ()))
 #t)
(check-expect
 (judgment-holds
  (one-empty () () ()))
 #f)
(check-expect
 (judgment-holds
  (one-empty (x y) ((x (Zero)) (y (Zero))) ()))
 #f)
(define-judgment-form Type
  #:mode (one-empty I I I)
  #:contract (one-empty (nonterm ...) (prod ...) (nonterm ...))
  [(one-empty (nonterm_1 nonterm ...) (prod_1 ...) any_seen)
   (empty-h (nonterm_1 prod_1 ...) any_seen)]
  [(one-empty (nonterm_1 nonterm_2 ...) (prod_1 ...) any_seen)
   (one-empty (nonterm_2 ...) (prod_1 ...)  any_seen)])

; TODO:
; - normalize types, DONE
; - union, DONE
; - subtyping, DONE
; - checking for empty type DONE

;(test)