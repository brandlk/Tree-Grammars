#lang racket
(require "types.rkt")
(require redex)
(require test-engine/racket-tests)
(provide (all-defined-out))

(caching-enabled? #f)

(define-extended-language Simply-Typed Type
  (p (f ... e : t))
  (f (x param ... : res = e))
  (param x-t)
  (x-t (x : t))
  (res t)
  (e (x e ...) ; function application
     x         ; variable
     (c e ...) ; constructor application
     (match e : t caseexp caseexp ...)) ; match expression
  (caseexp (case pat -> e))
  (pat x
       (c pat ...)))

(define-extended-language Simply-Typed-Ev Simply-Typed
  (gamma (x-t ...))
  (P (f ... E : t))
  (E (x v ... E e ...)
     (c v ... E e ...)
     (match E : t (case pat -> e) ...)
     hole)
  (v (c v ...))
  (subst ((x ..._1) (v ..._1))))

(define (one-holds goals)
  (ormap (lambda (expr)
           (eval
            ((lambda (x)
               (quasiquote (judgment-holds (unquote (first x))
                                           (unquote-splicing (rest x)))))
             expr)))
         goals))

(define-term dummy-type (n (n (Blubb))))
(define-term t-zero (z (z (Zero))))
(define-term id-dummy-type (id (x : dummy-type) : dummy-type = x))
(define-term p1-dummy-type (p1 (x : dummy-type) (y : dummy-type) : dummy-type = x))
(define-term p2-dummy-type (p2 (x : dummy-type) (y : dummy-type) : dummy-type = y))
(define-term fun-blubb (blubb (x : dummy-type) (y : dummy-type) : t-zero = (Zero)))
(define-term fun-no-plus
  (no-plus (x : numbers1) : numbers2 =
           (match x : numbers1
             (case (Zero) -> (Zero))
             (case (Succ y) -> (Succ (no-plus y)))
             (case (Plus a b) -> (add-f (no-plus a) (no-plus b))))))
(define-term fun-add
  (add-f (x : numbers2) (y : numbers2) : numbers2 =
         (match x : numbers2
           (case (Zero) -> y)
           (case (Succ z) -> (add-f z (Succ y))))))

; has-fun
(check-expect
 (judgment-holds
  (has-fun (id-dummy-type
            (foo (y : dummy-type) : dummy-type = (Blubb))
            (Huha) : dummy-type)
           id))
 #t)
(check-expect
 (judgment-holds
  (has-fun ((id (y : dummy-type) : dummy-type = y) (Huha) : dummy-type)
           blubb))
 #f)
(define-judgment-form Simply-Typed-Ev
  #:mode (has-fun I I)
  #:contract (has-fun p x)
  [(has-fun (f_1 ... (x_1 param ... : t = e) f_2 ... e_2 : t) x_1)])

; fun : p x -> f
(check-expect
 (term (fun (id-dummy-type fun-blubb (Zero) : t-zero) blubb))
 (term fun-blubb))
(define-metafunction Simply-Typed-Ev
  fun : p x -> f
  [(fun (f_1 ... (name res (x_1 param ... : t = e_1)) f_2 ... e : t) x_1) res])

; params-typed : f -> (param ...)
(check-expect
 (term (params-typed fun-blubb))
 (term ((x : dummy-type) (y : dummy-type))))
(define-metafunction Simply-Typed-Ev
  params-typed : f -> (param ...)
  [(params-typed (x param ... : t = e)) (param ...)])

; params : f -> (x ...)
(check-expect
 (term (params fun-blubb))
 (term (x y)))
(define-metafunction Simply-Typed-Ev
  params : f -> (x ...)
  [(params f)
   (x ...)
   (where ((x : t) ...) (params-typed f))])

; body : f -> e
(check-expect
 (term (body fun-blubb))
 (term (Zero)))
(define-metafunction Simply-Typed-Ev
  body : f -> e
  [(body (x param ... : t = e)) e])

; res-type : f -> t
(check-expect
 (term (res-type fun-blubb))
 (term t-zero))
(define-metafunction Simply-Typed-Ev
  res-type : f -> t
  [(res-type (x param ... : t = e)) t])

(require redex/tut-subst)
; subst : (x ...) (v ...) e -> e
(define-metafunction Simply-Typed-Ev
  subst : (x ..._1) (v ..._1) e -> e
  [(subst (x ...) (v ...) e)
   ,(subst/proc x? (term (x ...)) (term (v ...)) (term e))])
(define x? (redex-match Simply-Typed x))



; domatch-t : t pat -> gamma
(define-judgment-form Simply-Typed-Ev
  #:mode (match-t I I O)
  #:contract (match-t pat t gamma)
  [(match-t pat t gamma)
   (where (gamma_1 gamma_2 ...) (match-t-coll pat t))
   (where gamma (fold-union-pointwise (gamma_1 gamma_2 ...)))])
;(check-expect
; (term (domatch-t numbers1 (Succ (Plus x y))))
; (term ((x : numbers1) (y : numbers1))))
;(define-metafunction Simply-Typed-Ev
;  domatch-t : t pat -> gamma
;  [(domatch-t (name t (start_1 prod_1 ...)) (c pat ...))
;   (union-many-gamma (gamma ... ...))
;   (where ((c_1 nonterm_1 ...) ...) (filter-matching-right (rights t start_1) (c pat ...)))
;   (where ((gamma ...) ...) (((domatch-t (nonterm_1 prod_1 ...) pat) ...) ...))
;   ]
;  [(domatch-t t x) ((x : t))])

; match-t-coll : pat t -> (gamma ...)
(check-expect
 (term
  (match-t-coll (C x) (s (s))))
 (term ()))
(check-expect
 (term
  (match-t-coll x numbers2))
 (term (((x : numbers2)))))
(check-expect
 (term
  (match-t-coll x (s (s))))
 (term ()))
(check-expect
 (term (match-t-coll x numbers2))
 (term (((x : numbers2)))))
(check-expect
 (term (match-t-coll x (n (n (Succ n)))))
 (term ()))
(check-expect
 (term (match-t-coll (C x y)
                     (s (s (C a b) (C d e))
                        (a (A))
                        (b (B))
                        (d (D))
                        (e (E)))))
 (term (((x : (a (s (C a b) (C d e))
                        (a (A))
                        (b (B))
                        (d (D))
                        (e (E))))
         (y : (b (s (C a b) (C d e))
                        (a (A))
                        (b (B))
                        (d (D))
                        (e (E)))))
        ((x : (d (s (C a b) (C d e))
                        (a (A))
                        (b (B))
                        (d (D))
                        (e (E))))
         (y : (e (s (C a b) (C d e))
                        (a (A))
                        (b (B))
                        (d (D))
                        (e (E))))))))
(check-expect
 (term (match-t-coll (C x)
                     (s (s (C s) (D) (C a))
                        (a))))
 (term (((x : (s (s (C s) (D) (C a))
                 (a)))))))
(define-metafunction Simply-Typed-Ev
  match-t-coll : pat t -> (gamma ...)
  [(match-t-coll x t)
   (((x : t)))
   (where #f ,(judgment-holds (empty t)))]
  [(match-t-coll x t)
   ()
   (judgment-holds (empty t))]
  [(match-t-coll (c pat ...) (name t (start prod ...)))
   (gamma_4 ... ...)
   (where ((c_1 nonterm_1 ...) ...) (filter-matching-right
                                     (rights t start)
                                     (c pat ...)))
   ;                      (                 )
   (where ((name one-rhs1 ((gamma_1 ...) ...)) ...) (((match-t-coll pat (nonterm_1 prod ...)) ...) ...))
   (where ((name one-rhs2 ((gamma_2 ...) ...)) ...) ((crossprod one-rhs1) ...))
   (where ((name one-rhs3 (gamma_3 ...)) ...) (((fold-intersect-pointwise (gamma_2 ...)) ...) ...))
   (where ((name one-rhs4 (gamma_4 ...)) ...) ((filter-valid-gamma (gamma_3 ...)) ...))])

; filter-valid-gamma : (gamma ...) -> (gamma ...)
(check-expect
 (term (filter-valid-gamma
        (((x : numbers2)) ((x : numbers2) (y : (s (s)))) ((z : numbers2)))))
 (term (((x : numbers2)) ((z : numbers2)))))
(define-metafunction Simply-Typed-Ev
  filter-valid-gamma : (gamma ...) -> (gamma ...)
  [(filter-valid-gamma ()) ()]
  [(filter-valid-gamma (gamma_1 gamma_2 ...))
   (cons gamma_1 (filter-valid-gamma (gamma_2 ...)))
   (judgment-holds (valid-gamma gamma_1))]
  [(filter-valid-gamma (gamma_1 gamma_2 ...))
   (filter-valid-gamma (gamma_2 ...))])

(define-judgment-form Simply-Typed-Ev
  #:mode (valid-gamma I)
  #:contract (valid-gamma gamma)
  [(valid-gamma ())]
  [(valid-gamma ((x_1 : t_1) (x_2 : t_2) ...))
   (where (#f) (,@(list (judgment-holds (empty t_1)))))
   (valid-gamma ((x_2 : t_2) ...))])

(define-metafunction Simply-Typed-Ev
  fold-union-pointwise : (gamma ...) -> gamma
  [(fold-union-pointwise ()) ()]
  [(fold-union-pointwise (gamma_1 gamma_2 ...))
   (union-pointwise gamma_1
                    (fold-union-pointwise (gamma_2 ...)))])

(define-metafunction Simply-Typed-Ev
  fold-intersect-pointwise : (gamma ...) -> gamma
  [(fold-intersect-pointwise ()) ()]
  [(fold-intersect-pointwise (gamma_1 gamma_2 ...))
   (intersect-pointwise gamma_1
                        (fold-intersect-pointwise (gamma_2 ...)))])

(define-metafunction Simply-Typed-Ev
  intersect-pointwise : gamma gamma -> gamma
  [(intersect-pointwise () gamma) gamma]
  [(intersect-pointwise ((x_1 : t_1a) (x_2 : t_2) ...)
                        ((x_3 : t_3) ... (x_1 : t_1b) (x_4 : t_4) ...))
   (intersect-pointwise ((x_2 : t_2) ...)
                        ((x_3 : t_3) ... (x_1 : (intersect t_1a t_1b)) (x_4 : t_4) ...))]
  [(intersect-pointwise ((x_1 : t_1) (x_2 : t_2) ...)
                        ((x_3 : t_3) ...))
   (intersect-pointwise ((x_2 : t_2) ...) ((x_1 : t_1) (x_3 : t_3) ...))])

(define-metafunction Simply-Typed-Ev
  union-pointwise : gamma gamma -> gamma
  [(union-pointwise () gamma) gamma]
  [(union-pointwise ((x_1 : t_1a) (x_2 : t_2) ...)
                    ((x_3 : t_3) ... (x_1 : t_1b) (x_4 : t_4) ...))
   (union-pointwise ((x_2 : t_2) ...)
                    ((x_3 : t_3) ... (x_1 : (union t_1a t_1b)) (x_4 : t_4) ...))]
  [(union-pointwise ((x_1 : t_1) (x_2 : t_2) ...)
                    ((x_3 : t_3) ...))
   (union-pointwise ((x_2 : t_2) ...) ((x_1 : t_1) (x_3 : t_3) ...))])

; crossprod : ((any ...) ...) -> ((any ...) ...)
(check-expect
 (term (crossprod ((a b c) (d e) (f))))
 (term ((a d f) (a e f) (b d f) (b e f) (c d f) (c e f))))
(define-metafunction Simply-Typed-Ev
  crossprod : ((any ...) ...) -> ((any ...) ...)
  [(crossprod ()) (())] ; todo: is this right????
  [(crossprod ((any_1 ...))) ((any_1) ...)]
  [(crossprod ((any_1 ...) (any_2 ...) ...))
   (concat ((crossprod1 any_1 any_res) ...))
   (where any_res (crossprod ((any_2 ...) ...)))])
  
(define-metafunction Simply-Typed-Ev
  crossprod1 : any ((any ...) ...) -> ((any ...) ...)
  [(crossprod1 any_1 ((any_2 ...) ...))
   ((any_1 any_2 ...) ...)])

; crossprod2 : (any ...) (any ...) -> ((any any) ...)
(check-expect
 (term (crossprod2 (a b c) (d e)))
 (term ((a d) (a e) (b d) (b e) (c d) (c e))))
(define-metafunction Simply-Typed-Ev
  crossprod2 : (any ...) (any ...) -> ((any any) ...)
  [(crossprod2 () (any ...)) ()]
  [(crossprod2 (any ...) ()) ()]
  [(crossprod2 (any_1 any_2 ...) (any_3 ...))
   (concat (((any_1 any_3) ...) (crossprod2 (any_2 ...) (any_3 ...))))])

(define-metafunction Simply-Typed-Ev
  union-gamma : gamma gamma -> gamma
  [(union-gamma () gamma) gamma]
  [(union-gamma ((x_1a : t_1a1) (x_2a : t_2a) ...) ((x_1b : t_1b) ... (x_1a : t_1a2) (x_3b : t_3b) ...))
   (union-gamma ((x_2a : t_2a) ...) ((x_1b : t_1b) ... (x_1a : (start_new (start_new right_1 ... right_2 ...) prod ...))
                                     (x_3b : t_3b) ...))
   (where start_new (gensym-t x_1a))
   (where (s prod ...) t_1a2)
   (where (right_1 ...) (rights t_1a1 (startsym t_1a1)))
   (where (right_2 ...) (rights t_1a2 (startsym t_1a2)))]
  [(union-gamma ((x_1 : t_1) (x_2 : t_2) ...) gamma)
   (union-gamma ((x_2 : t_2) ...) (cons (x_1 : t_1) gamma))])

(define-metafunction Simply-Typed-Ev
  union-many-gamma : (gamma ...) -> gamma
  [(union-many-gamma ()) ()]
  [(union-many-gamma (gamma)) gamma]
  [(union-many-gamma (gamma_1 gamma_2 ...))
   (union-gamma gamma_1 (union-many-gamma (gamma_2 ...)))])

; matches-t
(check-expect
 (judgment-holds
  (matches-t numbers1 (Succ (Plus x (Plus (Zero) y)))))
 #t)
(check-expect
 (judgment-holds
  (matches-t numbers1 (Succ x y)))
 #f)
(define-judgment-form Simply-Typed-Ev
  #:mode (matches-t I I)
  #:contract (matches-t t pat)
  [(matches-t t x)]
  [(matches-t (name t (start_1 prod_1 ...)) pat)
   ; ..._1 seems to work only within one pattern
   (where ((c pat_1 ..._1)
           (right_1 ... (c nonterm_1 ..._1) right_2 ...))
           (pat (rights t start_1)))
   (matches-t (nonterm_1 prod_1 ...) pat_1) ...])

; filter-matching : t (caseexp ...) -> (caseexp ...)
(check-expect
 (term
  (filter-matching numbers1 ((case (Succ (Succ (Plus x))) -> x)
                             (case (Zero) -> (Zero))
                             (case (Plus a (Succ (Zero))) -> a)
                             (case (Blubb) -> (Blubb)))))
 (term ((case (Zero) -> (Zero)) (case (Plus a (Succ (Zero))) -> a))))
(define-metafunction Simply-Typed-Ev
  filter-matching : t (caseexp ...) -> (caseexp ...)
  [(filter-matching t ()) ()]
  [(filter-matching t ((name case1 (case pat_1 -> e_1))
                       (name case2 (case pat_2 -> e_2)) ...))
   (cons case1 (filter-matching t (case2 ...)))
   (judgment-holds (matches-t t pat_1))]
  [(filter-matching t (caseexp_1 caseexp_2 ...))
   (filter-matching t (caseexp_2 ...))])


; matches-t-one
(check-expect
 (judgment-holds
  (matches-t-one numbers1
                 ((Succ a (Plus b))
                  (Zero)
                  (Blubb))))
 #t)
(check-expect
 (judgment-holds
  (matches-t-one numbers1
                 ((Blubb))))
 #f)
(define-judgment-form Simply-Typed-Ev
  #:mode (matches-t-one I I)
  #:contract (matches-t-one t (pat ...))
  [(matches-t-one t (pat_1 pat_2 ...))
   (matches-t t pat_1)]
  [(matches-t-one t (pat_1 pat_2 ...))
   (matches-t-one t (pat_2 ...))])

; domatch : v pat -> subst
(check-expect
 (term (domatch (Succ (Zero)) (Succ x)))
 (term ((x) ((Zero)))))
(define-metafunction Simply-Typed-Ev
  domatch : v pat -> subst
  [(domatch (c v ...) (c pat ...)) ,(conc_pairwise (term ((domatch v pat) ...)))]
  [(domatch v x) ((x) (v))])

; matches
(check-expect
 (judgment-holds
  (matches (Succ (Zero)) (Succ x)))
 #t)
(check-expect
 (judgment-holds
  (matches (Zero) (Succ x)))
 #f)
(define-judgment-form Simply-Typed-Ev
  #:mode (matches I I)
  #:contract (matches v pat)
  [(matches v x)]
  [(matches (c v ...) (c pat ...))
   (matches v pat) ...])


; vars : pat -> (x ...)
(check-expect
 (term (vars (Succ (Plus x (Plus x y)))))
 (term (x x y)))
(define-metafunction Simply-Typed-Ev
  vars : pat -> (x ...)
  [(vars x) (x)]
  [(vars (c pat ...))
   (concat ((vars pat) ...))])

; linear-pattern
(check-expect
 (judgment-holds
  (linear-pattern (Succ (Plus x y))))
 #t)
(check-expect
 (judgment-holds
  (linear-pattern (Succ (Plus x x))))
 #f)
(define-judgment-form Simply-Typed-Ev
  #:mode (linear-pattern I)
  #:contract (linear-pattern pat)
  [(linear-pattern pat)
   (all-different (vars pat))])


; all-different
(check-expect
 (judgment-holds
  (all-different (a b c d)))
 #t)
(check-expect
 (judgment-holds
  (all-different (a b a d)))
 #f)
(define-judgment-form Simply-Typed-Ev
  #:mode (all-different I)
  #:contract (all-different (any ...))
  [(all-different ())]
  [(all-different (any_1 any_2 ...))
   (contains-not any_1 (any_2 ...))
   (all-different (any_2 ...))])

(define (conc_pairwise l)
  (foldl 
   (lambda (x y)
     (list (append (first y) (first x))
           (append (second y) (second x))))
   (list null null)
   l))

; reduction relation for simply typed language
(define red
  (reduction-relation
   Simply-Typed-Ev
   #:domain p
   (--> (name prog (in-hole P (x v ...)))
        (in-hole P (subst (params (fun prog x))
                          (v ...)
                          (body (fun prog x))))
        (side-condition (judgment-holds (has-fun prog x)))
        F-APP)
   (--> (in-hole P (match v : t (case pat_1 -> e_1) (case pat -> e) ...))
        (in-hole P (subst (x_1 ...) (v_1 ...) e_1))
        (judgment-holds (matches v pat_1))
        (judgment-holds (linear-pattern pat_1))
        (where ((x_1 ...) (v_1 ...)) (domatch v pat_1))
        MATCH-T)
   (--> (in-hole P (match v : t (case pat_1 -> e_1) (case pat -> e) ...+))
        (in-hole P (match v : t (case pat -> e) ...))
        (side-condition (not (judgment-holds (matches v pat_1))))
        MATCH-F)))

(check-expect
 (apply-reduction-relation red term1)
 (term ((id-dummy-type p1-dummy-type p2-dummy-type (id (Blubb)) : dummy-type))))
(check-expect
 (apply-reduction-relation* red term1)
 (term ((id-dummy-type p1-dummy-type p2-dummy-type (Blubb) : dummy-type))))
(check-expect
 (apply-reduction-relation* red term2)
 (term (((Matched) : (t (t (Matched)))))))
(check-expect
 (apply-reduction-relation* red term3)
 (term (((GreaterZero) : (t (t (GreaterOne) (GreaterZero) (Zero)))))))

(define term1
  (term (id-dummy-type
         p1-dummy-type
         p2-dummy-type
         (id (id (Blubb))) : dummy-type)))

(define term2
  (term ((match (Zero) : (t (t (Zero)))
           (case (Zero) -> (Matched))) : (t (t (Matched))))))

(define term3
  (term ((match (Succ (Zero)) : numbers2
           (case (Succ (Succ x)) -> (GreaterOne))
           (case (Succ x)        -> (GreaterZero))
           (case x               -> (Zero))) : (t (t (GreaterOne) (GreaterZero) (Zero))))))

(define term4
  (term ((id (Zero)) : t-zero)))

(define term5
  (term ((match (Plus (Zero) (Succ (Zero))) : numbers1
           (case (Plus x x) -> (Twice x))
           (case y          -> y)) : (t (t (Zero) (Succ t) (Plus t t) (Twice t))))))

; bind-vars : gamma f -> gamma
(check-expect
 (term (bind-vars ((blubb : dummy-type))
                  p1-dummy-type))
 (term ((x : dummy-type) (y : dummy-type) (blubb : dummy-type))))
(define-metafunction Simply-Typed-Ev
  bind-vars : gamma f -> gamma
  [(bind-vars (x-t ...) (x_f param ... : t = e))
   (param ... x-t ...)])

; types
(check-expect
 (judgment-holds
  (types (x : dummy-type)))
 #f)
(check-expect
 (judgment-holds
  (types ,term1))
 #t)
(check-expect
  (judgment-holds
   (types ,term2))
  #t)
(check-expect
 (judgment-holds
  (types ,term3))
 #t)
(check-expect
 (judgment-holds
  (types ,term4))
 #f)
(check-expect
 (judgment-holds
  (types (fun-no-plus
          fun-add
          (no-plus (Plus (Zero) (Zero))) : numbers2)))
 #t)
(check-expect
 (judgment-holds
  (types (fun-no-plus
          fun-add
          (no-plus (Plus (Zero) (Zero))) : numbers1)))
 #t)
(check-expect
 (judgment-holds
  (types ((Plus (Zero) (Zero)) : numbers2)))
 #f)
(check-expect
 (judgment-holds
  (types ,term5))
 #f)
(check-expect
 (judgment-holds
  (types ((match (Zero) : numbers2
            (case (Zero)        -> (Zero))
            (case (Succ (Zero)) -> (Zero))) : numbers2)))
 #f)
(check-expect
 (judgment-holds
  (types ((match (Zero) : numbers2
            (case (Zero)        -> (Zero))
            (case (Succ x) -> x)) : numbers2)))
 #t)
(define-judgment-form Simply-Typed-Ev
  #:mode (types I)
  #:contract (types p)
  [(types (f_1 ... e_1 : t_1))
   (types-e (bind-vars () f_1) (f_1 ...) (body f_1) (res-type f_1)) ...
   (types-e () (f_1 ...) e_1 t_1)])

; types-e-one
(define-judgment-form Simply-Typed-Ev
  #:mode (types-e-one I I I I)
  #:contract (types-e-one gamma (f ...) (e ..._1) ((t ..._1) ...))
  [(types-e-one gamma (f ...) (e ...) ((t_1 ...) (t_2 ...) ...))
   (types-e gamma (f ...) e t_1) ...]
  [(types-e-one gamma (f ...) (e ...) ((t_1 ...) (t_2 ...) ...))
   (types-e-one gamma (f ...) (e ...) ((t_2 ...) ...))])

; types-e
(define-judgment-form Simply-Typed-Ev
  #:mode (types-e I I I I)
  #:contract (types-e gamma (f ...) e t)
  [(types-e gamma (f ...) e t)
   (infer-e gamma (f ...) e t_sub)
   (subtype t_sub t)])
;  ; base case
;  [(types-e ((x : t_1) x-t ...) (f ...) x t_2)
;   (subtype t_2 t_1)
;   (subtype t_1 t_2)]
;  ; weakening
;  [(types-e ((x_1 : t_1) x-t ...) (f ...) x_2 t_2)
;   (types-e (x-t ...) (f ...) x_2 t_2)
;   (where #t (different x_1 x_2))]
;  ; function application
;  [(types-e gamma
;            (name funs (f_1 ... (x (x_1 : t_1) ..._1 : t_res = e_body) f_2 ...))
;            (x e ..._1)
;            t)
;   (subtype t_res t)
;   (types-e gamma funs e t_1) ...]
;  ; constructor application
;  [(types-e gamma
;            (f ...)
;            (c_1 e_1 ...)
;            (start prod ...))
;   (where ((c nonterm_1 ...) ...) (filter-matching-right (rights (start prod ...) start) (c_1 e_1 ...)))
;   (types-e-one gamma (f ...) (e_1 ...) (((nonterm_1 prod ...) ...) ...))]
;;  ; pattern matching
;  [(types-e gamma
;            (f ...)
;            (match e_match : t_match (case pat_1 -> e_1) ...)
;            t)
;   (types-e gamma (f ...) e_match t_match)
;   (linear-pattern pat_1) ... ; each variable occurs only once
;   ;(matches-t t_match pat_1) ... ; each pattern matches values of the grammar
;   (match-t pat_1 t_match gamma_pat) ...
;   (empty (constrain-t-by-many-pat t_match (pat_1 ...))) ; the patterns are exhaustive
;   
;   ;(where (gamma_pat ...) ((domatch-t t_match pat_1) ...))
;   (types-e (concat (gamma_pat gamma))
;            (f ...)
;            e_1
;            t) ...])

; constrain-t-by-many-pat : t (pat ...) -> t
(check-expect
 (list?
  (redex-match
   Simply-Typed-Ev
   (nonterm_new2 (n (Zero) (Succ n))
                 (nonterm_new1 (Succ n))
                 (nonterm_new2 (Succ nonterm_new3))
                 (nonterm_new3 (Zero) (Succ nonterm_new4))
                 (nonterm_new4))
   (term (constrain-t-by-many-pat numbers2 ((Zero) (Succ (Succ x)))))))
 #t)
(define-metafunction Simply-Typed-Ev
  constrain-t-by-many-pat : t (pat ...) -> t
  [(constrain-t-by-many-pat t ()) t]
  [(constrain-t-by-many-pat t (pat_1 pat_2 ...))
   (constrain-t-by-many-pat
    (constrain-t-by-pat t pat_1)
    (pat_2 ...))])

; constrain-t-by-pat : t pat -> t
; computes a new grammer equivalent to the old one
; without all values covered by pat
(check-expect
 (list?
  (redex-match
   Simply-Typed-Ev
   (nonterm_new (n (Zero) (Succ n) (Plus n n))
                (nonterm_new (Succ n) (Plus n n)))
   (term (constrain-t-by-pat numbers1 (Zero)))))
 #t)
(check-expect
 (list?
  (redex-match
   Simply-Typed-Ev
   (nonterm_new1 (n (Zero) (Succ n) (Plus n n))
                 (nonterm_new1 (Zero) (Plus n n) (Succ nonterm_new2))
                 (nonterm_new2 (Zero) (Plus n n) (Succ nonterm_new3))
                 (nonterm_new3))
   (term (constrain-t-by-pat numbers1 (Succ (Succ x))))))
 #t)
(check-expect
 (list?
  (redex-match
   Simply-Typed-Ev
   (nonterm_new1 (s (C1 a b))
                 (a (C2) (C3))
                 (b (C4) (C5))
                 (nonterm_new1 (C1 nonterm_new2 b) (C1 a nonterm_new3))
                 (nonterm_new2 (C3))
                 (nonterm_new3 (C5)))
   (term (constrain-t-by-pat
          (s (s (C1 a b))
             (a (C2) (C3))
             (b (C4) (C5)))
          (C1 (C2) (C4))))))
 #t)
(define-metafunction Simply-Typed-Ev
  constrain-t-by-pat : t pat -> t
  [(constrain-t-by-pat (start prod ...) pat)
   (start_new prod ... prod_new ...)
   (where start_new (gensym-t start))
   (where (prod_new ...) (constrain-t-by-pat-h start (prod ...) pat start_new))])
   

; constrain-t-by-pat-h : start (prod_old ...) pat start_new -> (prod_new ...)
; computes a list of new productions so that
; (start_new prod_old ... prod_new) corresponds to (start prod_old) without
; all values covered by pat
(define-metafunction Simply-Typed-Ev
  constrain-t-by-pat-h : start (prod ...) pat start -> (prod ...)
  ; variable: all right hand sides are eliminated (variable matches any value)
  [(constrain-t-by-pat-h start_old (prod_old ...) x start_new)
   ((start_new))]
  ; constructor without arguments: elimintes all constuctors without arguments
  ; and the same name - no recursive call
  [(constrain-t-by-pat-h start_old (prod_old ...) (c) start_new)
   ((start_new right_non-matching ...))
   (where (right_non-matching ...)
          (filter-non-matching-right (rights (start_old prod_old ...) start_old) (c)))]
  ; constructor with arguments
  [(constrain-t-by-pat-h start_old (prod_old ...) (c pat ...) start_new)
   ((start_new right_non-matching ... (c nonterm_comb ...) ... ...) prod_new ... ... ...)
   ; matching right hand sides
   (where ((c_matching nonterm_matching ...) ...)
          (filter-matching-right (rights (start_old prod_old ...) start_old) (c pat ...)))
   ; non-matching right hand sides - these are copied into the new productions
   (where (right_non-matching ...)
          (filter-non-matching-right (rights (start_old prod_old ...) start_old) (c pat ...)))
   ; generate new names
   (where ((x ...) ...) (((gensym-t nonterm_matching) ...) ...))
   ; recurse
   (where (((prod_new ...) ...) ...) (((constrain-t-by-pat-h nonterm_matching (prod_old ...) pat x) ...) ...))
   (where (((nonterm_comb ...) ...) ...) ((combine-n (nonterm_matching ...) (x ...)) ...))])

; combine-n : (nonterm ...+) (nonterm ...+) -> ((nonterm ...) ...+)
(check-expect
 (term (combine-n (a b c d) (x1 x2 x3 x4)))
 (term ((x1 b c d) (a x2 c d) (a b x3 d) (a b c x4))))
(define-metafunction Simply-Typed-Ev
  combine-n : (nonterm ...+) (nonterm ...+) -> ((nonterm ...) ...+)
  [(combine-n (nonterm_1 ... nonterm_2) (x))
   ((nonterm_1 ... x))]
  [(combine-n (name n (nonterm_1a ... x_1 nonterm_1b ..._1)) (x_2 nonterm_2 ..._1))
   (cons (nonterm_1a ... x_2 nonterm_1b ...)
         (combine-n n (nonterm_2 ...)))])
   

;; covers
;(define-judgment-form Simply-Typed-Ev
;  #:mode (covers I I)
;  #:contract (covers (pat ...) t)
;  [(covers (pat ...) (name t (start prod ...)))
;   (where ((c nonterm ...) ...) (rights t start))
;   (where (((c pat_1 ...) (c pat_2 ...) ...) ...) ((filter-matching-patterns (pat ...) (c nonterm ...)) ...))])



; TODO:
; - exhaustiveness check: DONE
; - type inference
; - start the soundness proof: DONE
; - write thesis outline

;; types
;(check-expect
; (judgment-holds
;  (types () (x) any))
; #f)
;(check-expect
; (judgment-holds
;  (types ((x : (n (n (Zero))))) (x) (n (n (Zero)))))
; #t)
;(check-expect
; (judgment-holds
;  (types () ,term1
;         (n (n (Blubb)))))
; #t)
;(check-expect
;  (judgment-holds
;   (types () ,term2 (start (start (Matched)))))
;  #t)
;(check-expect
; (judgment-holds
;  (types () ,term3
;         (start (start (GreaterZero) (Zero))
;                (nonterm_1 (GreaterZero))
;                (nonterm_2 (Zero)))))
; #t)
;(check-expect
; (judgment-holds
;  (types () ,term4 any))
; #f)
;(check-expect
; (judgment-holds
;  (types () (fun-no-plus
;             fun-add
;             (no-plus (Plus (Zero) (Zero))))
;         (n (n (Zero) (Succ n)))))
; #t)
(define-judgment-form Simply-Typed-Ev
  #:mode (infer I I O)
  #:contract (infer gamma p t)
  [(infer gamma (f_1 ... e_1) t_1)
   (infer-e (bind-vars gamma f_1) (f_1 ...) (body f_1) t_res1) ...
   (subtype t_res1 (res-type f_1)) ...
   (infer-e gamma (f_1 ...) e_1 t_1)])

;; infer-e
(check-expect
 (judgment-holds
  (infer-e ((x : (s (s (Blubb))))) () x
           (s (s (Blubb)))))
 #t)
(check-expect
 (judgment-holds
  (infer-e () () x any))
 #f)
(check-expect
 (judgment-holds
  (infer-e ((x : (f (f (Zero)))) (y : (s (s (Blubb))))) () y
           (s (s (Blubb)))))
 #t)
(check-expect
 (judgment-holds
  (infer-e () () (Blubb)
           (nonterm (nonterm (Blubb)))))
 #t)
(check-expect
 (judgment-holds
  (infer-e ()
           ((id (x : (s (s (Blubb)))) : (s (s (Blubb))) = x))
           (id (Blubb))
           (s (s (Blubb)))))
 #t)
(check-expect
 (judgment-holds
  (infer-e ()
           ((id (x : (s (s (Blubb) (Bla)))) : (s (s (Blubb) (Bla))) = x))
           (id (Blubb))
           (s (s (Blubb) (Bla)))))
 #t)
(check-expect
 (judgment-holds
  (infer-e ()
           ((id (x : (n (n (Blubb)))) : (n (n (Blubb))) = x))
           (id (Bla))
           any))
 #f)
(check-expect
 (judgment-holds
  (infer-e () ()
           (Succ (Plus (Zero) (Zero)))
           (start_a (start_a (Succ start_b))
                    (start_b (Plus start_c start_d))
                    (start_c (Zero))
                    (start_d (Zero)))))
 #t)
(check-expect
 (judgment-holds
  (infer-e () ()
           (Succ (Plus (Zero) (Zero)))
           (start_a (start_a (Succ start_b))
                    (start_b (Plus start_c start_c))
                    prod ...)))
 #f)
(define-judgment-form Simply-Typed-Ev
  #:mode (infer-e I I I O)
  #:contract (infer-e gamma (f ...) e t)
  ; base case
  [(infer-e ((x : t_1) x-t ...) (f ...) x t_1)]
  ; weakening
  [(infer-e ((x_!_1 : t_1) x-t ...) (f ...) (name x_2 x_!_1) t_2)
   (infer-e (x-t ...) (f ...) x_2 t_2)]
;  ; function application
  [(infer-e gamma
            (name funs (f_1 ... (x (x_1 : t_1) ..._1 : t_res = e_body) f_2 ...))
            (x e ..._1)
            t_res)
   (infer-e gamma funs e t_1sub) ...
   (subtype t_1sub t_1) ...]
;  ; constructor application
  [(infer-e gamma
            (f ...)
            (c_1 e_1 ...)
            (start_fresh (start_fresh (c_1 start_1fresh ...)) prod_1fresh ... ...))
   (infer-e gamma (f ...) e_1 t_1) ...
   (where ((start_1fresh prod_1fresh ...) ...) ((rename-t t_1) ...))
   (where start_fresh (gensym-t foo))]
;  ; pattern matching, TODO: exhaustiveness check!
  [(infer-e gamma
            (f ...)
            (match e_match : t_match (case pat_1 -> e_1) ...)
            (union t_1 ...))
   (infer-e gamma (f ...) e_match t_match-inf)
   (subtype t_match-inf t_match)
   (match-t pat_1 t_match gamma_pat) ...
   (infer-e (concat (gamma_pat gamma))
            (f ...)
            e_1 t_1) ...
   (empty (constrain-t-by-many-pat t_match (pat_1 ...)))])
;   
;   (matches-t-one t_match (pat_1 ...))
;   (where ((case pat_matching -> e_matching) ...) (filter-matching t_match ((case pat_1 -> e_1) ...)))
;   (where (gamma_pat ...) ((domatch-t t_match pat_matching) ...))
;   (types-e (concat (gamma_pat gamma))
;            (f ...)
;            e_matching
;            t_1) ...])
;;   ; e_match type subtype of union of patterns
;;   ; result: union of e_1 types with binding of pattern variables
;;   ]
;
;(define (types? p)
;  (not (null?
;        (judgment-holds (types () ,p t) t))))
;
;(define v? (redex-match
;            Simply-Typed
;            (f ... v)))
;
;(define (reduces? p)
;  (not (null?
;        (apply-reduction-relation
;         red
;         p))))
;
;(define (progress-holds? p)
;  (if (types? p)
;      (or (v? p)
;          (reduces? p))
;      #t))

(define-metafunction Simply-Typed-Ev
  normalize-p : p -> p
  [(normalize-p (f ... e))
   ((normalize-f f) ... e)])

(define-metafunction Simply-Typed-Ev
  normalize-f : f -> f
  [(normalize-f (x_name (x : t) ... : t_res = e))
   (x_name (x : (normalize t)) ... : (normalize t_res) = e)])

;(test)