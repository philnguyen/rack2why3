#lang typed/racket/base

(provide compile-contract)

(require racket/match
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../parse/main.rkt"
         "lib.rkt")

(define-parameter current-prefix : Symbol 'gen)

(: compile-contract : -module → -module)
;; Compile away contract combinators down to wrappings and first-order checks
;; E.g.:
;; (module m
;;   (define (f x) e)
;;   (provide
;;     (contract-out
;;       [f (c → λz.d)])))
;; -->
;; (module m
;;   (define (f x)
;;     (let ([z mon⦃c,x⦄])
;;       mon⦃d, (f z)⦄)))
(define (compile-contract m)
  (match-define (-module l forms) m)

  (: maybe-mon-𝒾 : Symbol → -e)
  (define (maybe-mon-𝒾 x)
    (define 𝒾 (-𝒾 x l))
    (cond [(hash-ref x->c x #f) => (λ ([c : -e]) (mon-asrt c 𝒾))]
          [else 𝒾]))

  (: compile-e : -e → -e)
  (define compile-e
    (match-lambda
      [(-λ xs e) (-λ xs (compile-e e))]
      [(-𝒾 x (== l)) (maybe-mon-𝒾 x)]
      [(-@ f xs ℓ)
       (define (default) (-@ (compile-e f) (map compile-e xs) ℓ))
       (match f
         [(-𝒾 x (== l)) ; attempt to inline
          (cond
            [(hash-ref x->c x #f) =>
             (match-lambda
               [(--> doms rng _)
                (define chked-args : (Listof -e)
                  (for/list ([dom doms] [eₓ xs])
                    (mon-asrt dom (compile-e eₓ))))
                (mon-assm rng (-@ f chked-args ℓ))]
               [(-->i doms (-λ zs d) _)
                (define chked-args : (Listof -e)
                  (for/list ([dom doms] [eₓ xs])
                    (mon-asrt dom (compile-e eₓ))))
                (-let-values
                 (for/list ([z (assert zs list?)]
                            [arg chked-args])
                   (cons (list z) arg))
                 (mon-assm d (-@ f chked-args 0)))]
               [c (-@ (mon-asrt c f) (map compile-e xs) ℓ)])]
            [else (default)])]
         [_ (default)])]
      [(-if e e₁ e₂) (-if (compile-e e) (compile-e e₁) (compile-e e₂))]
      [(-set! x e) (error 'compile-e "TODO: set!")]
      [(-wcm k v b) (error 'compile-e "TODO: wcm")]
      [(-begin es) (-begin (map compile-e es))]
      [(-begin0 e es) (-begin0 (compile-e e) (map compile-e es))]
      [(-let-values bnds e)
       (define bnds* : (Listof (Pairof (Listof Var-Name) -e))
         (for/list ([bnd bnds])
           (match-define (cons xs e) bnd)
           (cons xs (compile-e e))))
       (define e* (compile-e e))
       (-let-values bnds* e*)]
      [(-letrec-values bnds e)
       (define bnds* : (Listof (Pairof (Listof Var-Name) -e))
         (for/list ([bnd bnds])
           (match-define (cons xs e) bnd)
           (cons xs (compile-e e))))
       (define e* (compile-e e))
       (-letrec-values bnds* e*)]
      [(-μ/c ℓ c) (error 'compile-e "TODO: μ/c")]
      [(--> doms rng ℓ)
       (--> (map compile-e doms) (compile-e rng) ℓ)]
      [(-->i doms (-λ zs d) ℓ)
       (-->i (map compile-e doms) (-λ zs (compile-e d)) ℓ)]
      [(-case-> clauses ℓ)
       (define clauses* : (Listof (Pairof (Listof -e) -e))
         (for/list ([clause clauses])
           (match-define (cons es e) clause)
           (cons (map compile-e es) (compile-e e))))
       (-case-> clauses* ℓ)]
      [(-struct/c s cs ℓ)
       (-struct/c s (map compile-e cs) ℓ)]
      [e e]))

  (define x->c : (HashTable Var-Name -e) (map/hash compile-e (provides m)))

  (define forms* : (Listof -module-level-form)
    (for/list ([form forms])
      (match form
        [(-define-values (list f) e)
         (define (default) (-define-values (list f) (compile-e e)))
         
         (parameterize ([current-prefix (assert f symbol?)])
           (match e
             [(-λ xs e*)
              (cond
                [(hash-ref x->c f #f) =>
                 (match-lambda
                   [(--> doms rng _)
                    (define chked-args : (Listof -e)
                      (for/list ([dom doms] [x (assert xs list?)])
                        (mon-assm dom (-x x))))
                    (define body
                      (-let-values
                       (for/list ([x (assert xs list?)] [chked-arg chked-args])
                         (cons (list x) chked-arg))
                       (mon-asrt rng (compile-e e*))))
                    (-define-values (list f) (-λ xs body))]
                   [(-->i doms (-λ zs rng) _)
                    (define chked-args : (Listof -e)
                      (for/list ([dom doms] [x (assert xs list?)])
                        (mon-assm dom (-x x))))
                    (define body
                      (-let-values
                       (for/list ([z (assert zs list?)] [chked-arg chked-args])
                         (cons (list z) chked-arg))
                       (mon-asrt rng (compile-e e*))))
                    (-define-values (list f) (-λ xs body))]
                   [_ (default)])]
                [else form])]
             [_ (default)]))]
        [(? -e? e) (compile-e e)]
        [_ form])))

  (-module l forms*))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(:* mon-asrt mon-assm : -e -e → -e)
(define (mon-asrt c e) (mon #t c e))
(define (mon-assm c e) (mon #f c e))

(: mon : Boolean -e -e → -e)
(define (mon asrt? c e)
  (define -exn (if asrt? -bad -ok))
  (:* -asrt/assm -asrt/assm/not : -e -e → -e)
  (define (-asrt/assm c e)
    (-begin
     (list (-@ (if asrt? 'assert 'assume)
               (list c e)
               0)
           e)))
  (define (-asrt/assm/not c e)
    (-begin
     (list (-@ (if asrt? 'assert-not 'assume-not)
               (list c e)
               0)
           e)))

  (: mon-args : Boolean (Listof -e) (Listof Var-Name) → (Listof -e))
  (define (mon-args asrt? doms xs)
    (for/list ([dom doms] [x (assert xs list?)])
      (mon asrt? dom (-x x))))

  (: bind : (Listof Var-Name) (Listof -e) → (Listof (Pairof (Listof Var-Name) -e)))
  (define (bind xs es)
    (for/list ([x xs] [e es])
      (cons (list x) e)))

  (match c
    [(--> doms rng _)
     (match e
       [(-λ xs e*)
        (-λ xs
            (-let-values
             (bind (assert xs list?) (mon-args (not asrt?) doms (assert xs list?)))
             (mon asrt? rng e*)))]
       [(? simpl?)
        (define xs : (Listof Var-Name) (for/list ([_ doms])
                                         (next-sym! (format-symbol "x_~a" (current-prefix)))))
        (-begin
         (list
          (-@ (if asrt? 'assert 'assume) (list 'procedure? e) 0)
          (-λ xs
              (-let-values
               (bind (assert xs list?) (mon-args (not asrt?) doms (assert xs list?)))
               (-begin
                (list
                 (-@ 'assume (list 'procedure? e) 0)
                 (mon asrt? rng (-@ e (map -x xs) 0))))))))]
       [_
        (define x (next-sym! (format-symbol "h_~a" (current-prefix))))
        (define 𝐱 (-x x))
        (define xs : (Listof Var-Name) (for/list ([_ doms]) (next-sym! (format-symbol "x_~a" (current-prefix)))))
        (-let-values
         (list (cons (list x) e))
         (-begin
          (list
           (-@ (if asrt? 'assert 'assume) (list 'procedure? 𝐱) 0)
           (-λ xs
               (-let-values
                (bind (assert xs list?) (mon-args (not asrt?) doms (assert xs list?)))
                (-begin
                 (list
                  (-@ 'assume (list 'procedure? 𝐱) 0)
                  (mon asrt? rng (-@ 𝐱 (map -x xs) 0)))))))))])]
    [(-->i doms (-λ zs rng) _)
     (match e
       [(-λ xs e*)
        (-λ xs
            (-let-values
             (bind (assert zs list?) (mon-args (not asrt?) doms (assert xs list?)))
             (mon asrt? rng e*)))]
       [(? simpl?)
        (-begin
         (list
          (-@ (if asrt? 'assert 'assume) (list 'procedure? e) 0)
          (-λ zs
              (-let-values
               (bind (assert zs list?) (mon-args (not asrt?) doms (assert zs list?)))
               (-begin
                (list
                 (-@ 'assume (list 'procedure? e) 0)
                 (mon asrt? rng (-@ e (map -x (assert zs list?)) 0))))))))]
       [_
        (define x (next-sym! (format-symbol "h_~a" (current-prefix))))
        (define 𝐱 (-x x))
        (-let-values
         (list (cons (list x) e))
         (-begin
          (list
           (-@ (if asrt? 'assert 'assume) (list 'procedure? 𝐱) 0)
           (-λ zs
               (-let-values
                (bind (assert zs list?) (mon-args (not asrt?) doms (assert zs list?)))
                (-begin
                 (list
                  (-@ 'assume (list 'procedure? 𝐱) 0)
                  (mon asrt? rng (-@ 𝐱 (map -x (assert zs list?)) 0)))))))))])]
    [(-@ (-𝒾 'and/c 'Λ) cs _)
     (for/fold ([acc : -e e]) ([c cs])
       (mon asrt? c acc))]
    #;[(-@ (-𝒾 'or/c 'Λ) (list c d) _) ; assume c is flat
     ]
    [(-𝒾 'any/c 'Λ) e]
    [(-@ (-𝒾 'not/c 'Λ) (list c*) _)
     (cond
       [(simpl? e)
        (match c*
          [(or (? symbol? o) (-𝒾 (? symbol? o) 'Λ)) #:when o
           (-asrt/assm/not o e)]
          [_ (-if (-@ c* (list e) 0) -exn e)])]
       [else
        (define x (next-sym! (format-symbol "n_~a" (current-prefix))))
        (-let-values
         (list (cons (list x) e))
         (match c*
           [(or (? symbol? o) (-𝒾 (? symbol? o) 'Λ)) #:when o
            (-asrt/assm/not o e)]
           [_ (-if (-@ c* (list x) 0) -exn (-x x))]))])]
    [_
     (cond
       [(simpl? e)
        (match c
          [(or (? symbol? o) (-𝒾 (? symbol? o) 'Λ)) #:when o
           (-asrt/assm o e)]
          [_ (-if (-@ c (list e) 0) e -exn)])]
       [else
        (define x (next-sym! (format-symbol "f_~a" (current-prefix))))
        (define 𝐱 (-x x))
        (-let-values
         (list (cons (list x) e))
         (match c
           [(or (? symbol? o) (-𝒾 (? symbol? o) 'Λ)) #:when o
            (-asrt/assm o 𝐱)]
           [_ (-if (-@ c (list 𝐱) 0) 𝐱 -exn)]))])]))

(: provides : -module → (HashTable Var-Name -e))
;; Collect exported contract for each identifier
(define (provides m)
  (match-define (-module _ es) m)
  (for*/hash : (HashTable Var-Name -e) ([e es] #:when (-provide? e)
                                        [p/c (-provide-specs e)])
    (match-define (-p/c-item x c _) p/c)
    (values x c)))
