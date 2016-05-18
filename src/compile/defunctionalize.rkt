#lang typed/racket/base

(provide defunct-module)

(require racket/match
         (except-in racket/list remove-duplicates)
         (except-in racket/function arity-includes?)
         "../utils/main.rkt"
         "../ast/main.rkt"
         "../parse/main.rkt"
         "lib.rkt")

(: defunct-module : -module → (Values -module Closure-Table))
(define (defunct-module m)
  (match-define (-module l forms) m)

  ;; Table mapping each flat closure to compiled code
  (define clo-tab : Closure-Table (hash))

  (: defunct-module-level-form! : -module-level-form → -module-level-form)
  (define defunct-module-level-form!
    (match-lambda
      ;; Turn top-level lambda to regular function
      [(-define-values (list f) (-λ (? list? xs) e))
       (-define-values (list f)
                       (parameterize ([sym-prefix (format-symbol "Lam_~a" f)])
                         (-λ xs (defunct-e! e xs))))]
      [(-define-values (list x) e)
       (-define-values (list x)
                       (parameterize ([sym-prefix (format-symbol "Lam_~a" x)])
                         (defunct-e! e '())))]
      [(? -e? e) (defunct-e! e '())]
      [e
       (log-debug "defunct-module-level-form!: ignore ~a~n" (show-module-level-form e))
       e]))

  (: defunct-e! : -e (Listof Var-Name) → -e)
  ;; Compile expression to target, with side effect modifying the `apply` function
  (define (defunct-e! e fvs)
    (with-debugging/off
      ((e*)
       (match e
         [(or (? -x?) (? -𝒾?) (-b (or (? number?) (? null?) (? boolean?) (? keyword?)))) e]
         [(== -cons?) 'cons?]
         [(== -car) 'car]
         [(== -cdr) 'cdr]
         [(== -cons) 'cons]
         [(? symbol? o) o]
         [(? -prim? p) (error 'defunct-e! "not supporting primitive ~a for now~n" (show-e p))]
         [(-λ (? list? xs) e*)
          (define clo-name (next-sym!))
          (define fvs* (filter (set->predicate (fv e)) fvs))
          (defunct-clo! (Closure clo-name fvs*) xs e*)
          (-@ clo-name (map -x fvs*) (+ℓ!))]
         [(-@ f xs ℓ)
          (match f
            ;; Inline `λ` as `let` if possible
            [(-λ (? list? zs) e)
             (-let-values
              (for/list ([z zs] [x xs])
                (cons (list z) (defunct-e! x fvs)))
              (defunct-e! e (append/ignore-dups fvs zs)))]
            [_
             (-@ 'apply
                 (cons (defunct-e! f fvs) (for/list : (Listof -e) ([x xs]) (defunct-e! x fvs)))
                 ℓ)])]
         [(-if e₀ e₁ e₂)
          (-if (defunct-e! e₀ fvs) (defunct-e! e₁ fvs) (defunct-e! e₂ fvs))]
         [(-let-values bnds e)
          (define-values (xs bnds*)
            (for/lists ([xs : (Listof Var-Name)] [bnds* : (Listof (Pairof (Listof Var-Name) -e))])
                       ([bnd bnds])
              (match-define (cons (list x) e) bnd)
              (values x (cons (list x) (defunct-e! e fvs)))))
          (define e* (defunct-e! e (append/ignore-dups fvs xs)))
          (-let-values bnds* e*)]
         [(-begin es) (-begin (for/list : (Listof -e) ([e es]) (defunct-e! e fvs)))]))
      (printf "compile: ~a -> ~a~n" (show-e e) (show-e e*))))

  ;; Add a new clause of applying closure
  (: defunct-clo! : Closure (Listof Var-Name) -e → Void)
  (define (defunct-clo! clo xs e)
    (define e* (defunct-e! e (append/ignore-dups (Closure-free clo) xs)))
    (set! clo-tab (hash-set clo-tab clo (Rhs xs e*))))

  (define forms* (map defunct-module-level-form! forms))
  (values (-module l forms*) clo-tab))

(: test : Path-String → (Values Any Any))
(define (test p)
  (define-values (m clos) (defunct-module (file->module p)))
  (values (show-module m) clos))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(: append/ignore-dups (∀ (X) (Listof X) (Listof X) → (Listof X)))
(define (append/ignore-dups xs ys)
  (match xs
    ['() ys]
    [(cons x xs*)
     (cond [(member x ys) (append/ignore-dups xs* ys)]
           [else (cons x (append/ignore-dups xs* ys))])]))
