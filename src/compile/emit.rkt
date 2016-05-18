#lang typed/racket/base

(provide emit)

(require racket/match
         racket/string
         racket/set
         (except-in racket/list remove-duplicates)
         "../utils/main.rkt"
         "../ast/main.rkt"
         "lib.rkt")

(require/typed racket/base
  [hash-empty? (Closure-Table → Boolean)])

(: indent : String → String)
(define (indent s) (string-append "  " s))

(: with-indent : (U String (Listof String)) * → (Listof String))
(define (with-indent . ss)
  (match ss
    ['() '()]
    [(cons sᵢ ss*)
     (define rst (apply with-indent ss*))
     (cond [(string? sᵢ) (cons (indent sᵢ) rst)]
           [else (append (map indent sᵢ) rst)])]))

(: emit : -module Closure-Table  → (Listof String))
(define (emit m clo-tab)
  (match-define (-module l forms) m)
  
  ;; Declaure closures
  (define declare-values : (Listof String)
    (list*
     "type v ="
     "| Nil"
     "| Cons v v"
     "| N int"
     "| B bool"
     "(* generated lambdas *)"
     (for/list : (Listof String) ([clo (in-hash-keys clo-tab)])
       (match-define (Closure k xs) clo)
       (string-join
        (cons (symbol->string k)
              (for/list : (Listof String) ([_ xs]) "v"))
        #:before-first "| "))))

  ;; Primitive functions
  (define define-primitives : (Listof String)
    `(
      "(** Type predicates *)"
      "predicate is_Nil (v: v) = match v with"
      "| Nil -> True"
      "| _ -> False"
      "end"
      "predicate is_Cons (v: v) = match v with"
      "| Cons _ _ -> True"
      "| _ -> False"
      "end"
      "predicate is_List (v: v) = match v with"
      "| Nil -> True"
      "| Cons _ t -> is_List t"
      "| _ -> False"
      "end"
      "predicate is_N (v: v) = match v with"
      "| N _ -> True"
      "| _ -> False"
      "end"
      "predicate is_B (v: v) = match v with"
      "| B _ -> True"
      "| _ -> False"
      "end"
      "predicate is_Proc (v: v) = match v with"
      ,@(for/list : (Listof String) ([clo (in-hash-keys clo-tab)])
          (match-define (Closure k xs) clo)
          (string-join
           (cons (symbol->string k)
                 (for/list : (Listof String) ([_ xs]) "_"))
           #:before-first "| "
           #:after-last " -> True"))
      "| _ -> False"
      "end"
      "predicate is_Equal (u: v) (v: v) = u = v"
      "predicate is_Unsafe_Le (u: v) (v: v) ="
      "  is_N u /\\ is_N v /\\"
      "  match u, v with"
      "  | N m, N n -> m <= n"
      "  | _  , _   -> (* garbage *) False"
      "  end"
      ""
      "(** Contrivedly total versions of some primitive functions."
      "    This is for making implementation available during proofs."
      "    Real functions used in programs are guarded versions of these. *)"
      "function unsafe_add1 (v: v): v = match v with"
      "| N n -> N (1 + n)"
      "| _   -> (* garbage *) Nil"
      "end"
      "function unsafe_plus (u: v) (v: v): v = match u, v with"
      "| N m, N n -> N (m + n)"
      "| _  , _   -> (* garbage *) Nil"
      "end"
      "function unsafe_lep (u: v) (v: v): v = B (is_Unsafe_Le u v)"
      "function unsafe_car (v: v): v = match v with"
      "| Cons u _ -> u"
      "| _        -> (* garbage *) Nil"
      "end"
      "function unsafe_cdr (v: v): v = match v with"
      "| Cons _ u -> u"
      "| _        -> (* garbage *) Nil"
      "end"
      ""
      "(** Primitive functions *)"
      "function listp (v: v): v = B (is_List v)"
      "function nilp (v: v): v = B (is_Nil v)"
      "function consp (v: v): v = B (is_Cons v)"
      "function cons (u: v) (v: v): v = Cons u v"
      "let car (v: v)"
      "  requires {is_Cons v}"
      "  returns  {a -> a = unsafe_car v} = unsafe_car v"
      "let cdr (v: v)"
      "  requires {is_Cons v}"
      "  returns  {a -> a = unsafe_cdr v} = unsafe_cdr v"
      "function intp (v: v): v = B (is_N v)"
      "let add1 (v: v)"
      "  requires {is_N v}"
      "  returns  {a -> is_N a /\\ a = unsafe_add1 v} = unsafe_add1 v"
      "let plus (u: v) (v: v)"
      "  requires {is_N u /\\ is_N v}"
      "  returns  {a -> is_N a /\\ a = unsafe_plus u v} = unsafe_plus u v"
      "function boolp (v: v): v = B (is_B v)"
      "function neg (v: v): v = match v with"
      "| B False -> B True"
      "| _       -> B False"
      "end"
      "function procp (v: v): v = B (is_Proc v)"
      "function equalp (u: v) (v: v): v = B (u = v)"
      "let lep (u: v) (v: v)"
      "  requires {is_N u /\\ is_N v}"
      "  returns  {a -> is_B a /\\ a = unsafe_lep u v} = unsafe_lep u v"))

  ;; Define `apply` functions
  (define clo-by-arity 
    (for/fold ([acc : (HashTable Natural (℘ (Pairof Closure Rhs))) (hash)])
              ([(clo rhs) clo-tab])
      (match-define (Rhs xs _) rhs)
      (hash-update acc
                   (length xs)
                   (λ ([s : (℘ (Pairof Closure Rhs))])
                     (set-add s (cons clo rhs)))
                   →∅)))
  (define apply-defns
    (for/fold ([acc : (Listof String) '()])
              ([(n cases) clo-by-arity] #:unless (set-empty? cases))
      (define arg-list
        (string-join
         (for/list : (Listof String) ([i n])
           (format "(arg_~a: v)" i))))
      (define this-case
        `(""
          ,(format "(** Application of lambdas of arity ~a," n)
          "    specific to program under verification *)"
          ,(format "let rec apply_~a (func: v) ~a : v" n arg-list)
          "  requires {is_Proc func}"
          "  diverges = match func with"
          ,@(for/fold ([acc : (Listof String) '()])
                      ([clo-rhs cases])
              (match-define (cons clo rhs) clo-rhs)
              (match-define (Closure k fvs) clo)
              (match-define (Rhs xs e) rhs)
              (define lhs : String
                (string-join
                 (for/list : (Listof String) ([fv fvs])
                   (format "~a" fv))
                 #:before-first (format "| ~a " k)
                 #:after-last " ->"))
              (define bnd : String
                (let ([lhs
                       (string-join
                        (for/list : (Listof String) ([x xs])
                          (format "~a" x))
                        ", ")]
                      [rhs
                       (string-join
                        (for/list : (Listof String) ([i (length xs)])
                          (format "arg_~a" i))
                        ", ")])
                  (format "(~a) = (~a)" lhs rhs)))
              (append
               acc
               (list*
                lhs
                (with-indent
                  (format "let ~a in" bnd)
                  (emit-e e)))))
          ,@(let ([other-cases
                   (for*/list : (Listof String) ([(m cases) clo-by-arity] #:unless (= m n)
                                                 [clo-rhs cases])
                     (match-define (cons (Closure s xs) _) clo-rhs)
                     (string-join
                      (for/list : (Listof String) ([_ xs]) "_")
                      #:before-first (format "~a " s)))])
              (cond
                [(empty? other-cases) '()]
                [else
                 (list
                  (string-join other-cases " | "
                               #:before-first "| "
                               #:after-last " ->")
                  "  assume {False}; (* guaranteed no wrong arity *)"
                  "  absurd")])) 
          "| _ -> absurd"
          "end"))
      (append acc this-case)))
  

  ;; Emit regular definitions
  (define compiled-forms (append-map emit-form forms))
  
  `("module Prog"
    ,@(with-indent
        "use import int.Int"
        "use import bool.Bool"
        ""
        "(** Unitype for base values, primitives, and closures *)"
        declare-values
        ""
        define-primitives
        ""
        apply-defns
        ""
        "(** Compiled definitions, specific to program under verification *)"
        compiled-forms)
    "end")
)

(: emit-form : -module-level-form → (Listof String))
(define emit-form
  (match-lambda
    [(-define-values (list x) e) (emit-defn x e)]
    [(? -e? e) (emit-e e)]
    [_ '()]))

(: emit-defn : Var-Name -e → (Listof String))
(define (emit-defn x e)
  (match e
    [(-λ (? list? zs) e*)
     (define fxs
       (string-join
        (for/list : (Listof String) ([z zs]) (format "(~a: v)" z))
        #:before-first (format "let rec ~a " x)
        #:after-last " : v diverges ="))
     (list*
      ""
      fxs
      (with-indent (emit-e e*)))]
    [_
     (list*
      ""
      (format "let ~a =" x)
      (with-indent (emit-e e)))]))

(: emit-e : -e → (Listof String))
(define emit-e
  (match-lambda
    [(== -ok) (list (format "assume {False}; absurd"))]
    [(== -bad) (list (format "absurd"))]
    [(or (? symbol? o) (-𝒾 (? symbol? o) 'Λ))
     (error "Assume non-first-class use of primitives. Please wrap `~a` in a lambda" o)]
    [(-b b) (list (match b
                    [(? integer? n) (format "(N ~a)" n)]
                    [#f (format "(B False)")]
                    [#t (format "(B True)")]
                    [(list) "Nil"]))]
    [(-x x) (list (format "~a" (remove-dash x)))]
    [(-𝒾 name _) (list (format "~a" name))]
    [(-if e e₁ e₂)
     (define match-line
       (merge-lines
        `("match"
          ,@(with-indent (emit-e e))
          "with")))
     (define false-line
       (merge-lines
        `("| B False ->"
          ,@(with-indent (emit-e e₂)))))
     (define true-line
       (merge-lines
        `("| _ ->"
          ,@(with-indent (emit-e e₁)))))
     `(,@match-line
       ,@false-line
       ,@true-line
       "end")]
    [(-begin es)
     (let go ([es : (Listof -e) es])
       (match es
         [(list e) (emit-e e)]
         [(cons e es*)
          `(,@(merge-lines (append (emit-e e) '(";"))) ,@(go es*))]))]
    [(-let-values bnds e)
     (define bnds↓ : (Listof String)
       (append-map
        (λ ([bnd : (Pairof (Listof Var-Name) -e)])
          (match-define (cons (list x) eₓ) bnd)
          (merge-lines
           `(,(format "let ~a =" (remove-dash x))
             ,@(with-indent (emit-e eₓ))
             "in")))
        bnds))
     `(,@bnds↓
       ,@(emit-e e))]
    [(-@ f xs ℓ)
     (merge-lines
      (match f
        ['apply
         (match-define (cons fun args) xs)
         (emit-e (-@ fun args ℓ))]
        ['assert
         (match-define (cons fun args) xs)
         (match fun
           [(or (? symbol? o) (-𝒾 (? symbol? o) 'Λ)) #:when o
            (merge-lines
             `("assert {"
               ,(symbol->string (o->pred o))
               ,@(append-map emit-e args)
               "}"))])]
        ['assert-not
         (match-define (cons fun args) xs)
         (match fun
           [(or (? symbol? o) (-𝒾 (? symbol? o) 'Λ)) #:when o
            (merge-lines
             `("assert { not ("
               ,(symbol->string (o->pred o))
               ,@(append-map emit-e args)
               ")}"))])]
        ['assume
         (match-define (cons fun args) xs)
         (match fun
           [(or (? symbol? o) (-𝒾 (? symbol? o) 'Λ)) #:when o
            (merge-lines
             `("assume {"
               ,(symbol->string (o->pred o))
               ,@(append-map emit-e args)
               "}"))])]
        ['assume-not
         (match-define (cons fun args) xs)
         (match fun
           [(or (? symbol? o) (-𝒾 (? symbol? o) 'Λ)) #:when o
            (merge-lines
             `("assume {not ("
               ,(symbol->string (o->pred o))
               ,@(append-map emit-e args)
               ")}"))])]
        [(or (-𝒾 (? symbol? o) 'Λ) (? symbol? o)) #:when o
         `(,(symbol->string (o->prim o))
           ,@(with-indent (append-map emit-e/parens xs)))]
        [(-𝒾 (? symbol? o) #|FIXME sloppy|# _)
         `(,(symbol->string o)
           ,@(with-indent (append-map emit-e/parens xs)))]
        [_
         (merge-lines
          `(,(format "apply_~a" (length xs))
            ,@(with-indent (emit-e f))
            ,@(with-indent (append-map emit-e/parens xs))))]))]))

(: emit-e/parens : -e → (Listof String))
(define (emit-e/parens e)
  (if (simpl? e)
      (emit-e e)
      (merge-lines `("(" ,@(emit-e e) ")"))))

(: o->pred : Symbol → Symbol)
(define (o->pred o)
  (case o
    [(cons?) 'is_Cons]
    [(integer?) 'is_N]
    [(procedure?) 'is_Proc]
    [(equal?) 'is_Equal]
    [(boolean?) 'is_B]
    [(list?) 'is_List]
    [(<=) 'is_Unsafe_Le]
    [else (error 'o->pred "unsupported: ~a" o)]))

(: o->prim : Symbol → Symbol)
;; Map racket's prim to target prim
(define (o->prim o)
  (case o
    [(boolean?) 'boolp]
    [(null? empty?) 'nilp]
    [(cons) 'cons]
    [(cons? pair?) 'consp]
    [(car) 'car]
    [(cdr) 'cdr]
    [(integer?) 'intp]
    [(add1) 'add1]
    [(+) 'plus]
    [(procedure?) 'procp]
    [(not false) 'neg]
    [(equal?) 'equalp]
    [(<=) 'lep]
    [(list?) 'listp]
    [else o]))

(: merge-lines : (Listof String) → (Listof String))
(define (merge-lines ls)
  (define N 90)
  (define ls*
    (match ls
      ['() '()]
      [(cons l ls*) (cons l ((inst map String String) string-trim ls*))]))
  (define n (apply + (map string-length ls*)))
  (cond
    [(<= n N) (list (string-join ls*))]
    [else ls]))
