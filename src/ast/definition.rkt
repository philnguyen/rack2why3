#lang typed/racket/base

(provide (all-defined-out))

(require racket/match
         racket/set
         (except-in racket/list remove-duplicates)
         racket/function
         racket/extflonum 
         "../utils/main.rkt")

;; Parameterized begin
(struct (X) -begin ([body : (Listof X)]) #:transparent)
(define-type -begin/e (-begin -e))
(define-type -begin/top (-begin -top-level-form))

;; Temporary definition of module path
(define-type/pred Adhoc-Module-Path (U Symbol String) #|TODO|#)
(define-type Mon-Party Adhoc-Module-Path)
(struct Mon-Info ([pos : Mon-Party] [neg : Mon-Party] [src : Mon-Party]) #:transparent)

;; Swap positive and negative blame parties
(define swap-parties : (Mon-Info → Mon-Info)
  (match-lambda [(Mon-Info l+ l- lo) (Mon-Info l- l+ lo)]))

(define-type -ℓ Natural)

;; Source location generator. It's hacked to remember fixed location for havoc
(: +ℓ! : → -ℓ)
(: +ℓ/memo! : (U 'hv-ref 'hv-ap 'opq-ap 'ac-ap 'vref) Any * → -ℓ)
(define-values (+ℓ! +ℓ/memo!)
  (let ([n : -ℓ 1]
        [m : (HashTable (Listof Any) -ℓ) (make-hash)])
    (values
     (λ () (begin0 n (set! n (+ 1 n))))
     (λ (tag . xs) (hash-ref! m (cons tag xs) +ℓ!)))))

;; Symbol names are used for source code. Integers are used for generated.
;; Keep this eq?-able
(Var-Name . ::= . Symbol Integer)
(: +x! : → Integer)
(: +x/memo! : (U 'hv 'hv-rt) Any * → Integer)
(define-values (+x! +x/memo!)
  (let ([n : Integer 0]
        [m : (HashTable (Listof Any) Integer) (make-hash)])
    (values
     (λ () (begin0 n (set! n (+ 1 n))))
     (λ (tag . xs) (hash-ref! m (cons tag xs) +x!)))))

;; Identifier as a name and its source
(struct -𝒾 ([name : Symbol] [ctx : Adhoc-Module-Path]) #:transparent)

;; Struct meta data
(struct -struct-info ([id : -𝒾] [arity : Natural] [mutables : (℘ Natural)]) #:transparent)

;; Formal parameters
(-formals . ::= . (Listof Var-Name)
                  (-varargs [init : (Listof Var-Name)] [rest : Var-Name]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; AST subset definition as in Racket reference 1.2.3.1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(Arity . ::= . Natural arity-at-least (Listof (U Natural arity-at-least)))
(Base . ::= . Number ExtFlonum Boolean String Symbol Keyword Bytes Regexp PRegexp Char Null Void Arity)

(-top-level-form . ::= . -general-top-level-form
                         -e
                         -module
                         -begin/top)

(-module-level-form . ::= . -general-top-level-form
                            (-provide [specs : (Listof -provide-spec)])
                            -submodule-form)

(-general-top-level-form . ::= . -e
                                 (-define-values [ids : (Listof Symbol)] [e : -e])
                                 (-require (Listof -require-spec)))

(-submodule-form . ::= . (-module [path : Adhoc-Module-Path] [body : (Listof -module-level-form)]))

(-provide-spec . ::= . (-p/c-item [id : Symbol] [spec : -e] [loc : -ℓ]))

(-require-spec . ::= . Adhoc-Module-Path #|TODO|#)

(-e . ::= . -v
            (-x Var-Name) ; lexical variables 
            -𝒾 ; module references
            (-@ -e (Listof -e) -ℓ)
            (-if -e -e -e)
            (-wcm [key : -e] [val : -e] [body : -e])
            -begin/e
            (-begin0 -e (Listof -e))
            (-quote Any)
            (-let-values [bnds : (Listof (Pairof (Listof Var-Name) -e))] [body : -e])
            (-letrec-values [bnds : (Listof (Pairof (Listof Var-Name) -e))] [body : -e])
            (-set! Var-Name -e)
            (-error String)
            (-amb (℘ -e))
            
            ;; contract stuff
            (-μ/c -ℓ -e)
            (--> [doms : (Listof -e)] [rng : -e] [pos : -ℓ])
            (-->i [doms : (Listof -e)] [rng : -λ] [pos : -ℓ])
            (-case-> [clauses : (Listof (Pairof (Listof -e) -e))] -ℓ)
            (-x/c.tmp Symbol) ; hack
            (-x/c -ℓ)
            (-struct/c [info : -struct-info] [fields : (Listof -e)] [pos : -ℓ]))

(-v . ::= . -prim
            (-λ -formals -e)
            (-case-λ (Listof (Pairof (Listof Var-Name) -e)))
            (-• Natural))

(-prim . ::= . ;; Represent *unsafe* operations without contract checks. 
               ;; User code shouldn't have direct access to these.
               ;; Generated `prim` module exports these operations wrapped in contract. -o (-b Base)
               -o
               ;; primitive values that can appear in syntax
               (-b [unboxed : Base]))

(-o . ::= . Symbol
           (-st-p -struct-info)
           (-st-ac -struct-info Natural)
           (-st-mut -struct-info Natural)
           (-st-mk -struct-info))

(define-type -es (℘ -e))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Constants & 'Macros'
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define -tt (-b #t))
(define -ff (-b #f))
(define -null (-b null))
(define -void (-b (void)))

(define -𝒾-values (-𝒾 'values 'Λ))
(define -𝒾-cons (-𝒾 'cons 'Λ))
(define -s-cons (-struct-info -𝒾-cons 2 ∅))
(define -cons (-st-mk -s-cons))
(define -car (-st-ac -s-cons 0))
(define -cdr (-st-ac -s-cons 1))
(define -cons? (-st-p -s-cons))

(define -zero (-b 0))
(define -one (-b 1))

(define -𝒾-box (-𝒾 'box 'Λ))
(define -s-box  (-struct-info -𝒾-box 1 {set 0}))
(define -box? (-st-p -s-box))
(define -unbox (-st-ac -s-box 0))
(define -box (-st-mk -s-box))
(define -set-box! (-st-mut -s-box 0))
(define -pred (--> (list 'any/c) 'boolean? 0))

(define havoc-path 'havoc)
(define havoc-𝒾 (-𝒾 'havoc-id havoc-path))

(define m∅ : (HashTable -e -e) (hash))

(: -cond : (Listof (Pairof -e -e)) -e → -e)
;; Make `cond` at object language level, expanding to `if`
(define (-cond cases default)
  (foldr (λ ([alt : (Pairof -e -e)] [els : -e])
           (match-define (cons cnd thn) alt)
           (-if cnd thn els))
         default
         cases))

(: -->* : (Listof -e) -e -e → -e)
;; Make a non-dependent vararg contract
;; TODO: separate case for non-dependent varargs
(define (-->* cs rst d)
  (define xs (-varargs (map (λ (_) (+x!)) cs) (+x!)))
  (-->i (append cs (list rst)) (-λ xs d) (+ℓ!)))

;; Make conjunctive and disjunctive contracts
(define-values (-and/c -or/c)
  (let () 
    (: -app/c : Symbol (Listof -e) → -e)
    (define (-app/c o es) : -e
      (match es
        ['() 'any/c]
        [(list e) e]
        [(cons e es*)
         (-@ (-𝒾 o 'Λ) (list e (-app/c o es*)) (+ℓ!))]))
    (values (curry -app/c 'and/c) (curry -app/c 'or/c))))

(: -not/c : -e → -e)
(define (-not/c e)
  (-@ (-𝒾 'not/c 'Λ) (list e) (+ℓ!)))

(: -one-of/c : (Listof -e) → -e)
(define (-one-of/c es)
  (cond
    [(null? es) 'none/c]
    [else
     (define x (+x!))
     (define 𝐱 (-x x))
     (define body : -e
       (let build-body ([es : (Listof -e) es])
         (match es
           [(list e) (-@ 'equal? (list 𝐱 e) (+ℓ!))]
           [(cons e es*)
            (-if (-@ 'equal? (list 𝐱 e) (+ℓ!))
                 -tt
                 (build-body es*))])))
     (-λ (list x) body)]))

(: -cons/c : -e -e → -e)
(define (-cons/c c d)
  (-struct/c -s-cons (list c d) (+ℓ!)))

(: -listof : -e → -e)
(define (-listof c)
  (define ℓ (+ℓ!))
  (-μ/c ℓ (-or/c (list 'null? (-cons/c c (-x/c ℓ))))))

(: -box/c : -e → -e)
(define (-box/c c)
  (-struct/c -s-box (list c) (+ℓ!)))

(: -list/c : (Listof -e) → -e)
(define (-list/c cs)
  (foldr -cons/c 'null? cs))

(: -list : (Listof -e) → -e)
(define (-list es)
  (match es
    ['() -null]
    [(cons e es*)
     (-@ -cons (list e (-list es*)) (+ℓ!))]))

(:* -and : -e * → -e)
;; Return ast representing conjuction of 2 expressions
(define -and
  (match-lambda*
    [(list) -tt]
    [(list e) e]
    [(cons e es) (-if e (apply -and es) -ff)]))

(: -comp/c : Symbol -e → -e)
;; Return ast representing `(op _ e)`
(define (-comp/c op e)
  (define x (+x!))
  (define 𝐱 (-x x))
  (-λ (list x)
      (-and (-@ 'real? (list 𝐱) (+ℓ!)) (-@ op (list 𝐱 e) (+ℓ!)))))

(: -amb/simp : (Listof -e) → -e)
;; Smart constructor for `amb` with simplification for 1-expression case
(define -amb/simp
  (match-lambda
    [(list e) e]
    [es (-amb (list->set es))]))

(: -amb/remember : (Listof -e) → -e)
;; Return ast representing "remembered" non-determinism
(define/match (-amb/remember es)
  [((list)) (-b 'end-of-amb)]
  [((list e)) e]
  [((cons e es)) (-if (•!) e (-amb/remember es))])

(: -begin/simp : (∀ (X) (Listof X) → (U X (-begin X))))
;; Smart constructor for begin, simplifying single-expression case
(define/match (-begin/simp xs)
  [((list e)) e]
  [(es) (-begin es)])

(: •! : → -•)
;; Generate new labeled hole
(define •!
  (let ([n : Natural 0])
    (λ () (begin0 (-• n) (set! n (+ 1 n))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; Pretty Printing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-values (show-x/c show-x/c⁻¹ count-x/c) ((inst unique-sym -ℓ) 'x))

(define (show-ℓ [ℓ : -ℓ]) : Symbol
  (format-symbol "ℓ~a" (n-sub ℓ)))

(define (show-b [x : Base]) : Sexp
  (cond
    [(string? x) (format "\"~a\"" x)]
    [(or (symbol? x) (keyword? x)) `(quote ,x)]
    [(and (real? x) (inexact? x))
     (define s (number->string x))
     (substring s 0 (min (string-length s) 5))]
    [(or (regexp? x) (pregexp? x) (bytes? x)) (format "~a" x)]
    [(extflonum? x) (extfl->inexact x)]
    [(void? x) 'void]
    [(arity-at-least? x) `(arity-at-least ,(arity-at-least-value x))]
    [(list? x) `(list ,@(map show-b x))]
    [else x]))

;; Return operator's simple show-o for pretty-printing
(define show-o : (-o → Symbol)
  (match-lambda
   [(? symbol? s) s]
   [(-st-mk s) (show-struct-info s)]
   [(-st-ac (== -s-cons) 0) 'car]
   [(-st-ac (== -s-cons) 1) 'cdr]
   [(-st-ac (== -s-box) 0) 'unbox]
   [(-st-ac s i) (format-symbol "~a@~a" (show-struct-info s) i)]
   [(-st-p s) (format-symbol "~a?" (show-struct-info s))]
   [(-st-mut (== -s-box) 0) 'set-box!]
   [(-st-mut s i) (format-symbol "set-~a-~a!" (show-struct-info s) i)]))

(define (show-e [e : -e]) : Sexp
  (match e
    ; syntactic sugar
    #|[(-λ (list x) (-@ '= (list (-x x) e*) _)) `(=/c ,(show-e e*))]
    [(-λ (list x) (-@ 'equal? (list (-x x) e*) _)) `(≡/c ,(show-e e*))]
    [(-λ (list x) (-@ '> (list (-x x) e*) _)) `(>/c ,(show-e e*))]
    [(-λ (list x) (-@ '< (list (-x x) e*) _)) `(</c ,(show-e e*))]
    [(-λ (list x) (-@ '>= (list (-x x) e*) _)) `(≥/c ,(show-e e*))]
    [(-λ (list x) (-@ '<= (list (-x x) e*) _)) `(≤/c ,(show-e e*))]
    [(-@ (-λ (list x) (-x x)) (list e) _) (show-e e)]
    [(-@ (-λ (list x) (-if (-x x) (-x x) b)) (list a) _)
     (match* ((show-e a) (show-e b))
       [(`(or ,l ...) `(or ,r ...)) `(or ,@(cast l Sexps) ,@(cast r Sexps))]
       [(`(or ,l ...) r) `(or ,@(cast l Sexps) ,r)]
       [(l `(or ,r ...)) `(or ,l ,@(cast r Sexps))]
       [(l r) `(or ,l ,r)])]|#
    [(-if a b (-b #f))
     (match* ((show-e a) (show-e b))
       [(`(and ,l ...) `(and ,r ...)) `(and ,@(cast l Sexps) ,@(cast r Sexps))]
       [(`(and ,l ...) r) `(and ,@(cast l Sexps) ,r)]
       [(l `(and ,r ...)) `(and ,l ,@(cast r Sexps))]
       [(l r) `(and ,l ,r)])]
    [(-if a b (-b #t)) `(implies ,(show-e a) ,(show-e b))]

    [(-λ xs e) `(λ ,(show-formals xs) ,(show-e e))]
    [(-case-λ clauses)
     `(case-lambda
        ,@(for/list : (Listof Sexp) ([clause clauses])
            (match-define (cons xs e) clause)
            `(,(show-formals xs) ,(show-e e))))]
    [(-• i) (format-symbol "•~a" (n-sub i))]
    [(-b b) (show-b b)]
    [(? -o? o) (show-o o)]
    [(-x x) (show-Var-Name x)]
    [(-𝒾 x p)
     (case p ;; hack
       [(Λ) (format-symbol "_~a" x)]
       [else x])]
    [(-let-values bnds body)
     `(let-values
          ,(for/list : (Listof Sexp) ([bnd bnds])
             (match-define (cons xs ex) bnd)
             `(,xs ,(show-e ex)))
        ,(show-e body))]
    [(-letrec-values bnds body)
     `(letrec-values
          ,(for/list : (Listof Sexp) ([bnd bnds])
             (match-define (cons xs ex) bnd)
             `(,xs ,(show-e ex)))
        ,(show-e body))]
    [(-set! x e) `(set! ,x ,(show-e e))]
    [(-@ f xs _) `(,(show-e f) ,@(show-es xs))]
    [(-begin es) `(begin ,@(show-es es))]
    [(-begin0 e es) `(begin ,(show-e e) ,@(show-es es))]
    [(-error msg) `(error ,msg)]
    #;[(-apply f xs _) `(apply ,(show-e f) ,(go show-e xs))]
    [(-if i t e) `(if ,(show-e i) ,(show-e t) ,(show-e e))]
    [(-amb e*) `(amb ,@(for/list : (Listof Sexp) ([e e*]) (show-e e)))]
    [(-μ/c x c) `(μ/c (,(show-x/c x)) ,(show-e c))]
    [(--> cs d _)
     `(,@(map show-e cs) . -> . ,(show-e d))]
    [(-->i cs (and d (-λ xs _)) _)
     (match xs
       [(? list? xs)
        `(,@(map show-e cs) ↦ ,(show-e d))]
       [(-varargs xs₀ x)
        (define-values (cs₀ c) (split-at cs (length xs₀)))
        `(,@(map show-e cs₀) #:rest ,@(map show-e c) ↦ ,(show-e d))])]
    [(-case-> clauses _)
     (for/list : (Listof Sexp) ([clause clauses])
       (match-define (cons cs d) clause)
       `(,@(map show-e cs) . -> . ,(show-e d)))]
    [(-x/c.tmp x) x]
    [(-x/c x) (show-x/c x)]
    [(-struct/c info cs _)
     `(,(format-symbol "~a/c" (show-struct-info info)) ,@(show-es cs))]))

(define (show-es [es : (Sequenceof -e)]) : (Listof Sexp)
  (for/list ([e es]) (show-e e)))

(define (show-module [m : -module]) : (Listof Sexp)
  (match-define (-module path forms) m)
  `(module ,path
    ,@(map show-module-level-form forms)))

(define (show-struct-info [info : -struct-info]) : Symbol
  (-𝒾-name (-struct-info-id info)))

(define show-module-level-form : (-module-level-form → Sexp)
  (match-lambda
    [(-provide specs) `(provide ,@(map show-provide-spec specs))]
    [(? -general-top-level-form? m) (show-general-top-level-form m)]))

(define show-general-top-level-form : (-general-top-level-form → Sexp)
  (match-lambda
    [(? -e? e) (show-e e)]
    [(-define-values xs e)
     (match* (xs e)
       [((list f) (-λ xs e*)) `(define (,f ,@(show-formals xs)) ,(show-e e*))]
       [((list x) _) `(define ,x ,(show-e e))]
       [(_ _) `(define-values ,xs ,(show-e e))])]
    [(-require specs) `(require ,@(map show-require-spec specs))]))

(define show-provide-spec : (-provide-spec → Sexp)
  (match-lambda
    [(-p/c-item x c _) `(,x ,(show-e c))]))

(define show-require-spec : (-require-spec → Sexp)
  values)

(define show-formals : (-formals → Sexp)
  (match-lambda
    [(-varargs xs rst) (cons (map show-Var-Name xs) (show-Var-Name rst))]
    [(? list? l) (map show-Var-Name l)]))

(define (show-Var-Name [x : Var-Name]) : Symbol
  (cond [(integer? x) (format-symbol "𝐱~a" (n-sub x))]
        [else x]))

(define (show-e-map [m : (HashTable -e -e)]) : (Listof Sexp)
  (for/list ([(x y) m]) `(,(show-e x) ↦ ,(show-e y))))
