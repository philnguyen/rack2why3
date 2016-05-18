#lang typed/racket/base

(require racket/string
         "../utils/main.rkt"
         "../ast/definition.rkt")

(provide (all-defined-out))

(define-parameter sym-prefix : Symbol 'gen)

;; More predictable output than `gensym`
(define next-sym! : (case->
                     [→ Symbol]
                     [Symbol → Symbol])
  (let ([m : (HashTable Symbol Natural) (make-hasheq)])
    (case-lambda
      [()
       (next-sym! (sym-prefix))]
      [(s)
       (hash-update! m s add1 (λ () 0))
       (format-symbol "~a_~a" s (hash-ref m s))])))

(struct Closure ([name : Symbol] [free : (Listof Var-Name)]) #:transparent)
(struct Rhs ([bound : (Listof Var-Name)] [body : -e]) #:transparent)
(define-type Closure-Table (HashTable Closure Rhs))

(define -ok (-b '#:ok))
(define -bad (-b '#:bad))

(define (simpl? [e : -e]) (or (-x? e) (-v? e) (-𝒾? e)))

(: remove-dash : Var-Name → Var-Name)
(define (remove-dash x)
  (cond [(symbol? x)
         (string->symbol (string-replace (symbol->string x) "-" "_" #:all? #t))]
        [else x]))
