#lang typed/racket/base

(provide (all-defined-out))

(require racket/file
         "../ast/main.rkt"
         "../parse/main.rkt"
         "../utils/main.rkt"
         "compile-contract.rkt"
         "defunctionalize.rkt"
         "emit.rkt")

(: test : Path-String → Void)
(define (test fn)
  (for ([l (compile fn)])
    (displayln l)))

(: compile : Path-String → (Listof String))
(define (compile path)
  (define-values (m clos) (defunct-module (compile-contract (file->module path))))
  ;(printf "m:~n~a~n" (pretty (show-module m)))
  ;(printf "clo:~n~a~n" clos)
  (emit m clos))

(: compile-file : Path-String Path-String → Void)
(define (compile-file fn out)
  (display-lines-to-file (compile fn) out #:exists 'replace))
