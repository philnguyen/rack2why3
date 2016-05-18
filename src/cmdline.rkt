#lang typed/racket/base

(require racket/cmdline "compile/main.rkt")

(command-line
 #:program "racket2why"
 #:args (src-file out-file)
 (compile-file (assert src-file path-string?) (assert out-file path-string?)))
