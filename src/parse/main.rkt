#lang typed/racket/base

(require racket/match "../ast/definition.rkt")
(require/typed/provide "private.rkt"
  [file->module (Path-String → -module)])


#|
(: file->module : Path-String → -module)
;; Alpha renaming on top of the old parser (hack)
(define (file->module p) (α-rename (file->module* p)))
|#
