#lang racket

(provide
 (contract-out
  [inc (->i ([n integer?])
            (res (n) (λ (a) (<= n a))))]
  [length (list? . -> . (and/c integer? (λ (l) (<= 0 l))))]
  [map ((any/c . -> . any/c) list? . -> . list?)]
  [filter ((any/c . -> . any/c) list? . -> . list?)]
  [foldr ((any/c any/c . -> . any/c) any/c list? . -> . any/c)]
  [foldl ((any/c any/c . -> . any/c) any/c list? . -> . any/c)]
  ))

(define (inc x) (add1 x))

(define (length x)
  (cond [(cons? x) (+ 1 (length (cdr x)))]
        [else 0]))

(define (map f x)
  (cond [(cons? x) (cons (f (car x)) (map f (cdr x)))]
        [else null]))

(define (filter p xs)
  (cond [(cons? xs)
         (if (p (car xs))
             (cons (car xs) (filter p (cdr xs)))
             (filter p (cdr xs)))]
        [else null]))

(define (foldr f a xs)
  (cond [(cons? xs) (f (car xs) (foldr f a (cdr xs)))]
        [else a]))

(define (foldl f a xs)
  (cond [(cons? xs) (foldl f (f a (car xs)) (cdr xs))]
        [else a]))
