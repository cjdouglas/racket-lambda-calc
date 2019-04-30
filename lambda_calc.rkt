#lang racket
;; Church numeral to Racket num for verification
(define (to-num n)
  ((n add1) 0))

;; Church boolean to Racket boolean for verification
(define (to-bool b)
  ((b #t) #f))

;; Church numerals
(define Z
  (λ (s)
    (λ (z) z)))
(define S
  (λ (n)
    (λ (s)
      (λ (z)
        (s ((n s) z))))))
(define one
  (S Z))
(define two
  (S (S Z)))
(define three
  (S (S (S Z))))
(define four
  (S (S (S (S Z)))))
(define plus
  (λ (n)
    (λ (m)
      ((n S) m))))
(define mult
  (λ (n)
    (λ (m)
      ((m (plus n)) Z))))
(define five ((plus one) four))
(define fifteen ((mult five) three))

;; Church booleans
(define true
  (λ (t)
    (λ (f) t)))
(define false
  (λ (t)
    (λ (f) f)))
(define and
  (λ (p)
    (λ (q)
      ((p q) false))))
(define or
  (λ (p)
    (λ (q)
      ((p true) q))))
(define not
  (λ (p)
    ((p false) true)))
;((and true) false)
;((or false) true)
;(not false)

;; Church pairs
;;
;; Constructs a pair
;; λx.λy.λf.f x y
(define mkpair
  (λ (x)
    (λ (y)
      (λ (f)
        ((f x) y)))))
;; Returns the first element of a pair
;; λx.λy.x
(define fst
  (λ (x)
    (λ (y) x)))
;; Returns the second element of a pair
;; λx.λy.y
(define snd
  (λ (x)
    (λ (y) y)))
;; Returns the sum of the pair values
;; λx.λy.x + y
(define sum
  (λ (x)
    (λ (y) (+ x y))))
(((mkpair 9) 7) fst)

;; Church Lists
;; Encoded using the above pair structures
;;
;; Represents nil
;; λc.λn.n
(define nil
  (λ (c)
    (λ (n) n)))
;; Constructs a list
;; λa.λl.λc.λn.c a l
(define cons
  (λ (a)
    (λ (l)
      (λ (c)
        (λ (n)
          ((c a) l))))))
;; Checks whether a list is nil or not
;; λz.z (λa.λl.false) true
(define is-nil
  (λ (z)
    ((z
      (λ (a)
          (λ (l) false)))
     true)))
(define z ((cons 7) ((cons 2) ((cons 9) nil))))
(define z2 nil)
(define head
  (λ (z)
    ((z true) false)))
(define tail
  (λ (z)
    ((z false) false)))
(head z)
(head (tail z))
(is-nil z)
(is-nil z2)

;; TODO: binary trees
