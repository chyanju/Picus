#lang rosette
(define-symbolic x0 integer?)
(define-symbolic x1 integer?)
(define-symbolic x2 integer?)
(define-symbolic x3 integer?)
(define-symbolic x4 integer?)
(define p 21888242871839275222246405745257275088548364400416034343698204186575808495617)
(define (assert-range x) (assert (&& (>= x 0) (< x p))))
(assert-range x0)
(assert-range x1)
(assert-range x2)
(assert-range x3)
(assert-range x4)
(assert (= x0 1))

(define c0 (=
  (modulo (* x0 x4) p)
  (modulo (* (+ x0 (* 21888242871839275222246405745257275088548364400416034343698204186575808495616 x4)) x1) p)
))

(define c1 (=
  (modulo x1 p)
  (modulo (* x2 x3) p)
))

(define-symbolic x1b integer?)
(define-symbolic x2b integer?)
(assert-range x1b)
(assert-range x2b)

(define c0b (=
  (modulo (* x0 x4) p)
  (modulo (* (+ x0 (* 21888242871839275222246405745257275088548364400416034343698204186575808495616 x4)) x1b) p)
))

(define c1b (=
  (modulo x1b p)
  (modulo (* x2b x3) p)
))

(solve (assert (&& c0 c1 c0b c1b (! (= x2 x2b)) (! (= x1 x1b)))))