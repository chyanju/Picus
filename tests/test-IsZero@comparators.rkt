#lang rosette
(output-smt #t)
(define-symbolic x0 integer?)
(define-symbolic x1 integer?)
(define-symbolic x2 integer?) 
(define-symbolic x3 integer?)

(define p 21888242871839275222246405745257275088548364400416034343698204186575808495617)
(define (assert-range x) (assert (&& (>= x 0) (< x p))))
(assert-range x0)
(assert-range x1)
(assert-range x2)
(assert-range x3)
(assert (= x0 1))

; disable modulo
; (define (modulo a b) a)

(define c0 (=
  (modulo (* x2 x3) p)
  (modulo (+ x0 (* 21888242871839275222246405745257275088548364400416034343698204186575808495616 x1)) p)
))

(define c1 (=
  (modulo (* x2 x1) p)
  (modulo 0 p)
))

(define-symbolic x1b integer?)
(define-symbolic x3b integer?)
(assert-range x1b)
(assert-range x3b)

(define c0b (=
  (modulo (* x2 x3b) p)
  (modulo (+ x0 (* 21888242871839275222246405745257275088548364400416034343698204186575808495616 x1b)) p)
))

(define c1b (=
  (modulo (* x2 x1b) p)
  (modulo 0 p)
))


; no range analysis, z3 returns (unknown)
; (define sol (solve (assert (&& c0 c1 c0b c1b (! (= x1 x1b)) ))))
; with range analysis, z3 returns (unsat), which is verified
(define sol (solve (assert (&& c0 c1 c0b c1b (&& (! (= x1 x1b)) (|| (= x1 0) (= x1 1)) (|| (= x1b 0) (= x1b 1)) ) ))))
(printf "~a\n" sol)
