#lang rosette
(output-smt #t)

(define p 21888242871839275222246405745257275088548364400416034343698204186575808495617)

; use this to restrict the range to normal prime: [0, p)
(define (assert-range x) (assert (&& (>= x 0) (< x p))))

; use this to restrict the range to binary: {0, 1}
(define (assert-binary x) (assert (|| (= x 0) (= x 1))))

; disable modulo
; (define (modulo a b) a)

; mod eqv
(define (peqv x y) (= (modulo x p) (modulo y p)))

; define original variables
(define-symbolic x0 integer?)
(define-symbolic x1 integer?)
(define-symbolic x2 integer?)
(define-symbolic x3 integer?)
(define-symbolic x4 integer?)
(define-symbolic x5 integer?)
(define-symbolic x6 integer?)
(define-symbolic x7 integer?)
(assert-range x0)
(assert-binary x1) ; 0 or 1
(assert-binary x2) ; 0 or 1
(assert-range x3)
(assert-range x4)
(assert-range x5)
(assert-range x6)
(assert-binary x7) ; 0 or 1
(assert (= x0 1))

; define original constraints
(define c0 (peqv
    (* (+ (* 21888242871839275222246405745257275088548364400416034343698204186575808495616 x0) x1) x1)
    0
))
(define c1 (peqv
    (* (+ (* 21888242871839275222246405745257275088548364400416034343698204186575808495616 x0) x2) x2)
    0
))
(define c2 (peqv
    (* (+ (* 21888242871839275222246405745257275088548364400416034343698204186575808495616 x0) x7) x7)
    0
))
(define c3 (peqv
    0
    (+
        (* 2 x2)
        (* 4 x7)
        x5
        (* 21888242871839275222246405745257275088548364400416034343698204186575808495616 x3)
        (* 21888242871839275222246405745257275088548364400416034343698204186575808495613 x0)
        (* 21888242871839275222246405745257275088548364400416034343698204186575808495615 x4)
        (* 2 x6)
        x1
    )
))

; define alternative variables
(define-symbolic x1b integer?)
(define-symbolic x2b integer?)
(define-symbolic x7b integer?)
(assert-binary x1b) ; 0 or 1
(assert-binary x2b) ; 0 or 1
(assert-binary x7b) ; 0 or 1

; define alternative constraints
(define c0b (peqv
    (* (+ (* 21888242871839275222246405745257275088548364400416034343698204186575808495616 x0) x1b) x1b)
    0
))
(define c1b (peqv
    (* (+ (* 21888242871839275222246405745257275088548364400416034343698204186575808495616 x0) x2b) x2b)
    0
))
(define c2b (peqv
    (* (+ (* 21888242871839275222246405745257275088548364400416034343698204186575808495616 x0) x7b) x7b)
    0
))
(define c3b (peqv
    0
    (+
        (* 2 x2b)
        (* 4 x7b)
        x5
        (* 21888242871839275222246405745257275088548364400416034343698204186575808495616 x3)
        (* 21888242871839275222246405745257275088548364400416034343698204186575808495613 x0)
        (* 21888242871839275222246405745257275088548364400416034343698204186575808495615 x4)
        (* 2 x6)
        x1b
    )
))

; with range analysis, z3 returns (unsat), which is verified
(define sol (solve (assert (&&
    c0 c1 c2 c3 c0b c1b c2b c3b
    (||
        (! (= x1 x1b))
        (! (= x2 x2b))
    )
))))
(printf "~a\n" sol)
