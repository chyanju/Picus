#lang rosette
(provide (prefix-out config: (all-defined-out)))

; the global field p as seen in: https://docs.circom.io/circom-language/basic-operators/#field-elements
; also used by ecne as seen in: reference: https://github.com/franklynwang/EcneProject/blob/master/src/R1CSConstraintSolver.jl#L10
(define p 21888242871839275222246405745257275088548364400416034343698204186575808495617)

; the number of significant bits of p
(define b 254)
; mask = 2^b - 1, used in bit operators: https://docs.circom.io/circom-language/basic-operators/#bitwise-operators
(define mask (- (expt 2 b) 1))

(define nbits 256) ; number of bits used for default bitvector
(define bvsym (string->symbol (format "bv~a" nbits))) ; default type (symbol) provided to tokamak fresh symbol
(define bv (bitvector nbits)) ; default type, bitvector

(define cap 100) ; default mhash capacity

; (fixme) quick fix for mul function to speed up

; uncomment this for normal mul
; (define (mul x y) 
;     (define res (bvmul x y))
;     (assert (&& (bvsge res x) (bvsge res y)))
;     res
; )

; uncomment this for uninterpreted mul
(define-symbolic smul (~> bv bv bv))
(define (mul x y) 
    (define res (smul x y))
    (assert (&& (bvsge res x) (bvsge res y)))
    res
)