#lang racket
(require json
  (prefix-in pre: "../picus/precondition.rkt")
  (prefix-in int: "../picus/r1cs/r1cs-z3-interpreter.rkt")
)

(define out (pre:read-precondition "../benchmarks/circomlib-cff5ab6/BabyAdd@babyjub.pre.json"))
(int:interpret-r1cs (cdr (list-ref out 0)))