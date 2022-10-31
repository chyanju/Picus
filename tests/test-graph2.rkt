#lang racket
(require csv-reading graph
  (prefix-in r1cs: "../picus/r1cs/r1cs-grammar.rkt")
  (prefix-in solver: "../picus/solver.rkt")
  (prefix-in cg: "../picus/algorithms/constraint-graph.rkt")
)

(define-values (ovec svec osvec) (cg:read-sym "../benchmarks/circomlib-cff5ab6/BitElementMulAny@escalarmulany.sym"))