#lang racket
(require
  (prefix-in r1cs: "../picus/r1cs/r1cs-grammar.rkt")
  (prefix-in solver: "../picus/solver.rkt")
  (prefix-in simple: "../picus/optimizers/r1cs-z3-simple-optimizer.rkt")
)

(define range-vec (build-vector 10000 (lambda (x) 'bottom)))
(define comment-vec (build-vector 1000 (lambda (x) null)))
(define arg-solver "z3")

(define solve (solver:solve arg-solver))
(define parse-r1cs (solver:parse-r1cs arg-solver))
(define expand-r1cs (solver:expand-r1cs arg-solver))
(define normalize-r1cs (solver:normalize-r1cs arg-solver))
(define optimize-r1cs-p0 (solver:optimize-r1cs-p0 arg-solver))
(define optimize-r1cs-p1 (solver:optimize-r1cs-p1 arg-solver))
(define interpret-r1cs (solver:interpret-r1cs arg-solver))

; (define r0 (r1cs:read-r1cs "../benchmarks/circomlib-cff5ab6/BabyDbl@babyjub.r1cs"))
; (define r0 (r1cs:read-r1cs "../benchmarks/circomlib-cff5ab6/CompConstant@compconstant.r1cs"))
(define r0 (r1cs:read-r1cs "../benchmarks/circomlib-cff5ab6/Sign@sign.r1cs"))
(define-values (xlist options defs cnsts) (parse-r1cs r0 null))

; ==== first apply optimization phase 0 ====
(define p0cnsts (optimize-r1cs-p0 cnsts))

; ==== then expand the constraints ====
(define expcnsts (expand-r1cs p0cnsts))

; ==== then normalize the constraints ====
(define nrmcnsts (normalize-r1cs expcnsts))

; ==== then apply optimization phase 1 ====
(define p1cnsts (optimize-r1cs-p1 nrmcnsts #t)) ; include p defs

(simple:optimize-r1cs (r1cs:rcmds-ref nrmcnsts 500))