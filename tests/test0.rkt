#lang racket
(require
  (prefix-in r1cs: "../picus/r1cs/r1cs-grammar.rkt")
  (prefix-in solver: "../picus/solver.rkt")
  (prefix-in pp: "../picus/algorithms/pp.rkt")
)

(define parse-r1cs (solver:parse-r1cs "z3"))
(define normalize (solver:normalize "z3"))

(define r0 (r1cs:read-r1cs "../benchmarks/circomlib-cff5ab6/BabyDbl@babyjub.r1cs"))
(define-values (xlist options defs cnsts) (parse-r1cs r0 null))
(define ocnsts (normalize cnsts))

(define vars (r1cs:get-assert-variables ocnsts))
(define vars-linear (r1cs:get-assert-variables/linear ocnsts))
(define vars-nonlinear (r1cs:get-assert-variables/nonlinear ocnsts))
(printf "linear vars: ~a\n" vars-linear)
(printf "nonlinear vars: ~a\n" vars-nonlinear)

(define n (length (r1cs:rcmds-vs ocnsts)))
(for ([i (range n)]) (printf "~a\n" (r1cs:rcmds->string ocnsts i)))

; (define cdmap (pp:get-cdmap ocnsts))
(define rcdmap (pp:get-rcdmap ocnsts #t))
(for ([key (hash-keys rcdmap)]) (printf "~a => ~a\n" key (hash-ref rcdmap key)))