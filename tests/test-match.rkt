#lang racket
(require
  (prefix-in r1cs: "../picus/r1cs/r1cs-grammar.rkt")
)

(define p (r1cs:radd (list (r1cs:rmul (list (r1cs:rint 3) (r1cs:rint 4))) (r1cs:rmul (list (r1cs:rint 5) (r1cs:rint 6))))) )

(match p
  [(r1cs:radd (list (r1cs:rmul (list m0 m1)) ...)) m0])