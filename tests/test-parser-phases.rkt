#lang racket
(require
  (prefix-in r1cs: "../picus/r1cs/r1cs-grammar.rkt")
  (prefix-in parser: "../picus/r1cs/r1cs-z3-parser.rkt")
)

(define r0 (r1cs:read-r1cs "../benchmarks/circomlib-cff5ab6/BinSub@binsub.r1cs"))
(define-values (xlist opts defs cnsts) (parser:parse-r1cs r0 null))
(define expanded-cnsts (parser:expand-r1cs cnsts))

; (define-values (_xlist _opts _defs _cnsts) (parser:parse-r1cs-old r0 null))

; (r1cs:rcmds-ref cnsts 0)
; (printf "===\n")
; (r1cs:rcmds-ref expanded-cnsts 0)
; (equal? _cnsts expanded-cnsts)