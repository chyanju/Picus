#lang rosette
(require json racket/engine
    (prefix-in tokamak: "./tokamak.rkt")
)
; z3 require
(require
    (prefix-in z3-solver: "./solvers/z3-solver.rkt")
    (prefix-in z3-rint: "./r1cs/r1cs-z3-interpreter.rkt")
    (prefix-in z3-parser: "./r1cs/r1cs-z3-parser.rkt")
    ; optimizers
    (prefix-in z3-simple: "./optimizers/r1cs-z3-simple-optimizer.rkt")
    (prefix-in z3-subp: "./optimizers/r1cs-z3-subp-optimizer.rkt")
)
; cvc5 require
(require
    (prefix-in cvc5-solver: "./solvers/cvc5-solver.rkt")
    (prefix-in cvc5-rint: "./r1cs/r1cs-cvc5-interpreter.rkt")
    (prefix-in cvc5-parser: "./r1cs/r1cs-cvc5-parser.rkt")
    ; optimizers
    (prefix-in cvc5-simple: "./optimizers/r1cs-cvc5-simple-optimizer.rkt")
    (prefix-in cvc5-subp: "./optimizers/r1cs-cvc5-subp-optimizer.rkt")
)
(provide (rename-out
    [state-smt-path state-smt-path]
    [solve solve]
    [parse-r1cs parse-r1cs]
    [normalize normalize]
    [optimize optimize]
    [interpret-r1cs interpret-r1cs]
))

(define (state-smt-path arg-solver)
    (cond
        [(equal? "z3" arg-solver) (lambda () z3-solver:state-smt-path)]
        [(equal? "cvc5" arg-solver) (lambda () cvc5-solver:state-smt-path)]
        [else (tokamak:exit "you can't reach here")]
    )
)
(define (solve arg-solver)
    (cond
        [(equal? "z3" arg-solver) z3-solver:solve]
        [(equal? "cvc5" arg-solver) cvc5-solver:solve]
        [else (tokamak:exit "you can't reach here")]
    )
)
(define (parse-r1cs arg-solver)
    (cond
        [(equal? "z3" arg-solver) z3-parser:parse-r1cs]
        [(equal? "cvc5" arg-solver) cvc5-parser:parse-r1cs]
        [else (tokamak:exit "you can't reach here")]
    )
)
(define (normalize arg-solver)
    (cond
        [(equal? "z3" arg-solver) (lambda (x) (z3-simple:optimize-r1cs x))]
        [(equal? "cvc5" arg-solver) (lambda (x) (cvc5-simple:optimize-r1cs x))]
        [else (tokamak:exit "you can't reach here")]
    )
)
(define (optimize arg-solver)
    (cond
        [(equal? "z3" arg-solver) (lambda (x) (z3-subp:optimize-r1cs x))]
        [(equal? "cvc5" arg-solver) (lambda (x) (cvc5-subp:optimize-r1cs x))]
        [else (tokamak:exit "you can't reach here")]
    )
)
(define (interpret-r1cs arg-solver)
    (cond
        [(equal? "z3" arg-solver) z3-rint:interpret-r1cs]
        [(equal? "cvc5" arg-solver) cvc5-rint:interpret-r1cs]
        [else (tokamak:exit "you can't reach here")]
    )
)