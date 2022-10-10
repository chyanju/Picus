#lang rosette
; common require
(require json racket/engine
    (prefix-in tokamak: "./picus/tokamak.rkt")
    (prefix-in utils: "./picus/utils.rkt")
    (prefix-in config: "./picus/config.rkt")
    (prefix-in r1cs: "./picus/r1cs-grammar.rkt")
    (prefix-in pp: "./picus/algorithms/clara-pp.rkt")
)
; z3 require
(require
    (prefix-in z3-solver: "./picus/z3-utils.rkt")
    (prefix-in z3-rint: "./picus/r1cs-z3-interpreter.rkt")
    (prefix-in z3-parser: "./picus/r1cs-z3-parser.rkt")
    (prefix-in z3-osimp: "./picus/optimizers/r1cs-z3-simple-optimizer.rkt")
    (prefix-in z3-oab0: "./picus/optimizers/r1cs-z3-AB0-optimizer.rkt")
    ;(prefix-in z3-bounds: "./picus/optimizers/r1cs-z3-Bounds-optimizer.rkt")
)
; cvc5 require
(require
    (prefix-in cvc5-solver: "./picus/cvc5-utils.rkt")
    (prefix-in cvc5-rint: "./picus/r1cs-cvc5-interpreter.rkt")
    (prefix-in cvc5-parser: "./picus/r1cs-cvc5-parser.rkt")
    (prefix-in cvc5-osimp: "./picus/optimizers/r1cs-cvc5-simple-optimizer.rkt")
    ; note: cvc5 doesn't have AB0 optimizer, use template instead
)

; =====================================
; ======== commandline parsing ========
; =====================================
; stateful variable
(define state-smt-path null)
; parse command line arguments
(define arg-r1cs null)
(define arg-solver "z3")
(define arg-timeout 5000)
(define arg-smt #f)
(define arg-weak #f)
(define arg-model #f)
(command-line
    #:once-each
    [("--r1cs") p-r1cs "path to target r1cs"
        (begin
            (set! arg-r1cs p-r1cs)
            (when (! (string-suffix? arg-r1cs ".r1cs"))
                (tokamak:exit "file needs to be *.r1cs")
            )
        )
    ]
    [("--solver") p-solver "solver to use: z3 | cvc5 (default: z3)"
        (cond
            [(|| (equal? "z3" p-solver) (equal? "cvc5" p-solver)) (set! arg-solver p-solver)]
            [else (tokamak:exit "solver needs to be either z3 or cvc5")]
        )
    ]
    [("--timeout") p-timeout "timeout for every small query (default: 5000ms)"
        (begin
            (set! arg-timeout (string->number p-timeout))
        )
    ]
    [("--smt") "show path to generated smt files (default: false)"
        (begin
            (set! arg-smt #t)
        )
    ]
    [("--weak") "only check weak safety, not strong safety  (default: false)"
        (begin
            (set! arg-weak #t)
        )
    ]
    [("--get-model") "produce and print out counter example for every query (default: false)"
        (begin
            (set! arg-model #t)
        )
    ]
)
(printf "# r1cs file: ~a\n" arg-r1cs)
(printf "# timeout: ~a\n" arg-timeout)
(printf "# solver: ~a\n" arg-solver)

; =========================================
; ======== solver specific methods ========
; =========================================
(define (solver:get-theory)
    (cond
        [(equal? "z3" arg-solver) "QF_NIA"]
        [(equal? "cvc5" arg-solver) "QF_FF"]
        [else (tokamak:exit "you can't reach here")]
    )
)
(define (solver:solve)
    (cond
        [(equal? "z3" arg-solver) z3-solver:solve]
        [(equal? "cvc5" arg-solver) cvc5-solver:solve]
        [else (tokamak:exit "you can't reach here")]
    )
)
(define (solver:state-smt-path)
    (cond
        [(equal? "z3" arg-solver) z3-solver:state-smt-path]
        [(equal? "cvc5" arg-solver) cvc5-solver:state-smt-path]
        [else (tokamak:exit "you can't reach here")]
    )
)
(define (parser:parse-r1cs)
    (cond
        [(equal? "z3" arg-solver) z3-parser:parse-r1cs]
        [(equal? "cvc5" arg-solver) cvc5-parser:parse-r1cs]
        [else (tokamak:exit "you can't reach here")]
    )
)
(define (optimizer:optimize)
    (cond
        [(equal? "z3" arg-solver) (lambda (x) (
            z3-oab0:optimize-r1cs (z3-osimp:optimize-r1cs x)
            ))]
        [(equal? "cvc5" arg-solver) (lambda (x)
            (cvc5-osimp:optimize-r1cs x)
        )]
        [else (tokamak:exit "you can't reach here")]
    )
)
(define (rint:interpret-r1cs)
    (cond
        [(equal? "z3" arg-solver) z3-rint:interpret-r1cs]
        [(equal? "cvc5" arg-solver) cvc5-rint:interpret-r1cs]
        [else (tokamak:exit "you can't reach here")]
    )
)

; ======================
; ======== main ========
; ======================
(define r0 (r1cs:read-r1cs arg-r1cs))
(define nwires (r1cs:get-nwires r0))
(define mconstraints (r1cs:get-mconstraints r0))
(printf "# number of wires: ~a\n" nwires)
(printf "# number of constraints: ~a\n" mconstraints)
(printf "# field size (how many bytes): ~a\n" (r1cs:get-field-size r0))

; parse original r1cs
(printf "# parsing original r1cs...\n")
(define-values (xlist original-definitions original-cnsts) ((parser:parse-r1cs) r0 null)) ; interpret the constraint system
(define input-list (r1cs:r1cs-inputs r0))
(define output-list (r1cs:r1cs-outputs r0))
(printf "# inputs: ~a.\n" input-list)
(printf "# outputs: ~a.\n" output-list)
;(printf "# xlist: ~a.\n" xlist)

; parse alternative r1cs
(define xlist0 (for/list ([i (range nwires)])
    (if (not (utils:contains? input-list i))
        (format "y~a" i)
        (list-ref xlist i)
    )
))
;(printf "# xlist0: ~a.\n" xlist0)
(printf "# parsing alternative r1cs...\n")
(define-values (_ alternative-definitions alternative-cnsts) ((parser:parse-r1cs) r0 xlist0))

(define res-ul (pp:apply-pp
    r0 nwires mconstraints input-list output-list
    xlist original-definitions original-cnsts
    xlist0 alternative-definitions alternative-cnsts
    arg-weak arg-timeout arg-smt arg-model
    solver:get-theory solver:solve solver:state-smt-path parser:parse-r1cs optimizer:optimize rint:interpret-r1cs
))
(printf "# final unknown list: ~a\n" res-ul)
(if (not arg-weak)
    (if (empty? res-ul)
        (printf "# Strong safety verified.\n")
        (printf "# Strong safey failed.\n")
    )
    (printf "# Weak flag activated: skipping check strong safey\n")
)

(if (utils:empty_inter? res-ul output-list)
    (printf "# Weak safety verified.\n")
    (printf "# Weak safey failed.\n")
)
