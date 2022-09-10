#lang rosette
; common require
(require json racket/engine
    (prefix-in tokamak: "./picus/tokamak.rkt")
    (prefix-in utils: "./picus/utils.rkt")
    (prefix-in config: "./picus/config.rkt")
    (prefix-in r1cs: "./picus/r1cs-grammar.rkt")
)
; z3 require
(require
    (prefix-in z3-solver: "./picus/z3-utils.rkt")
    (prefix-in z3-rint: "./picus/r1cs-z3-interpreter.rkt")
    (prefix-in z3-parser: "./picus/r1cs-z3-parser.rkt")
    (prefix-in z3-osimp: "./picus/optimizers/r1cs-z3-simple-optimizer.rkt")
    (prefix-in z3-oab0: "./picus/optimizers/r1cs-z3-AB0-optimizer.rkt")
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
(define (parser:parse-r1cs)
    (cond
        [(equal? "z3" arg-solver) z3-parser:parse-r1cs]
        [(equal? "cvc5" arg-solver) cvc5-parser:parse-r1cs]
        [else (tokamak:exit "you can't reach here")]
    )
)
(define (optimizer:optimize)
    (cond
        [(equal? "z3" arg-solver) (lambda (x) (z3-oab0:optimize-r1cs (z3-osimp:optimize-r1cs x)))]
        [(equal? "cvc5" arg-solver) (lambda (x) (cvc5-osimp:optimize-r1cs x))]
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
; load r1cs binary
(define r0 (r1cs:read-r1cs arg-r1cs))
(define nwires (r1cs:get-nwires r0))
(printf "# number of wires: ~a\n" nwires)
(printf "# number of constraints: ~a\n" (r1cs:get-mconstraints r0))
(printf "# field size (how many bytes): ~a\n" (r1cs:get-field-size r0))

; parse original r1cs
(printf "# parsing original r1cs...\n")
(define-values (xlist original-definitions original-cnsts) ((parser:parse-r1cs) r0 null)) ; interpret the constraint system
(define input-list (r1cs:r1cs-inputs r0))
(define output-list (r1cs:r1cs-outputs r0))
(printf "# inputs: ~a.\n" input-list)
(printf "# outputs: ~a.\n" output-list)
(printf "# xlist: ~a.\n" xlist)

; parse alternative r1cs
(define xlist0 (for/list ([i (range nwires)])
    (if (not (utils:contains? input-list i))
        (format "y~a" i)
        (list-ref xlist i)
    )
))
(printf "# xlist0: ~a.\n" xlist0)
(printf "# parsing alternative r1cs...\n")
(define-values (_ alternative-definitions alternative-cnsts) ((parser:parse-r1cs) r0 xlist0))

; assemble solve query
(printf "# assembling query...\n")
(define tmp0 (r1cs:rassert (r1cs:ror
    (filter (lambda (x) (! (null? x))) (for/list ([i (range nwires)])
        (if (utils:contains? output-list i)
            (r1cs:rneq (r1cs:rvar (list-ref xlist i)) (r1cs:rvar (list-ref xlist0 i)))
            null
        )
    ))
)))
(define query-cmds (r1cs:rcmds (list tmp0)))

(printf "# assembling final smt...\n")
(define final-cmds (r1cs:append-rcmds
    (r1cs:rcmds (list
        ; (note) setlogic needs to go first so optimizer can detect it
        (r1cs:rlogic (r1cs:rstr (solver:get-theory)))
    ))
    (r1cs:rcmds (list
        (r1cs:rcmt (r1cs:rstr "================================"))
        (r1cs:rcmt (r1cs:rstr "======== original block ========"))
        (r1cs:rcmt (r1cs:rstr "================================"))
    ))
    original-definitions
    original-cnsts
    (r1cs:rcmds (list
        (r1cs:rcmt (r1cs:rstr "==================================="))
        (r1cs:rcmt (r1cs:rstr "======== alternative block ========"))
        (r1cs:rcmt (r1cs:rstr "==================================="))
    ))
    alternative-definitions
    alternative-cnsts
    (r1cs:rcmds (list
        (r1cs:rcmt (r1cs:rstr "============================="))
        (r1cs:rcmt (r1cs:rstr "======== query block ========"))
        (r1cs:rcmt (r1cs:rstr "============================="))
    ))
    query-cmds
    (r1cs:rcmds (list (r1cs:rsolve )))
))

; perform optimization
(define optimized-cmds ((optimizer:optimize) final-cmds))
(define final-str (string-join ((rint:interpret-r1cs) optimized-cmds) "\n"))
; (printf "# final str is:\n~a\n" final-str)

; solve!
(define res ((solver:solve) final-str arg-timeout #:output-smt? arg-smt))
(if (equal? 'unsat (car res))
    (printf "# verified.\n")
    (printf "# failed / reason: ~a\n" res)
)