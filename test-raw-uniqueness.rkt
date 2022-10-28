#lang rosette
; common require
(require json racket/engine
    (prefix-in tokamak: "./picus/tokamak.rkt")
    (prefix-in utils: "./picus/utils.rkt")
    (prefix-in config: "./picus/config.rkt")
    (prefix-in r1cs: "./picus/r1cs/r1cs-grammar.rkt")
    (prefix-in solver: "./picus/solver.rkt")
)

; =====================================
; ======== commandline parsing ========
; =====================================
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
            [(set-member? (set "z3" "cvc5" "cvc4") p-solver) (set! arg-solver p-solver)]
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
(printf "# smt: ~a\n" arg-smt)

; =================================================
; ======== resolve solver specific methods ========
; =================================================
(define state-smt-path (solver:state-smt-path arg-solver))
(define solve (solver:solve arg-solver))
(define parse-r1cs (solver:parse-r1cs arg-solver))
(define normalize-r1cs (solver:normalize-r1cs arg-solver))
(define optimize-r1cs (solver:optimize-r1cs arg-solver))
(define interpret-r1cs (solver:interpret-r1cs arg-solver))

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
(define-values (xlist original-options original-definitions original-cnsts) (parse-r1cs r0 null)) ; interpret the constraint system
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
(define-values (_ __ alternative-definitions alternative-cnsts) (parse-r1cs r0 xlist0))

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
(define final-cmds (r1cs:rcmds-append
    (r1cs:rcmds (list
        (r1cs:rcmt "================================")
        (r1cs:rcmt "======== original block ========")
        (r1cs:rcmt "================================")
    ))
    original-definitions
    original-cnsts
    (r1cs:rcmds (list
        (r1cs:rcmt "===================================")
        (r1cs:rcmt "======== alternative block ========")
        (r1cs:rcmt "===================================")
    ))
    alternative-definitions
    alternative-cnsts
    (r1cs:rcmds (list
        (r1cs:rcmt "=============================")
        (r1cs:rcmt "======== query block ========")
        (r1cs:rcmt "=============================")
    ))
    query-cmds
    (r1cs:rcmds (list (r1cs:rsolve )))
))

; perform optimization
(define optimized-cmds (optimize-r1cs (normalize-r1cs final-cmds)))
; add options at last
(define final-str (string-join (interpret-r1cs
    (r1cs:rcmds-append original-options optimized-cmds))
    "\n"
))

; solve!
(define res (solve final-str arg-timeout #:output-smt? arg-smt))
(if (equal? 'unsat (car res))
    (printf "# verified.\n")
    (printf "# failed / reason: ~a\n" res)
)