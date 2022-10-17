#lang rosette
; common require
(require json racket/engine
    (prefix-in tokamak: "./picus/tokamak.rkt")
    (prefix-in utils: "./picus/utils.rkt")
    (prefix-in config: "./picus/config.rkt")
    (prefix-in solver: "./picus/solver.rkt")
    (prefix-in r1cs: "./picus/r1cs/r1cs-grammar.rkt")
    (prefix-in pp: "./picus/algorithms/pp.rkt")
)

; =====================================
; ======== commandline parsing ========
; =====================================
; parse command line arguments
(define arg-r1cs null)
(define arg-solver "z3")
(define arg-timeout 5000)
(define arg-smt #f)
(define arg-weak #f)
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
)
(printf "# r1cs file: ~a\n" arg-r1cs)
(printf "# timeout: ~a\n" arg-timeout)
(printf "# solver: ~a\n" arg-solver)
(printf "# solver: ~a\n" arg-solver)
(printf "# smt: ~a\n" arg-smt)
(printf "# weak: ~a\n" arg-weak)

; =================================================
; ======== resolve solver specific methods ========
; =================================================
(define state-smt-path (solver:state-smt-path arg-solver))
(define solve (solver:solve arg-solver))
(define parse-r1cs (solver:parse-r1cs arg-solver))
(define normalize (solver:normalize arg-solver))
(define optimize (solver:optimize arg-solver))
(define interpret-r1cs (solver:interpret-r1cs arg-solver))

; ==================================
; ======== main preparation ========
; ==================================
(define r0 (r1cs:read-r1cs arg-r1cs))
(define nwires (r1cs:get-nwires r0))
(define mconstraints (r1cs:get-mconstraints r0))
(printf "# number of wires: ~a\n" nwires)
(printf "# number of constraints: ~a\n" mconstraints)
(printf "# field size (how many bytes): ~a\n" (r1cs:get-field-size r0))

; parse original r1cs
(printf "# parsing original r1cs...\n")
(define-values (xlist original-options original-definitions original-cnsts) (parse-r1cs r0 null)) ; interpret the constraint system
(define input-list (r1cs:r1cs-inputs r0))
(define input-set (list->set input-list))
(define output-list (r1cs:r1cs-outputs r0))
(define output-set (list->set output-list))
(define target-set (if arg-weak (list->set output-list) (list->set (range nwires))))
(printf "# inputs: ~a.\n" input-list)
(printf "# outputs: ~a.\n" output-list)
(printf "# xlist: ~a.\n" xlist)
(printf "# targets: ~a.\n" target-set)

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

; ============================
; ======== main solve ========
; ============================
(define-values (res res-ks res-us res-info) (pp:apply-pp
    r0 nwires mconstraints input-set output-set target-set
    xlist original-options original-definitions original-cnsts
    xlist0 alternative-definitions alternative-cnsts
    arg-timeout arg-smt
    solve state-smt-path parse-r1cs normalize optimize interpret-r1cs
))
(printf "# final unknown set ~a.\n" res-us)
(if arg-weak
    (printf "# weak uniqueness: ~a.\n" res)
    (printf "# strong uniqueness: ~a.\n" res)
)