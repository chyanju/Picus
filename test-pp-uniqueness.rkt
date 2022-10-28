#lang rosette
; common require
(require json racket/engine
    (prefix-in tokamak: "./picus/tokamak.rkt")
    (prefix-in utils: "./picus/utils.rkt")
    (prefix-in config: "./picus/config.rkt")
    (prefix-in solver: "./picus/solver.rkt")
    (prefix-in r1cs: "./picus/r1cs/r1cs-grammar.rkt")
    (prefix-in pp: "./picus/algorithms/pp.rkt")
    (prefix-in pre: "./picus/precondition.rkt")
)

; =====================================
; ======== commandline parsing ========
; =====================================
; parse command line arguments
(define arg-r1cs null)
(define arg-solver "z3")
(define arg-timeout 5000)
(define arg-precondition null)
(define arg-prop #t)
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
    [("--solver") p-solver "solver to use: z3 | cvc4 | cvc5 (default: z3)"
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
    [("--precondition") p-precondition "include precondition into the reasoning (default: false)"
        (begin
            (set! arg-precondition p-precondition)
        )
    ]
    [("--noprop") "disable propagation (default: false / propagation on)"
        (begin
            (set! arg-prop #f)
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
(printf "# propagation: ~a\n" arg-prop)
(printf "# smt: ~a\n" arg-smt)
(printf "# weak: ~a\n" arg-weak)
(printf "# precondition: ~a\n" arg-precondition)

; =================================================
; ======== resolve solver specific methods ========
; =================================================
(define state-smt-path (solver:state-smt-path arg-solver))
(define solve (solver:solve arg-solver))
(define parse-r1cs (solver:parse-r1cs arg-solver))
(define expand-r1cs (solver:expand-r1cs arg-solver))
(define normalize-r1cs (solver:normalize-r1cs arg-solver))
(define optimize-r1cs-p0 (solver:optimize-r1cs-p0 arg-solver))
(define optimize-r1cs-p1 (solver:optimize-r1cs-p1 arg-solver))
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

; categorize signals
(define input-list (r1cs:r1cs-inputs r0))
(define input-set (list->set input-list))
(define output-list (r1cs:r1cs-outputs r0))
(define output-set (list->set output-list))
(define target-set (if arg-weak (list->set output-list) (list->set (range nwires))))
(printf "# inputs: ~a.\n" input-list)
(printf "# outputs: ~a.\n" output-list)
(printf "# targets: ~a.\n" target-set)

; parse original r1cs
(printf "# parsing original r1cs...\n")
(define-values (xlist opts defs cnsts) (parse-r1cs r0 null)) ; interpret the constraint system
(printf "# xlist: ~a.\n" xlist)
; parse alternative r1cs
(define alt-xlist (for/list ([i (range nwires)])
    (if (not (utils:contains? input-list i))
        (format "y~a" i)
        (list-ref xlist i)
    )
))
(printf "# alt-xlist ~a.\n" alt-xlist)
(printf "# parsing alternative r1cs...\n")
(define-values (_ __ alt-defs alt-cnsts) (parse-r1cs r0 alt-xlist))

(printf "# configuring precondition...\n")
(define-values (unique-set precondition) (if (null? arg-precondition)
    (values (list->set (list)) null)
    ; read!
    (pre:read-precondition arg-precondition)
))
(printf "# unique: ~a.\n" unique-set)

; ============================
; ======== main solve ========
; ============================
; a full picus constraint pass is:
;   raw
;    | parse-r1cs
;    v
;  cnsts
;    | optimize-r1cs-p0
;    v
; p0cnsts
;    | expand-r1cs
;    v
; expcnsts
;    | normalize-r1cs
;    v
; nrmcnsts
;    | optimize-r1cs-p1
;    v
; p1cnsts
;    | (downstream queries)
;   ...
(define-values (res res-ks res-us res-info) (pp:apply-pp
    r0 nwires mconstraints
    input-set output-set target-set
    xlist opts defs cnsts
    alt-xlist alt-defs alt-cnsts
    unique-set precondition ; prior knowledge row
    arg-prop arg-timeout arg-smt
    solve state-smt-path interpret-r1cs
    parse-r1cs optimize-r1cs-p0 expand-r1cs normalize-r1cs optimize-r1cs-p1
))
(printf "# final unknown set ~a.\n" res-us)
(if arg-weak
    (printf "# weak uniqueness: ~a.\n" res)
    (printf "# strong uniqueness: ~a.\n" res)
)