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
(define r0 (r1cs:read-r1cs arg-r1cs))
(define nwires (r1cs:get-nwires r0))
(printf "# number of wires: ~a\n" nwires)
(printf "# number of constraints: ~a\n" (r1cs:get-mconstraints r0))
(printf "# field size (how many bytes): ~a\n" (r1cs:get-field-size r0))

; parse original r1cs
(printf "# parsing original r1cs...\n")
(define-values (xlist original-cmds) ((parser:parse-r1cs) r0 null)) ; interpret the constraint system
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
(define-values (_ alternative-cmds) ((parser:parse-r1cs) r0 xlist0))

(define partial-cmds (r1cs:append-rcmds
    (r1cs:rcmds (list
        (r1cs:rcmt (r1cs:rstr "================================"))
        (r1cs:rcmt (r1cs:rstr "======== original block ========"))
        (r1cs:rcmt (r1cs:rstr "================================"))
    ))
    original-cmds
    (r1cs:rcmds (list
        (r1cs:rcmt (r1cs:rstr "==================================="))
        (r1cs:rcmt (r1cs:rstr "======== alternative block ========"))
        (r1cs:rcmt (r1cs:rstr "==================================="))
    ))
    alternative-cmds))

; keep track of index of xlist (not xlist0 since that's incomplete)
(define known-list (filter
    (lambda (x) (! (null? x)))
    (for/list ([i (range nwires)])
        (if (utils:contains? xlist0 (list-ref xlist i))
            i
            null
        )
    )
))
(define unknown-list (filter
    (lambda (x) (! (null? x)))
    (for/list ([i (range nwires)])
        (if (utils:contains? xlist0 (list-ref xlist i))
            null
            i
        )
    )
))
(printf "# initial knwon-list: ~a\n" known-list)
(printf "# initial unknown-list: ~a\n" unknown-list)

; returns final unknown list, and if it's empty, it means all are known
; and thus verified
(define (inc-solve kl ul)
    (printf "# ==== new round inc-solve ===\n")
    (define tmp-kl (for/list ([i kl]) i))
    (define tmp-ul (list ))
    (define changed? #f)
    (for ([i ul])
        (printf "  # checking: (~a ~a), " (list-ref xlist i) (list-ref xlist0 i))
        (define known-cmds (r1cs:rcmds (for/list ([j tmp-kl])
            (r1cs:rassert (r1cs:req (r1cs:rvar (list-ref xlist j)) (r1cs:rvar (list-ref xlist0 j))))
        )))
        (define final-cmds (r1cs:append-rcmds
            (r1cs:rcmds (list (r1cs:rlogic (r1cs:rstr (solver:get-theory)))))
            partial-cmds
            (r1cs:rcmds (list
                (r1cs:rcmt (r1cs:rstr "============================="))
                (r1cs:rcmt (r1cs:rstr "======== known block ========"))
                (r1cs:rcmt (r1cs:rstr "============================="))
            ))
            known-cmds
            (r1cs:rcmds (list
                (r1cs:rcmt (r1cs:rstr "============================="))
                (r1cs:rcmt (r1cs:rstr "======== query block ========"))
                (r1cs:rcmt (r1cs:rstr "============================="))
            ))
            (r1cs:rcmds (list
                (r1cs:rassert (r1cs:rneq (r1cs:rvar (list-ref xlist i)) (r1cs:rvar (list-ref xlist0 i))))
                (r1cs:rsolve )
            ))
        ))
        ; perform optimization
        (define optimized-cmds ((optimizer:optimize) final-cmds))
        (define final-str (string-join ((rint:interpret-r1cs) optimized-cmds) "\n"))
        (define res ((solver:solve) final-str arg-timeout #:output-smt? #f))
        (cond
            [(equal? 'unsat (car res))
                (printf "verified.\n")
                (set! tmp-kl (cons i tmp-kl))
                (set! changed? #t)
            ]
            [(equal? 'sat (car res))
                (printf "sat.\n")
                (set! tmp-ul (cons i tmp-ul))
            ]
            [else
                (printf "skip.\n")
                (set! tmp-ul (cons i tmp-ul))
            ]
        )
        (when arg-smt
            (printf "    # smt path: ~a\n" (solver:state-smt-path)))
    )
    ; return
    (if changed?
        (inc-solve (reverse tmp-kl) (reverse tmp-ul))
        tmp-ul
    )
)

(define res-ul (inc-solve known-list unknown-list))
(printf "# final unknown list: ~a\n" res-ul)
(if (empty? res-ul)
    (printf "# Strong safety verified.\n")
    (printf "# Strong safey failed.\n")
)

(if (utils:empty_inter? res-ul output-list)
    (printf "# Weak safety verified.\n")
    (printf "# Weak safey failed.\n")
)
