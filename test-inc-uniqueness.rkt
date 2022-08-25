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
(define mconstraints (r1cs:get-mconstraints r0))
(printf "# number of wires: ~a\n" nwires)
(printf "# number of constraints: ~a\n" mcons)
(printf "# field size (how many bytes): ~a\n" (r1cs:get-field-size r0))

; parse signal2constraints and constraints2signals
(define signal2constraints (r1cs:compute-signal2constraints r0))
(define constraint2signals (r1cs:compute-constraint2signals r0))
(define constraint2solvablesignals (r1cs:compute-constraint2solvablesignals r0))
(printf "# map from signal to constraints: ~a\n" signal2constraints)
(printf "# map from constraints to signals: ~a\n" constraint2signals)
(printf "# map from constraints to solvable signals: ~a\n" constraint2solvablesignals)

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


(printf "# initial known-list: ~a\n" known-list)
(printf "# initial unknown-list: ~a\n" unknown-list)


; initialize unknown sets for each constraint 
(define initial-constraint2ukn
    (for/list ([i mconstraints])
        (filter
            (lambda (signal) (
                utils:contains? 
                    unknown-list
                    signal   
            )) 
            (list-ref constraint2signals i)
        )
    )
)

(printf "# initial constraints2ukn ~a\n" initial-constraint2ukn)



(define (apply-propagation known unknown constraint2ukn pot-easy)
    
    (printf "# ==== new round of propagation ===\n")
    (for ([cnst pot-easy])
        (define ukn-set (list-ref constraint2ukn cnst))
        (set!-values (known unknown constraint2ukn) (cond 
            [(= (length ukn-set) 1) 
                (define only-signal (car ukn-set))
                (cond 
                    [(utils:contains? (list-ref constraint2solvablesignals cnst) only-signal)
                        (printf "# Verified uniqueness of signal ~a via constraint ~a\n" only-signal cnst)
                        (set! known (cons only-signal known))
                        (set! unknown (remove only-signal unknown))
                        (for ([pot-cnst (list-ref signal2constraints only-signal)])
                            (define new-value (remove only-signal (list-ref constraint2ukn pot-cnst)))
                            (set! constraint2ukn (list-set constraint2ukn pot-cnst new-value))
                        )
                        (apply-propagation known unknown constraint2ukn (list-ref signal2constraints only-signal))
                    ]
                    [else (values known unknown constraint2ukn)]
                )
            ]
            [else (values known unknown constraint2ukn)]
        ))
        
    )

    (values known unknown constraint2ukn) 
)


(define (get-order-promising-signals constraint2ukn ukn)
    (define constraint2numberknown 
        (for/list ([index mconstraints])
            (define nUkn (length (list-ref constraint2ukn index)))
            (define nKnown (- (length (list-ref constraint2signals index)) nUkn))
            nKnown
        )
    )
    (define signal2numberknown
        (for/list ([signal ukn])
            (define total-known
                (foldl 
                    (lambda (y x)(+ x (list-ref constraint2numberknown y)))
                    0
                    (list-ref signal2constraints signal)
                )
            )
            (list signal total-known) 
        )
    )    
    
    (define order-signal-val (
        sort signal2numberknown (lambda (x y) (> (list-ref x 1) (list-ref y 1))))
    )
    (for/list ([value order-signal-val])
        (list-ref value 0)
    )

)



(define (apply-complete-iteration known unknown constraint2ukn pot-easy)
    
    (define-values (kn ukn c2ukn) (apply-propagation known unknown constraint2ukn pot-easy))
    (define promising-signals-ordered (get-order-promising-signals c2ukn ukn))
    (printf "# ==== new round of SMT solvers ===\n")
    (define signal-smt (try-solve-smt promising-signals-ordered kn))
    (cond
        [(>= signal-smt 0)
            (set! kn (cons signal-smt kn))
            (set! ukn (remove signal-smt ukn))
            (for ([pot-cnst (list-ref signal2constraints signal-smt)])
                (define new-value (remove signal-smt (list-ref constraint2ukn pot-cnst)))
                (set! c2ukn (list-set constraint2ukn pot-cnst new-value))
            )
            (if (null? ukn)
                null
                (apply-complete-iteration kn ukn c2ukn (list-ref signal2constraints signal-smt))
            )
        ]
        [else ukn]
    )

)

(define (try-solve-smt promising-signals-ordered known)
    (if (null? promising-signals-ordered)
        -1
        (if (try-solve-smt-single-signal (car promising-signals-ordered) known)
            (car promising-signals-ordered)
            (try-solve-smt (cdr promising-signals-ordered) known)
        )
    )
)

(define (try-solve-smt-single-signal signal known)
    (printf "  # checking: (~a ~a), " (list-ref xlist signal) (list-ref xlist0 signal))
    (define known-cmds (r1cs:rcmds (for/list ([j known])
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
            (r1cs:rassert (r1cs:rneq (r1cs:rvar (list-ref xlist signal)) (r1cs:rvar (list-ref xlist0 signal))))
            (r1cs:rsolve )
        ))
    ))
    ; perform optimization
    (define optimized-cmds ((optimizer:optimize) final-cmds))
    (define final-str (string-join ((rint:interpret-r1cs) optimized-cmds) "\n"))
    (define res ((solver:solve) final-str arg-timeout #:output-smt? #f))
    (when arg-smt
    (printf "    # smt path: ~a\n" (solver:state-smt-path)))
    (cond
        [(equal? 'unsat (car res))
            (printf "verified.\n")
             #t
        ]
        [(equal? 'sat (car res))
            (printf "sat.\n")
            #f
        ]
        [else
            (printf "skip.\n")
            #f
        ]
    )
)


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

(define res-ul (apply-complete-iteration known-list unknown-list initial-constraint2ukn (range mconstraints)))
(printf "# final unknown list: ~a\n" res-ul)
(if (empty? res-ul)
    (printf "# Strong safety verified.\n")
    (printf "# Strong safey failed.\n")
)

(if (utils:empty_inter? res-ul output-list)
    (printf "# Weak safety verified.\n")
    (printf "# Weak safey failed.\n")
)
