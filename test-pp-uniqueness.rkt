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
    ;(prefix-in z3-bounds: "./picus/optimizers/r1cs-z3-Bounds-optimizer.rkt")
)
; cvc5 require
(require
    (prefix-in cvc5-solver: "./picus/cvc5-utils.rkt")
    (prefix-in cvc5-rint: "./picus/r1cs-cvc5-interpreter.rkt")
    (prefix-in cvc5-parser: "./picus/r1cs-cvc5-parser.rkt")
    (prefix-in cvc5-osimp: "./picus/optimizers/r1cs-cvc5-simple-optimizer.rkt")
    (prefix-in cvc5-brep: "./picus/optimizers/r1cs-cvc5-base-representation-optimizer.rkt")
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
(define (optimizer:get-base-representation)
    (cond
        [(equal? "z3" arg-solver) '()]
        [(equal? "cvc5" arg-solver) (lambda (x)
            (cvc5-brep:get-base-representations x)
        )]
        [else (tokamak:exit "you can't reach here")]
    )
)
(define (optimizer:generate-base-representations-constraints)
    (cond
        [(equal? "z3" arg-solver) '()]
        [(equal? "cvc5" arg-solver) (lambda (x y)
            (cvc5-brep:generate-base-representations-constraints x y)
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

; parse signal2constraints and constraints2signals
(define signal2constraints (r1cs:compute-signal2constraints r0))
(define constraint2signals (r1cs:compute-constraint2signals r0))
(define constraint2solvablesignals (r1cs:compute-constraint2solvablesignals r0))
(printf "# map from signal to constraints: ~a\n" signal2constraints)
(printf "# map from constraints to signals: ~a\n" constraint2signals)
(printf "# map from constraints to solvable signals: ~a\n" constraint2solvablesignals)

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

(define optimized-original-cnsts ((optimizer:optimize) original-cnsts))
(define optimized-alternative-cnsts ((optimizer:optimize) alternative-cnsts))

; to generate the constraints checking for base-representations
(define base-representations-original ((optimizer:get-base-representation) optimized-original-cnsts))
(define base-representations-alternative ((optimizer:get-base-representation) optimized-alternative-cnsts))
;(printf "# Base representations original: ~a.\n" base-representations-original)
;(printf "# Base representations alternative: ~a.\n" base-representations-alternative)
(define constraints-base-representations 
    ((optimizer:generate-base-representations-constraints) 
        base-representations-original
        base-representations-alternative
    )
)
(printf "# New constraints: ~a.\n" constraints-base-representations)


(define partial-cmds (r1cs:append-rcmds
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
        (r1cs:rcmt (r1cs:rstr "================================"))
        (r1cs:rcmt (r1cs:rstr "========= Added lemmas ========="))
        (r1cs:rcmt (r1cs:rstr "================================"))
    ))
    constraints-base-representations

    ))

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


; compute the level-1 neighbors of the signals
; (not taking into account as neighbors the known signals)
(define (compute-signal2neighborconstraints signal known)   
    (foldl 
       (lambda (x y) 
            (set-union y (foldl (lambda (x1 y1) (
                set-union y1 (if (utils:contains? known-list x1) '() (list-ref signal2constraints x1))))
                '()
                (list-ref constraint2signals x)
            ) )
        )
        (list-ref signal2constraints signal)
        (list-ref signal2constraints signal)
    )
) 

; generate a smt file containing the constraints of the set s
(define (partial-cmds-list list-c) 
    (r1cs:append-rcmds
        (r1cs:rcmds 
            (list (r1cs:rassert (r1cs:req
            (r1cs:rint 1) (r1cs:rvar (format "~a" (list-ref xlist 0)))
            )))
        )
        (r1cs:rcmds (list
            (r1cs:rcmt (r1cs:rstr "================================"))
            (r1cs:rcmt (r1cs:rstr "======== original block ========"))
            (r1cs:rcmt (r1cs:rstr "================================"))
        ))
        original-definitions
        (r1cs:get-subset-cmds original-cnsts list-c)
        (r1cs:rcmds (list
            (r1cs:rcmt (r1cs:rstr "==================================="))
            (r1cs:rcmt (r1cs:rstr "======== alternative block ========"))
            (r1cs:rcmt (r1cs:rstr "==================================="))
        ))
        alternative-definitions
        (r1cs:get-subset-cmds alternative-cnsts list-c)
        (r1cs:rcmds (list
        (r1cs:rcmt (r1cs:rstr "================================"))
        (r1cs:rcmt (r1cs:rstr "========= Added lemmas ========="))
        (r1cs:rcmt (r1cs:rstr "================================"))
        ))
        constraints-base-representations
    )
)

(define (partial-cmds-signal-level0 s)  
    (partial-cmds-list (list-ref signal2constraints s))
)

(define (partial-cmds-signal-level1 s) 
    (partial-cmds-list (compute-signal2neighborconstraints s input-list))
)

(define (partial-cmds-signal-level1known s known) 
    (partial-cmds-list (compute-signal2neighborconstraints s known))
)

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

(define (get-bounded-signals constraints2ukn)
    (define bounded-constraints 
        (filter
            (lambda (x) 
                (= (length (list-ref constraints2ukn x)) 1)
            )
            (range mconstraints)
        )
    )
    (define bounded-signals
        (for/list ([cnst bounded-constraints])
            (car (list-ref constraints2ukn cnst))
        )
    )
    (values bounded-constraints bounded-signals) 
)

(define (get-order-promising-signals constraint2ukn ukn triedAndFailed)
    ;(printf "constraint2ukn: ~a\n" constraint2ukn)
    (define-values (bounded-constraints bounded-signals) (get-bounded-signals constraint2ukn))
    ;(printf "Bounded signals: ~a\n" bounded-signals)
    ;(printf "Bounded constraints: ~a\n" bounded-constraints)
    (define constraint2UnUkn 
        (for/list ([index mconstraints])
            (cond 
            [(utils:contains? bounded-constraints index) -2]
            [else 
                (define nUkn (length (list-ref constraint2ukn index)))
                (define nBoundedUkn (length 
                    (filter 
                        (lambda (x) (utils:contains? bounded-signals x))
                     (list-ref constraint2ukn index)
                    )
                ))
                (define nKnown (- (length (list-ref constraint2signals index)) (length (list-ref constraint2ukn index))))
                ;(printf "Known ~a Bounded ~a Ukn ~a\n" nKnown nBoundedUkn nUkn)
                (+ (* 0.1 nKnown) (* 0.5 nBoundedUkn) (- nUkn))
            ]
            )

        )
    )
    ;(printf "Constraint to points ~a\n" constraint2UnUkn)
    (define signal2totalPoints
        (for/list ([signal ukn])
            (define total-known
                (foldl 
                    (lambda (y x)(max x (list-ref constraint2UnUkn y)))
                    -1000
                    (list-ref signal2constraints signal)
                )
            )
            (define already-tried (utils:contains? triedAndFailed signal))
            (if already-tried
                (list signal (- total-known 100)) 
                (list signal total-known) 
            )
        )
    )
    ;(printf "Signal to points ~a\n" signal2totalPoints)
    (define order-signal-val (
        sort signal2totalPoints (lambda (x y) (> (list-ref x 1) (list-ref y 1))))
    )
    (for/list ([value order-signal-val])
        (list-ref value 0)
    )
)


(define (apply-complete-iteration known unknown constraint2ukn pot-easy tried-and-failed)
    (define-values (kn ukn c2ukn) (apply-propagation known unknown constraint2ukn pot-easy))
    (define promising-signals-ordered (get-order-promising-signals c2ukn ukn tried-and-failed))
    (printf "# ==== new round of SMT solvers ===\n")
    (define-values (signal-smt new-failures) (try-solve-smt promising-signals-ordered kn tried-and-failed))
    (cond
        [(>= signal-smt 0)
            (set! kn (cons signal-smt kn))
            (set! ukn (remove signal-smt ukn))
            (for ([pot-cnst (list-ref signal2constraints signal-smt)])
                (define new-value (remove signal-smt (list-ref c2ukn pot-cnst)))
                (set! c2ukn (list-set c2ukn pot-cnst new-value))
            )
            (if (null? ukn)
                null
                (if arg-weak
                    (if (utils:empty_inter? ukn output-list)
                        ukn
                        (apply-complete-iteration kn ukn c2ukn (list-ref signal2constraints signal-smt) new-failures)
                    )
                    (apply-complete-iteration kn ukn c2ukn (list-ref signal2constraints signal-smt) new-failures)
                )
            )
        ]
        [else ukn]
    )
)

(define (try-solve-smt promising-signals-ordered known tried-and-failed)
    (cond
        [(null? promising-signals-ordered) (values -1 '())]
        [else
            (cond
                [(try-solve-smt-single-signal (car promising-signals-ordered) known 0)
                    (values (car promising-signals-ordered) tried-and-failed)
                ]
                [else
                    (set! tried-and-failed (cons (car promising-signals-ordered) tried-and-failed))
                    (try-solve-smt (cdr promising-signals-ordered) known tried-and-failed)
                ]
            )
        
        ]
    )
)

(define (try-solve-smt-single-signal signal known level)
    (printf "  # checking: (~a ~a), " (list-ref xlist signal) (list-ref xlist0 signal))
    (define known-cmds (r1cs:rcmds (for/list ([j known])
        (r1cs:rassert (r1cs:req (r1cs:rvar (list-ref xlist j)) (r1cs:rvar (list-ref xlist0 j))))
    )))
    (define partial-cmds-level
        (cond
            [(= level 0) (partial-cmds-signal-level0 signal)]
            [(= level 1) (partial-cmds-signal-level1 signal)]
            [(= level 2) partial-cmds]
        )
    )
    (define final-cmds (r1cs:append-rcmds
        (r1cs:rcmds (list (r1cs:rlogic (r1cs:rstr (solver:get-theory)))))
        partial-cmds-level
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
            (cond 
                [(< level 2) 
                    (printf "sat\n")
                    (try-solve-smt-single-signal signal known (+ level 1))
                ]
                [ else
                    (printf "sat\n")
                    #f
                ]
            )
            
        ]
        [else
            (cond 
                [(< level 2) 
                    (printf "skip\n")
                    (try-solve-smt-single-signal signal known (+ level 1))
                ]
                [ else
                    (printf "skip\n")
                    #f
                ]
            )
        ]
    )
)

(define res-ul (apply-complete-iteration known-list unknown-list initial-constraint2ukn (range mconstraints) '()))
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
