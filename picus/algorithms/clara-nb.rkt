#lang rosette
; this implements the propagation & preserving algorithm with base lemma
(require
    (prefix-in tokamak: "../tokamak.rkt")
    (prefix-in utils: "../utils.rkt")
    (prefix-in config: "../config.rkt")
    (prefix-in r1cs: "../r1cs-grammar.rkt")
)
(provide (rename-out
    [apply-nb apply-nb]
))

(define (is-rint-zero x)
    (if (r1cs:rint? x)
        (if (= 0 (r1cs:rint-v x))
            #t
            #f
        )
        #f
    )
)

(define (is-rint-one x)
    (if (r1cs:rint? x)
        (if (= 1 (r1cs:rint-v x))
            #t
            #f
        )
        #f
    )
)

(define (contains-rint-zero l)
    (if (null? l)
        #f
        (let ([x (car l)])
            (if (r1cs:rint? x)
                (if (= 0 (r1cs:rint-v x))
                    #t
                    (contains-rint-zero (cdr l))
                )
                (contains-rint-zero (cdr l))
            )
        )
    )
)

(define (get-single-coefficient v)
    (match v
        [(r1cs:rint v) (list v "x0")]
        [(r1cs:rvar v) (list 1 v)]
        [(r1cs:rmul vs) 
            (define l1 (get-single-coefficient (car vs)))
            (define l2 (get-single-coefficient (car (cdr vs))))
            (list (* (list-ref l1 0) (list-ref l2 0)) (list-ref l2 1))
        ]
        [else (tokamak:exit "not supported for single coefficient ~a" v)]
    )
)

(define (get-list-coefficients vs)
    (for/list ([v vs])
        (get-single-coefficient v)
    )
)

(define (check-base base sorted_coefs)
    (if (= (length sorted_coefs) 1)
        #t
        (if (= (modulo (* base (car sorted_coefs)) config:p) (car (cdr sorted_coefs)))
            (check-base base (cdr sorted_coefs))
            #f
        )
    )
)

(define (is-base-representation coefs-vars)
    (define sorted-coefs-vars (sort coefs-vars (lambda (x y) (< (list-ref x 0)  (list-ref y 0)))))

    (define sorted-coefs 
        (for/list ([v sorted-coefs-vars])
            (list-ref v 0)
        )
    )

    (define sorted-vars
        (for/list ([v sorted-coefs-vars])
            (string->number (substring (list-ref v 1) 1))
        )
    )

    (define pot_base (/ (car (cdr sorted-coefs)) (car sorted-coefs)))
    (if (> pot_base 1)
        (if (utils:contains? sorted-vars 0)
            (values #f 1 '())
            (values (check-base pot_base (cdr sorted-coefs)) pot_base sorted-vars)
        )
        (values #f 1 '())
    )
)

(define (get-potential-inits vs)
    (filter 
        (lambda (v) (and 
            (= 2 (length v)) 
            (or (= 1 (list-ref v 0)) (= (- config:p 1) (list-ref v 0))))
        )
        vs
    )
)

(define (generate-base-constraints vs)
    (define coefs (get-list-coefficients vs))
    (define potential-inits (get-potential-inits coefs))
    (define new-cnst '())
    (for ([init potential-inits])
        (define pos-coefs
            (filter
                (lambda (x) (not (string=? (car (cdr x)) (car (cdr init)))))
                (for/list ([elem coefs])
                    (list 
                        (if (= (car init) 1)
                            (- config:p (car elem))
                            (car elem)
                        )
                        (car (cdr elem))
                    )
                )
            )
        )
        (define-values (is-base base vars) (is-base-representation pos-coefs))
        (cond 
            [is-base (set! new-cnst (cons (list base vars (string->number (substring (list-ref init 1) 1))) new-cnst))]
        )
    )
    
    new-cnst
)

(define (get-base-representations arg-r1cs)
    ;(printf "Studying ~a\n" arg-r1cs)
    (match arg-r1cs

        ; command level
        ; probably the original block
        [(r1cs:rcmds vs) 
            (define new-reps (for/list ([v vs]) (get-base-representations v)))
            (foldl append (list) new-reps)
        ]
        
        [(r1cs:rassert v)(get-base-representations v)]

        ; sub-command level
        [(r1cs:req lhs rhs)
            (cond
                [(is-rint-zero lhs)
                    (match rhs
                        [(r1cs:radd vs)
                            ; apply lemma
                            (if (> (length vs) 2)
                                (generate-base-constraints vs)
                                '()
                            )
                            ;(printf "New cons: ~a\n" cnsts)
                        ]
                        [else '()]
                    )
                ]
                [(is-rint-zero rhs)
                    (match lhs
                        [(r1cs:radd vs)
                            ; apply lemma
                            (if (> (length vs) 2)
                                (generate-base-constraints vs)
                                '()
                            )
                        ]
                        [else '()]
                    )
                ]
                [else '()]
            )
        
        ]



        [(r1cs:rneq lhs rhs) (list)]
        [(r1cs:rleq lhs rhs) (list)]
        [(r1cs:rlt lhs rhs) (list)]
        [(r1cs:rgeq lhs rhs) (list)]
        [(r1cs:rgt lhs rhs) (list)]
        [(r1cs:rraw v) (list)]
        [(r1cs:rlogic v) (list)]
        [(r1cs:rdef v t) (list)]
        [(r1cs:rassert v) (list)]
        [(r1cs:rcmt v) (list)]
        [(r1cs:rsolve ) (list)]

        [(r1cs:rand vs) 
            (define new-reps (for/list ([v vs]) (get-base-representations v)))
            (foldl append (list) new-reps)
        ]
        [(r1cs:ror vs) 
            (list )
        ]
        [(r1cs:rstr v) (list )]

        [else (tokamak:exit "not supported for base representation: ~a" arg-r1cs)]
    )
)

(define (rebuild-addition vs)
    (r1cs:radd 
        (for/list ([v vs])
            (r1cs:rmul (list
                (r1cs:rint (list-ref v 0))
                (r1cs:rvar (list-ref v 1))
            ))
        )
    )
)

(define (belongs-to-base-field s base)
    (r1cs:req
        (r1cs:rmul(for/list [(pos (range base))]
            (r1cs:radd (list (r1cs:rint (- config:p pos)) (r1cs:rvar s)))
        ))
        (r1cs:rint 0)
    )
)

(define (generate-base-representations-constraints list-base-1 list-base-2)
    
    (define new-conds (for/list ([i (range (length list-base-1))])
        (define info-base-1 (list-ref list-base-1 i))
        (define base-1 (list-ref info-base-1 0))
        (define bounded-vars-1 (list-ref info-base-1 1))
        (define right-side-1 (list-ref info-base-1 2))

        (define info-base-2 (list-ref list-base-2 i))
        (define base-2 (list-ref info-base-2 0))
        (define bounded-vars-2 (list-ref info-base-2 1))
        (define right-side-2 (list-ref info-base-2 2))

        (assert (= base-1 base-2))

        (define base-assertions-1
            (r1cs:rand 
                (for/list ([x bounded-vars-1])
                    (belongs-to-base-field x base-1)
                )
            )
        )
        (define base-assertions-2 
            (r1cs:rand 
                (for/list ([x bounded-vars-2])
                    (belongs-to-base-field x base-1)
                )
            )
        )
        (define eq-assertion
            (r1cs:req
                (rebuild-addition right-side-1)
                (rebuild-addition right-side-2)
            )
        )
        (define impl-conditions
            (r1cs:rand (list base-assertions-1 base-assertions-2 eq-assertion))
        )

        (define impl-postconditions
            (r1cs:rand 
                (for/list ([i (range (length bounded-vars-2))])
                    (r1cs:req 
                        (r1cs:rvar (list-ref bounded-vars-1 i)) 
                        (r1cs:rvar (list-ref bounded-vars-2 i))
                    )
                )
            )
        )
        (r1cs:rassert (r1cs:rimp impl-conditions impl-postconditions))
    
    ))
    (r1cs:rcmds new-conds)
)

(define (compute-bounded-signals arg-r1cs)
    (define constraints (r1cs:get-constraints arg-r1cs))
    (define mconstraints (r1cs:get-mconstraints arg-r1cs))
    (define bounds (for/list ([cnst mconstraints])
        (r1cs:extract-bounded-signals (list-ref constraints cnst))
    ))
    (filter
        (lambda (x) (not (= (list-ref x 0) 0)))
        bounds
    )
)

(define (get-subset-cmds cmd l-values)
    (match cmd
        [(r1cs:rcmds vs)
            (r1cs:rcmds (for/list ([v l-values]) (list-ref vs v)))
        ]
        [else (tokamak:exit "error: not a list command ~a" cmd)]
    )
)

; ==============================================================================================
; ======== Propagation & Preserving with Neighboring Algorithm (Clara's Implementation) ========
; ==============================================================================================
; (note) for convenience this moves the entire context
;        because the original version is deeply merged into main context with
;        closures, global variables etc. that are hard to detach
(define (apply-nb
    r0 nwires mconstraints input-list output-list
    xlist original-definitions original-cnsts
    xlist0 alternative-definitions alternative-cnsts
    arg-weak arg-timeout arg-smt arg-initlvl
    solver:get-theory solver:solve solver:state-smt-path parser:parse-r1cs optimizer:optimize rint:interpret-r1cs
    )
    (printf "# computing mappings...\n")
    ; parse signal2constraints and constraints2signals
    (define signal2constraints (r1cs:compute-signal2constraints r0))
    (printf "# map from signal to constraints: ~a\n" signal2constraints)
    (define constraint2signals (r1cs:compute-constraint2signals r0))
    (printf "# map from constraints to signals: ~a\n" constraint2signals)
    (define constraint2solvablesignals (r1cs:compute-constraint2solvablesignals r0))
    (printf "# map from constraints to solvable signals: ~a\n" constraint2solvablesignals)

    (define optimized-original-cnsts ((optimizer:optimize) original-cnsts))
    (define optimized-alternative-cnsts ((optimizer:optimize) alternative-cnsts))

    ; to generate the constraints checking for base-representations
    (define base-representations (get-base-representations optimized-original-cnsts))
    (printf "# Base representations: ~a.\n" base-representations)

    ; to obtain the bounds for checking the base representations -> can be used by the solver
    (define bounded-signals (compute-bounded-signals r0))
    (printf "Bounded signals: ~a\n" bounded-signals)

    ;;; function to check if the bounds of a base representation are satisfied
    (define (is-valid-base-representation base elems bounds)
        (define are-valid-elems
        (for/list ([elem elems])
            (define-values (is-bounded bound) (utils:get-elem-map bounds elem))
            (match is-bounded
                [#f #f]
                [else 
                (< bound base)
                ]
            )
        )
        )
        (foldl (lambda (x y) (and x y)) #t are-valid-elems)
    )

    ;;; base representations where the bounds are verified
    ;;; in case the right side is unique, the elements at the left side is too
    (define valid-base-representations 
        (filter 
            (lambda (base-representation) (is-valid-base-representation 
                (list-ref base-representation 0) 
                (list-ref base-representation 1) 
                bounded-signals
            ))
            base-representations
        )
    )
    (printf "Valid Base Representations ~a\n" valid-base-representations)

    (define base2activation-signal
        (for/list ([base valid-base-representations])
            (list-ref base 2)
        )
    )

    (define base2propagation-signals
        (for/list ([base valid-base-representations])
            (filter 
                (lambda (x) (not (utils:contains? input-list x)))
                (list-ref base 1)
            )
        )
    )

    (printf "Base2Activation ~a\n" base2activation-signal)
    (printf "Base2Propagation ~a\n" base2propagation-signals)

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
            (get-subset-cmds original-cnsts list-c)
            (r1cs:rcmds (list
                (r1cs:rcmt (r1cs:rstr "==================================="))
                (r1cs:rcmt (r1cs:rstr "======== alternative block ========"))
                (r1cs:rcmt (r1cs:rstr "==================================="))
            ))
            alternative-definitions
            (get-subset-cmds alternative-cnsts list-c)

        )
    )

    ;;; to generate the cluster of constraints of a signal depending on the level
    (define (partial-cmds-signal-level0 s)
        (partial-cmds-list (list-ref signal2constraints s))
    )

    (define (partial-cmds-signal-level1 s)
        (partial-cmds-list (compute-signal2neighborconstraints s input-list))
    )

    (define (partial-cmds-signal-level1known s known)
        (partial-cmds-list (compute-signal2neighborconstraints s known))
    )


    ; applies the base checking to the different bases: in case the activation
    ; is unique then all the propagation signals are unique
    (define (apply-basis-lemma known unknown constraint2ukn used-basis)
        (printf "# ==== new round of applying lemmas ===\n")
        (define pot-easy '())
        (for ([index (range (length base2activation-signal))]) 
            (define pot-activation (list-ref base2activation-signal index))
            (cond
                [(and (not (utils:contains? used-basis index)) (utils:contains? known pot-activation))
                    (for ([pro-signal (list-ref base2propagation-signals index)])
                        (printf "# Verified uniqueness of signal ~a via unique basis reasoning\n" pro-signal)
                        (set! known (cons pro-signal known))
                        (set! unknown (remove pro-signal unknown))
                        (for ([pot-cnst (list-ref signal2constraints pro-signal)])
                            (define new-value (remove pro-signal (list-ref constraint2ukn pot-cnst)))
                            (set! constraint2ukn (list-set constraint2ukn pot-cnst new-value))
                        )
                        (set! pot-easy (append (list-ref signal2constraints pro-signal) pot-easy))
                    )
                    (set! used-basis (cons index used-basis))
                ]
            )
        )

        (values known unknown constraint2ukn pot-easy used-basis)
    )

    ;;; applies the propagation phase
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


    ;;; Functions related with the heuristics
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


    ;;; function that applies a complete iteration of the algorithm
    (define (apply-complete-iteration known unknown constraint2ukn pot-easy0 used-basis0 tried-and-failed)
        (define-values (kn0 ukn0 c2ukn0) 
            (apply-propagation known unknown constraint2ukn pot-easy0)
        )
        
        (define-values (kn ukn c2ukn pot-easy used-basis) 
            (apply-basis-lemma kn0 ukn0 c2ukn0 used-basis0)
        )

        (cond
            [(null? pot-easy)
                (cond
                    [(and arg-weak (utils:empty_inter? ukn output-list))
                        null
                    ]
                    [else
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
                                            (apply-complete-iteration kn ukn c2ukn (list-ref signal2constraints signal-smt) used-basis new-failures)
                                        )
                                        (apply-complete-iteration kn ukn c2ukn (list-ref signal2constraints signal-smt) used-basis new-failures)
                                    )
                                )
                            ]
                            [else ukn]
                        )
                    ]
                )
            ]
            [ else
                (apply-complete-iteration kn ukn c2ukn pot-easy used-basis tried-and-failed)
            ]
        )
    )

    ;;; function that applies the smt phase of the algorithm
    (define (try-solve-smt promising-signals-ordered known tried-and-failed)
        (cond
            [(null? promising-signals-ordered) (values -1 '())]
            [else
                (cond
                    [(try-solve-smt-single-signal (car promising-signals-ordered) known arg-initlvl)
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

    ;;; function that tries to verify the uniqueness of signal s, assuming that the signals in known are unique
    ;;; level indicates the cluster of constraints that it sends to the SMT solver
    (define (try-solve-smt-single-signal signal known level)
        (printf "  # checking: (~a ~a)@Lv.~a, " (list-ref xlist signal) (list-ref xlist0 signal) level)
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

    (define res-ul (apply-complete-iteration known-list unknown-list initial-constraint2ukn (range mconstraints) '() '()))
    ; return
    res-ul
)