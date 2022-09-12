#lang rosette
; this implements the propagation & preserving algorithm with base lemma
(require
    (prefix-in tokamak: "../tokamak.rkt")
    (prefix-in utils: "../utils.rkt")
    (prefix-in config: "../config.rkt")
    (prefix-in r1cs: "../r1cs/r1cs-grammar.rkt")
)
(provide (rename-out
    [apply-inc apply-inc]
))

(define (apply-inc
    r0 nwires mconstraints input-list output-list
    xlist original-options original-definitions original-cnsts
    xlist0 alternative-definitions alternative-cnsts
    arg-timeout arg-smt
    solve state-smt-path parse-r1cs optimize interpret-r1cs
    )
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
            (define optimized-cmds (optimize final-cmds))
            (define final-str (string-join (interpret-r1cs
                (r1cs:append-rcmds original-options optimized-cmds))
                "\n"
            ))
            (define res (solve final-str arg-timeout #:output-smt? #f))
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
                (printf "    # smt path: ~a\n" (state-smt-path)))
        )
        ; return
        (if changed?
            (inc-solve (reverse tmp-kl) (reverse tmp-ul))
            tmp-ul
        )
    )

    (define res-ul (inc-solve known-list unknown-list))
    ; return
    res-ul
)