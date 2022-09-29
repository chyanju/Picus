#lang rosette
; this implements the propagation & preserving algorithm with base lemma
(require
    (prefix-in tokamak: "../tokamak.rkt")
    (prefix-in utils: "../utils.rkt")
    (prefix-in config: "../config.rkt")
    (prefix-in r1cs: "../r1cs/r1cs-grammar.rkt")
)
(provide (rename-out
    [get-cdmap get-cdmap]
    [get-rcdmap get-rcdmap]
    [pp-propagate pp-propagate]
    [apply-pp apply-pp]
))

; get constraint dependency map
; input is the *normalized main constraint part* of r1cs ast
;   - main constraints is the `cnsts part (r1cs:rcmds) from parse-r1cs
; returns a map of:
;   - key: index of a variable
;   - val: list of sets of variables
; meaning: if a key wants to be determined as unique,
;          one of the sets from val should be completely determined
; construction rules (++terms):
;   - only non-non-linear (YES, no typo here) variable can be determined (put to key)
;     because for x*y=k, x can't be guaranteed to be unique,
;     even if knowing y and k (due to field mul)
(define (get-cdmap arg-cnsts [arg-indexonly #f])
    (define res (make-hash))
    (for ([p (r1cs:rcmds-vs arg-cnsts)])
        (define all-vars (r1cs:get-assert-variables p arg-indexonly))
        (define nonlinear-vars (r1cs:get-assert-variables/nonlinear p arg-indexonly))
        ; (note) you can't use linears directly, because one var could be both linear and non-linear
        ;        in this case, it's still non-linear in the current constraint
        (define deducible-vars (set-subtract all-vars nonlinear-vars))
        (for ([key deducible-vars])
            (when (! (hash-has-key? res key)) (hash-set! res key (list )))
            (hash-set! res key (cons (set-subtract all-vars (list->set (list key))) (hash-ref res key)))
        )
    )
    res
)
; get a reversed cdmap
;   - arg-indexonly: whether to extract the indices instead of keeping the full variable name
; example output:
;   #<set: x10> => #<set: x4>
;   #<set: x6 x14 x12 x11> => #<set: x13>
;   #<set: x5 x14 x12> => #<set: x11>
;   #<set: x5 x14 x11> => #<set: x12>
;   #<set: x2> => #<set: x6>
;   #<set: x8> => #<set: x4>
;   #<set: x1> => #<set: x5>
;   #<set: x9> => #<set: x3>
;   #<set: x7> => #<set: x3>
(define (get-rcdmap arg-cnsts [arg-indexonly #f])
    (define res (get-cdmap arg-cnsts arg-indexonly))
    (define new-res (make-hash))
    (for ([key (hash-keys res)])
        (define vals (hash-ref res key))
        (for ([val vals])
            (when (! (hash-has-key? new-res val)) (hash-set! new-res val (list )))
            (hash-set! new-res val (cons key (hash-ref new-res val)))
        )
    )
    ; make immutable
    (for ([key (hash-keys new-res)])
        (hash-set! new-res key (list->set (hash-ref new-res key)))
    )
    new-res
)

; recursive
(define (pp-propagate rcdmap ks us)
    (printf "  # propagation: ")
    (define new-ks (list->set (set->list ks))) ; (fixme) do this to copy into a mutable set, required by set-* operations
    (define new-us (list->set (set->list us))) ; (fixme) same as above
    (define rec? #f) ; whether propagate should be called again
    (for* ([key (hash-keys rcdmap)])
        (when (set-empty? (set-subtract key ks))
            ; all ks are in key, propagate
            (set! new-ks (set-union new-ks (hash-ref rcdmap key)))
            (set! new-us (set-subtract new-us (hash-ref rcdmap key)))
        )
    )
    (let ([s0 (set-subtract new-ks ks)])
        (if (set-empty? s0)
            (printf "none.\n")
            (printf "~a added.\n" s0)
        )
    )
    (if (= (set-count ks) (set-count new-ks))
        ; no updates, return now
        (values new-ks new-us)
        ; has updates, call again
        (pp-propagate rcdmap new-ks new-us)
    )
)


(define state-rcdkey-counter null) ; cached rcdkey counter, key: index, val: count
(define state-blame-counter null) ; adjustment weight, key: index, val: weight delta +
; key first select: select the key with higher appearance in rcdmap
(define (pp-select rcdmap uspool)
    ; check for existence of counter
    (when (null? state-rcdkey-counter)
        ; counter not created yet, create one
        (define tmp-counter (make-hash))
        (for ([keys (hash-keys rcdmap)])
            (for ([key keys])
                (when (! (hash-has-key? tmp-counter key)) (hash-set! tmp-counter key 0))
                (hash-set! tmp-counter key (+ 1 (hash-ref tmp-counter key)))
            )
        )
        (set! state-rcdkey-counter tmp-counter)
    )
    ; copy the counter and filter out non uspool ones
    (define tmp-counter (make-hash))
    (for ([key (hash-keys state-rcdkey-counter)])
        (when (set-member? uspool key)
            ; copy and calculate the weight
            (hash-set! tmp-counter key
                (+ (hash-ref state-rcdkey-counter key) (hash-ref state-blame-counter key))
            )
        )
    )
    ; sort and pick
    (define p0 (argmax cdr (hash->list tmp-counter)))
    ; return
    (car p0)
)
; naive select
; (define (pp-select rcdmap uspool) (set-first uspool))

(define (pp-solve
    arg-timeout arg-smt
    solve state-smt-path normalize optimize interpret-r1cs
    xlist xlist0 original-options partial-cmds
    ks us os sid
    )
    (printf "  # checking: (~a ~a), " (list-ref xlist sid) (list-ref xlist0 sid))
    ; assemble commands
    (define known-cmds (r1cs:rcmds (for/list ([j ks])
        (r1cs:rassert (r1cs:req (r1cs:rvar (list-ref xlist j)) (r1cs:rvar (list-ref xlist0 j))))
    )))
    (define final-cmds (r1cs:append-rcmds
        partial-cmds
        (r1cs:rcmds (list
            (r1cs:rcmt "=============================")
            (r1cs:rcmt "======== known block ========")
            (r1cs:rcmt "=============================")
        ))
        known-cmds
        (r1cs:rcmds (list
            (r1cs:rcmt "=============================")
            (r1cs:rcmt "======== query block ========")
            (r1cs:rcmt "=============================")
        ))
        (r1cs:rcmds (list
            (r1cs:rassert (r1cs:rneq (r1cs:rvar (list-ref xlist sid)) (r1cs:rvar (list-ref xlist0 sid))))
            (r1cs:rsolve )
        ))
    ))
    ; perform optimization
    (define optimized-cmds (optimize (normalize final-cmds)))
    (define final-str (string-join (interpret-r1cs
        (r1cs:append-rcmds original-options optimized-cmds))
        "\n"
    ))
    (define res (solve final-str arg-timeout #:output-smt? #f))
    (define solved? (cond
        [(equal? 'unsat (car res))
            (printf "verified.\n")
            ; verified
            #t
        ]
        [(equal? 'sat (car res))
            (printf "sat.\n")
            ; not verified
            #f
        ]
        [else
            (printf "skip.\n")
            ; possibly timeout, not verified
            #f
        ]
    ))
    (when arg-smt
        (printf "    # smt path: ~a\n" (state-smt-path)))
    ; return
    solved?
)

; uspool is usually initialized as us
(define (pp-select-and-solve
    arg-timeout arg-smt
    solve state-smt-path normalize optimize interpret-r1cs
    xlist xlist0 original-options partial-cmds
    rcdmap ks us os uspool
    )

    (if (set-empty? uspool)
        ; nothing more to choose, can't solve any in this iteration, main process fail
        ; return same ks & us
        (values ks us)
        ; else, set not empty, move forward
        (begin
            (define sid (pp-select rcdmap uspool))
            (define solved? (pp-solve
                arg-timeout arg-smt
                solve state-smt-path normalize optimize interpret-r1cs
                xlist xlist0 original-options partial-cmds
                ks us os sid
            ))
            (cond
                ; solved, update ks & us, then return
                [solved? (values (set-add ks sid) (set-remove us sid))]
                ; not solved, update uspool and recursively call again
                [else
                    ; decrease the weight of the selected id since it's not solved
                    (hash-set! state-blame-counter sid (- (hash-ref state-blame-counter sid) 1))
                    ; still has something to choose from, invoke recursively again
                    (pp-select-and-solve
                        arg-timeout arg-smt
                        solve state-smt-path normalize optimize interpret-r1cs
                        xlist xlist0 original-options partial-cmds
                        rcdmap ks us os (set-remove uspool sid)
                    )
                ]
            )
        )
    )
)

; perform one iteration of pp algorithm
;   - ks: known set
;   - us: unknown set
(define (pp-iteration
    arg-timeout arg-smt arg-weak
    solve state-smt-path normalize optimize interpret-r1cs
    xlist xlist0 original-options partial-cmds
    rcdmap ks us os
    )
    ; (printf "# new pp iteration.\n")
    ; first, propagate
    (define-values (new-ks new-us) (pp-propagate rcdmap ks us))
    ; then, select and solve
    (define-values (xnew-ks xnew-us) (pp-select-and-solve
        arg-timeout arg-smt
        solve state-smt-path normalize optimize interpret-r1cs
        xlist xlist0 original-options partial-cmds
        rcdmap new-ks new-us os new-us
    ))
    (if arg-weak
        (if (set-empty? (set-intersect os xnew-us))
            ; no output is unknown, return
            xnew-us
            ; still there's unknown output, continue
            (if (equal? xnew-us new-us)
                ; can't reduce any unknown any more, return
                xnew-us
                ; continue
                (pp-iteration
                    arg-timeout arg-smt arg-weak
                    solve state-smt-path normalize optimize interpret-r1cs
                    xlist xlist0 original-options partial-cmds
                    rcdmap xnew-ks xnew-us os
                )
            )
        )
        (if (equal? xnew-us new-us)
            ; can't reduce any unknown any more, return
            xnew-us
            ; continue
            (pp-iteration
                arg-timeout arg-smt arg-weak
                solve state-smt-path normalize optimize interpret-r1cs
                xlist xlist0 original-options partial-cmds
                rcdmap xnew-ks xnew-us os
            )
        )
    )
)

(define (apply-pp
    r0 nwires mconstraints input-set output-set
    xlist original-options original-definitions original-cnsts
    xlist0 alternative-definitions alternative-cnsts
    arg-timeout arg-smt arg-weak
    solve state-smt-path parse-r1cs normalize optimize interpret-r1cs
    )

    ; keep track of index of xlist (not xlist0 since that's incomplete)
    (define known-set (list->set (filter
        (lambda (x) (! (null? x)))
        (for/list ([i (range nwires)])
            (if (utils:contains? xlist0 (list-ref xlist i))
                i
                null
            )
        )
    )))
    (define unknown-set (list->set (filter
        (lambda (x) (! (null? x)))
        (for/list ([i (range nwires)])
            (if (utils:contains? xlist0 (list-ref xlist i))
                null
                i
            )
        )
    )))
    (printf "# initial known-set ~a\n" known-set)
    (printf "# initial unknown-set ~a\n" unknown-set)

    (define normalized-original-cnsts (normalize original-cnsts))
    (define normalized-alternative-cnsts (normalize alternative-cnsts))

    (define partial-cmds (r1cs:append-rcmds
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
    ))

    ; generate rcdmap
    (define rcdmap (get-rcdmap normalized-original-cnsts #t))
    (for ([key (hash-keys rcdmap)]) (printf "~a => ~a\n" key (hash-ref rcdmap key)))

    ; initialization of state: weights are all set to 0
    (set! state-blame-counter (make-hash))
    (for ([key (range nwires)]) (hash-set! state-blame-counter key 0))

    (pp-iteration
        arg-timeout arg-smt arg-weak
        solve state-smt-path normalize optimize interpret-r1cs
        xlist xlist0 original-options partial-cmds
        rcdmap known-set unknown-set output-set
    )
)