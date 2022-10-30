#lang racket
; this implements the decide & propagate verification loop algorithm
(require
    (prefix-in tokamak: "../tokamak.rkt")
    (prefix-in utils: "../utils.rkt")
    (prefix-in config: "../config.rkt")
    (prefix-in r1cs: "../r1cs/r1cs-grammar.rkt")
    (prefix-in selector: "./selector.rkt")
    ; lemmas
    (prefix-in l0: "./lemmas/linear-lemma.rkt")
    (prefix-in l1: "./lemmas/binary01-lemma.rkt")
)
(provide (rename-out
    [apply-algorithm apply-algorithm]
))

; ======== module global variables ======== ;

; selector series, need arg-selector to resolve
(define apply-selector null)
(define selector-feedback null)
(define selector-init null)

; this is the selector context provided to every apply-selector call
; grab the current context, then pack and return
(define (selector-context) (make-hash (list
    (cons 'rcdmap (l0:compute-rcdmap :sdmcnsts #t))
)))

; problem pack, needs to be set and initialized by apply- function
(define :r0 null)
(define :nwires null)
(define :mconstraints null)
(define :input-set null)
(define :output-set null)
(define :target-set null)

(define :xlist null)
(define :opts null)
(define :defs null)
(define :cnsts null) ; standard form
(define :sdmcnsts null) ; normalized standard form (specifically for rcdmap, original only)
(define :p0cnsts null) ; standard form optimized by phase 0 optimization
(define :expcnsts null) ; expanded form
(define :nrmcnsts null) ; normalized form
(define :p1cnsts null) ; normalized form optimized by phase 1 optimization

(define :alt-xlist null)
(define :alt-defs null)
(define :alt-cnsts null)
(define :alt-p0cnsts null)
(define :alt-expcnsts null)
(define :alt-nrmcnsts null)
(define :alt-p1cnsts null)

(define :arg-selector null)
(define :arg-prop null)
(define :arg-timeout null)
(define :arg-smt null)

(define :unique-set null)
(define :precondition null)

(define :solve null)
(define :state-smt-path null)
(define :interpret-r1cs null)

(define :parse-r1cs null)
(define :optimize-r1cs-p0 null)
(define :expand-r1cs null)
(define :normalize-r1cs null)
(define :optimize-r1cs-p1 null)

; problem intermediate results
(define :partial-cmds null)

; more specific range for all signals, potential values are (from abstract to concrete):
;   - 'bottom: it's {0, ..., p-1} (everything)
;   - a set of potential values
; (note) this tracks the range, not the uniqueness status, they are different
(define :range-vec null)

; main solving procedure
; returns:
;   - (values 'verified info): the given query is verified
;   - (values 'sat info): the given query has a counter-example (not verified)
;   - (values 'skip info): the given query times out (small step)
(define (dpvl-solve ks us sid)
    (printf "  # checking: (~a ~a), " (list-ref :xlist sid) (list-ref :alt-xlist sid))
    ; assemble commands
    (define known-cmds (r1cs:rcmds (for/list ([j ks])
        (r1cs:rassert (r1cs:req (r1cs:rvar (list-ref :xlist j)) (r1cs:rvar (list-ref :alt-xlist j))))
    )))
    (define final-cmds (r1cs:rcmds-append
        :partial-cmds
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
            (r1cs:rassert (r1cs:rneq (r1cs:rvar (list-ref :xlist sid)) (r1cs:rvar (list-ref :alt-xlist sid))))
            (r1cs:rsolve )
        ))
    ))
    ; perform optimization
    (define final-str (string-join (:interpret-r1cs
        (r1cs:rcmds-append :opts final-cmds))
        "\n"
    ))
    (define res (:solve final-str :arg-timeout #:output-smt? #f))
    (define solved? (cond
        [(equal? 'unsat (car res))
            (printf "verified.\n")
            ; verified, safe
            'verified
        ]
        [(equal? 'sat (car res))
            ; (important) here if the current signal is not a target, it's ok to see a sat
            (if (set-member? :target-set sid)
                ; the current signal is a target, now there's a counter-example, unsafe
                ; in pp, this counter-example is valid
                (begin (printf "sat.\n") 'sat)
                ; not a target, fine, just skip
                (begin (printf "sat but not a target.\n") 'skip)
            )
        ]
        [else
            (printf "skip.\n")
            ; possibly timeout in small step, result is unknown
            'skip
        ]
    ))
    (when :arg-smt
        (printf "    # smt path: ~a\n" (:state-smt-path)))
    ; return
    (values solved? (cdr res))
)

; select and solve
; returns:
;   - (values 'normal ks us info)
;   - (values 'break ks us info)
;   (note) since it's called recursively, at some level it could have new different ks with 'break
;          in that case you still break since a counter-example is already found
; uspool is usually initialized as us
(define (dpvl-select-and-solve ks us uspool)
    (cond
        [(set-empty? uspool)
            ; can't solve any more signal in this iteration
            (values 'normal ks us null)
        ]
        ; else, set not empty, move forward
        [else
            (define sid (apply-selector uspool (selector-context)))
            (define-values (solved? info) (dpvl-solve ks us sid))
            ; send feedback to selector
            (selector-feedback sid solved?)
            (cond
                ; solved, update ks & us, then return
                [(equal? 'verified solved?) (values 'normal (set-add ks sid) (set-remove us sid) null)]
                ; found a counter-example here, forced stop, nothing more to solve
                ; return the same ks & us to indicate the caller to stop
                [(equal? 'sat solved?) (values 'break ks us info)]
                ; unknown or timeout, update uspool and recursively call again
                [(equal? 'skip solved?) (dpvl-select-and-solve ks us (set-remove uspool sid))]
                [else (tokamak:error "unsupported solved? value, got: ~a." solved?)]
            )
        ]
    )
)

; (define tmp-inspect (list 512 513 514 515 516 517 518 519 384 385 386 387 388 389 390 391 392 393 394 395 396 397 398 399 400 401 402 403 404 405 406 407 408 409 410 411 412 413 414 415 416 417 418 419 420 421 422 423 424 425 426 427 428 429 430 431 432 433 434 435 436 437 438 439 440 441 442 443 444 445 446 447 448 449 450 451 452 453 454 455 456 457 458 459 460 461 462 463 464 465 466 467 468 469 470 471 472 473 474 475 476 477 478 479 480 481 482 483 484 485 486 487 488 489 490 491 492 493 494 495 496 497 498 499 500 501 502 503 504 505 506 507 508 509 510 511))

; recursively apply all lemmas until fixed point
(define (dpvl-propagate ks us)
    ; (printf "range-vec[inspect]: ~a\n" (for/list ([i tmp-inspect]) (vector-ref :range-vec i)))

    (define tmp-ks (list->set (set->list ks)))
    (define tmp-us (list->set (set->list us)))

    ; prepare lemma 0
    ; generate rcdmap requires no optimization to exclude ror and rand
    ; rcdmap requires normalized constraints to get best results
    (define rcdmap (l0:compute-rcdmap :sdmcnsts #t))
    ; (for ([key (hash-keys rcdmap)]) (printf "~a => ~a\n" key (hash-ref rcdmap key)))

    ; apply lemma 0
    (set!-values (tmp-ks tmp-us) (l0:apply-lemma rcdmap tmp-ks tmp-us))

    ; apply lemma 1
    (set!-values (tmp-ks tmp-us) (l1:apply-lemma tmp-ks tmp-us :p1cnsts :range-vec))

    ; return
    (if (= (set-count ks) (set-count tmp-ks))
        ; no updates, return
        (values tmp-ks tmp-us)
        ; has updates, call again
        (dpvl-propagate tmp-ks tmp-us)
    )
)

; perform one iteration of pp algorithm
;   - ks: known set
;   - us: unknown set
; returns:
;   - ('safe ks us info)
;   - ('unsafe ks us info)
;   - ('unknown ks us info)
(define (dpvl-iterate ks us)

    ; first, propagate
    (define-values (new-ks new-us) (if :arg-prop
        ; do propagation
        (dpvl-propagate ks us)
        ; don't do propagation
        (values ks us)
    ))
    (cond
        [(set-empty? (set-intersect :target-set new-us))
            ; no target signal is unknown, no need to solve any more, return
            (values 'safe new-ks new-us null)
        ]
        [else
            ; still there's unknown target signal, continue
            ; then select and solve
            (define-values (s0 xnew-ks xnew-us info) (dpvl-select-and-solve new-ks new-us new-us))
            (cond
                ; normal means there's no counter-example
                [(equal? 'normal s0)
                    (cond
                        [(set-empty? (set-intersect :target-set xnew-us))
                            ; no target signal is unknown, return
                            (values 'safe xnew-ks xnew-us null)
                        ]
                        [(equal? xnew-us new-us)
                            ; can't reduce any unknown any more, return
                            (values 'unknown xnew-ks xnew-us info)
                        ]
                        [else
                            ; continue the iteration
                            (dpvl-iterate xnew-ks xnew-us)
                        ]
                    )
                ]
                ; 'break means there's counter-example
                [(equal? 'break s0) (values 'unsafe xnew-ks xnew-us info)]
                [else (tokamak:error "unsupported s0 value, got: ~a." s0)]
            )
        ]
    )
)

; verifies signals in target-set
; returns (same as dpvl-iterate):
;   - (values 'safe ks us info)
;   - (values 'unsafe ks us info)
;   - (values 'unknown ks us info)
(define (apply-algorithm
    r0 nwires mconstraints
    input-set output-set target-set
    xlist opts defs cnsts
    alt-xlist alt-defs alt-cnsts
    unique-set precondition
    arg-selector arg-prop arg-timeout arg-smt
    solve state-smt-path interpret-r1cs
    parse-r1cs optimize-r1cs-p0 expand-r1cs normalize-r1cs optimize-r1cs-p1
    )

    ; first load in all global variables
    (set! :r0 r0)
    (set! :nwires nwires)
    (set! :mconstraints mconstraints)
    (set! :input-set input-set)
    (set! :output-set output-set)
    (set! :target-set target-set)

    (set! :xlist xlist)
    (set! :opts opts)
    (set! :defs defs)
    (set! :cnsts cnsts)

    (set! :alt-xlist alt-xlist)
    (set! :alt-defs alt-defs)
    (set! :alt-cnsts alt-cnsts)

    (set! :arg-selector arg-selector)
    (set! :arg-prop arg-prop)
    (set! :arg-timeout arg-timeout)
    (set! :arg-smt arg-smt)

    (set! :unique-set unique-set)
    (set! :precondition precondition)

    (set! :solve solve)
    (set! :state-smt-path state-smt-path)
    (set! :interpret-r1cs interpret-r1cs)

    (set! :parse-r1cs parse-r1cs)
    (set! :optimize-r1cs-p0 optimize-r1cs-p0)
    (set! :expand-r1cs expand-r1cs)
    (set! :normalize-r1cs normalize-r1cs)
    (set! :optimize-r1cs-p1 optimize-r1cs-p1)


    ; keep track of index of xlist (not alt-xlist since that's incomplete)
    (define known-set (list->set (filter
        (lambda (x) (not (null? x)))
        (for/list ([i (range :nwires)])
            (if (utils:contains? :alt-xlist (list-ref :xlist i))
                i
                null
            )
        )
    )))
    (define unknown-set (list->set (filter
        (lambda (x) (not (null? x)))
        (for/list ([i (range :nwires)])
            (if (utils:contains? :alt-xlist (list-ref :xlist i))
                null
                i
            )
        )
    )))
    (printf "# initial known-set ~a\n" known-set)
    (printf "# initial unknown-set ~a\n" unknown-set)
    
    ; (precondition related) incorporate unique-set if unique-set is not an empty set
    (set! known-set (set-union known-set unique-set))
    (set! unknown-set (set-subtract unknown-set unique-set))
    (printf "# refined known-set: ~a\n" known-set)
    (printf "# refined unknown-set: ~a\n" unknown-set)

    ; ==== branch out: skip optimization phase 0 and apply expand & normalize ====
    ; computing rcdmap need no ab0 lemma from optimization phase 0
    (set! :sdmcnsts (:normalize-r1cs (:expand-r1cs :cnsts)))

    ; ==== first apply optimization phase 0 ====
    (set! :p0cnsts (:optimize-r1cs-p0 :cnsts))
    (set! :alt-p0cnsts (:optimize-r1cs-p0 :alt-cnsts))

    ; ==== then expand the constraints ====
    (set! :expcnsts (:expand-r1cs :p0cnsts))
    (set! :alt-expcnsts (:expand-r1cs :alt-p0cnsts))

    ; ==== then normalize the constraints ====
    (set! :nrmcnsts (:normalize-r1cs :expcnsts))
    (set! :alt-nrmcnsts (:normalize-r1cs :alt-expcnsts))

    ; initialize selector
    (set! apply-selector (selector:apply-selector arg-selector))
    (set! selector-feedback (selector:selector-feedback arg-selector))
    (set! selector-init (selector:selector-init arg-selector))
    (selector-init :nwires)

    ; ==== then apply optimization phase 1 ====
    (set! :p1cnsts (:optimize-r1cs-p1 :nrmcnsts #t)) ; include p defs
    (set! :alt-p1cnsts (:optimize-r1cs-p1 :alt-nrmcnsts #f)) ; no p defs since this is alt-

    ; prepare partial cmds for better reuse through out the algorithm
    (set! :partial-cmds (r1cs:rcmds-append
        (r1cs:rcmds (list
            (r1cs:rcmt "================================")
            (r1cs:rcmt "======== original block ========")
            (r1cs:rcmt "================================")
        ))
        :defs
        :p1cnsts
        (r1cs:rcmds (list
            (r1cs:rcmt "===================================")
            (r1cs:rcmt "======== alternative block ========")
            (r1cs:rcmt "===================================")
        ))
        :alt-defs
        :alt-p1cnsts
        (r1cs:rcmds (list
            (r1cs:rcmt "====================================")
            (r1cs:rcmt "======== precondition block ========")
            (r1cs:rcmt "====================================")
        ))
        (if (null? :precondition)
            ; no precondition
            (r1cs:rcmds (list (r1cs:rcmt "(no precondition or skipped by user)")))
            ; assemble precondition
            (r1cs:rcmds (flatten (for/list ([v :precondition])
                (cons
                    (r1cs:rcmt (format "precondition tag: ~a" (car v)))
                    (cdr v)
                )
            )))
        )
    ))

    ; initialize range set to all values
    (set! :range-vec (build-vector :nwires (lambda (x) 'bottom)))
    ; x0 is always 1
    (vector-set! :range-vec 0 (list->set (list 1)))

    ; invoke the algorithm iteration
    (define-values (ret0 rks rus info) (dpvl-iterate known-set unknown-set))

    ; return
    (values ret0 rks rus info)
)