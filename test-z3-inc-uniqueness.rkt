#lang rosette
(require racket/engine)
(require json rosette/solver/smt/z3
    (prefix-in tokamak: "./picus/tokamak.rkt")
    (prefix-in utils: "./picus/utils.rkt")
    (prefix-in z3: "./picus/z3-utils.rkt")
    (prefix-in config: "./picus/config.rkt")
    (prefix-in r1cs: "./picus/r1cs-grammar.rkt")
    (prefix-in rint: "./picus/r1cs-z3-interpreter.rkt")
    (prefix-in parser: "./picus/r1cs-parser.rkt")
    (prefix-in osimp: "./picus/optimizers/r1cs-z3-simple-optimizer.rkt")
    (prefix-in oab0: "./picus/optimizers/r1cs-z3-AB0-optimizer.rkt")
)

; parse command line arguments
(define arg-r1cs null)
(define arg-timeout 5000)
(define arg-smt #f)
(command-line
    #:once-each
    [("--r1cs") p-r1cs "path to target r1cs"
        (begin
            (set! arg-r1cs p-r1cs)
            (when (! (string-suffix? arg-r1cs ".r1cs"))
                (printf "# error: file need to be *.r1cs\n")
                (exit 0)
            )
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

(define r0 (r1cs:read-r1cs arg-r1cs))
(define nwires (r1cs:get-nwires r0))
(printf "# number of wires: ~a\n" nwires)
(printf "# number of constraints: ~a\n" (r1cs:get-mconstraints r0))
(printf "# field size (how many bytes): ~a\n" (r1cs:get-field-size r0))

; parse original r1cs
(printf "# parsing original r1cs...\n")
(define-values (xlist original-cmds) (parser:parse-r1cs r0 null)) ; interpret the constraint system
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
(define-values (_ alternative-cmds) (parser:parse-r1cs r0 xlist0))

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
            (r1cs:rcmds (list (r1cs:rlogic (r1cs:rstr "QF_NIA"))))
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
        (define optimized-cmds
            ; final-cmds
            ; (osimp:optimize-r1cs final-cmds)
            (oab0:optimize-r1cs (osimp:optimize-r1cs final-cmds))
        )
        (define final-str (string-join (rint:interpret-r1cs optimized-cmds) "\n"))
        (define res (z3:solve final-str arg-timeout #:output-smt? #f))
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
            (printf "    # smt path: ~a\n" z3:state-smt-path))
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
