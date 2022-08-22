#lang rosette
(require racket/engine)
(require json
    (prefix-in tokamak: "./picus/tokamak.rkt")
    (prefix-in utils: "./picus/utils.rkt")
    (prefix-in cvc5: "./picus/cvc5-utils.rkt")
    (prefix-in config: "./picus/config.rkt")
    (prefix-in r1cs: "./picus/r1cs-grammar.rkt")
    (prefix-in rint: "./picus/r1cs-cvc5-interpreter.rkt")
    (prefix-in parser: "./picus/r1cs-parser.rkt")
    ; (prefix-in osimp: "./picus/optimizers/r1cs-z3-simple-optimizer.rkt")
    ; (prefix-in oab0: "./picus/optimizers/r1cs-z3-AB0-optimizer.rkt")
)

; stateful variable
(define state-smt-path null)
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

; load r1cs binary
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

; assemble solve query
(printf "# assembling query...\n")
(define tmp0 (r1cs:rassert (r1cs:ror
    (filter (lambda (x) (! (null? x))) (for/list ([i (range nwires)])
        (if (utils:contains? output-list i)
            (r1cs:rneq (r1cs:rvar (list-ref xlist i)) (r1cs:rvar (list-ref xlist0 i)))
            null
        )
    ))
)))
(define query-cmds (r1cs:rcmds (list tmp0)))
; =======================================

(printf "# assembling final smt...\n")
(define final-cmds (r1cs:append-rcmds
    (r1cs:rcmds (list
        (r1cs:rraw "(set-info :smt-lib-version 2.6)")
        (r1cs:rraw "(set-info :category \"crafted\")")
        (r1cs:rraw "(set-logic QF_FF)")
        (r1cs:rraw "(define-sort F () (_ FiniteField 21888242871839275222246405745257275088548364400416034343698204186575808495617))")
    ))
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
    alternative-cmds
    (r1cs:rcmds (list
        (r1cs:rcmt (r1cs:rstr "============================="))
        (r1cs:rcmt (r1cs:rstr "======== query block ========"))
        (r1cs:rcmt (r1cs:rstr "============================="))
    ))
    query-cmds
    (r1cs:rcmds (list (r1cs:rsolve )))
))
; perform optimization
(define optimized-cmds
    final-cmds
    ; (osimp:optimize-r1cs final-cmds)
    ; (oab0:optimize-r1cs (osimp:optimize-r1cs final-cmds))
)
(define final-str (string-join (rint:interpret-r1cs optimized-cmds) "\n"))
; (note) replace Int with F for cvc5 only
(set! final-str (string-replace final-str " Int" " F"))
(set! final-str (regexp-replace* #rx"(; ======== range constraints ========.*?); ======== r1cs constraints ========" final-str "; ======== r1cs constraints ========"))
(printf "# final str is:\n~a\n" final-str)
; solve!
(define res (cvc5:solve final-str arg-timeout #:output-smt? arg-smt))
(if (equal? 'unsat (car res))
    (printf "# verified.\n")
    (printf "# failed / reason: ~a\n" res)
)