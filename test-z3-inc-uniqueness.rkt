#lang rosette
(require racket/engine)
(require json rosette/solver/smt/z3
    (prefix-in tokamak: "./picus/tokamak.rkt")
    (prefix-in utils: "./picus/utils.rkt")
    (prefix-in config: "./picus/config.rkt")
    (prefix-in r1cs: "./picus/r1cs.rkt")
    (prefix-in rint: "./picus/r1cs-z3-interpreter.rkt")
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

(define (optimization-p smt-str)
    (string-append
        (format "(declare-const p Int)\n(assert (= p ~a))\n\n" config:p)
        (string-replace
            (string-replace smt-str (format "~a" config:p) "p")
            (format "~a" (- config:p 1))
            "(- p 1)"
        )
    )
)

; solving component
(define (do-solve smt-str timeout #:verbose? [verbose? #f])
    (define temp-folder (find-system-path 'temp-dir))
    (define temp-file (format "picus~a.smt"
        (string-replace (format "~a" (current-inexact-milliseconds)) "." "")))
    (define temp-path (build-path temp-folder temp-file))
    (define smt-file (open-output-file temp-path))
    (display smt-str smt-file)
    (close-output-port smt-file)
    (set! state-smt-path temp-path) ; update global smt path
    (when verbose?
        (printf "# written to: ~a\n" temp-path)
    )
<<<<<<< HEAD
    (printf "# written to: ~a\n" temp-path)
=======
>>>>>>> 89d898ebc681d7d93c59bfad4218817c8b89fa10
    (when verbose?
        (printf "# solving...\n")
    )
    (define-values (sp out in err)
            ; (note) use `apply` to expand the last argument
            (apply subprocess #f #f #f (find-executable-path "z3") (list temp-path))
    )
    (define engine0 (engine (lambda (_)
        (define out-str (port->string out))
        (define err-str (port->string err))
        (close-input-port out)
        (close-output-port in)
        (close-input-port err)
        (subprocess-wait sp)
        (cons out-str err-str)
    )))
    (define eres (engine-run timeout engine0))
    (define esol (engine-result engine0))
    (cond
        [(! eres)
            ; need to kill the process
            (subprocess-kill sp #t)
            (cons 'timeout "")
        ]
        [else
            (define out-str (car esol))
            (define err-str (cdr esol))
            (when verbose?
                (printf "# stdout:\n~a\n" out-str)
                (printf "# stderr:\n~a\n" err-str)
            )
            (cond
                [(non-empty-string? err-str) (cons 'error err-str)] ; something wrong, not solved
                [(string-prefix? out-str "unsat") (cons 'unsat out-str)]
                [(string-prefix? out-str "sat") (cons 'sat out-str)]
                [(string-prefix? out-str "unknown") (cons 'unknown out-str)]
                [else (cons 'else out-str)]
            )
        ]
    )
)

(define r0 (r1cs:read-r1cs arg-r1cs))
(define nwires (r1cs:get-nwires r0))
(printf "# number of wires: ~a (+1)\n" nwires)
(printf "# number of constraints: ~a\n" (r1cs:get-mconstraints r0))
(printf "# field size (how many bytes): ~a\n" (r1cs:get-field-size r0))

(printf "# interpreting original r1cs...\n")
(define-values (xlist original-raw) (rint:interpret-r1cs r0 null)) ; interpret the constraint system
(define input-list (r1cs:r1cs-inputs r0))
(define output-list (r1cs:r1cs-outputs r0))
(printf "# inputs: ~a.\n" input-list)
(printf "# outputs: ~a.\n" output-list)
(printf "# xlist: ~a.\n" xlist)

; fix inputs, create alternative outputs
; (note) need nwires+1 to account for 1st input
; =======================================
; output verification (weak verification)
; clara fixed version
;   |- create alternative variables for all non-input variables
;   |- but restrict output variables as weak verification states
(define xlist0 (for/list ([i (range (+ 1 nwires))])
    (if (not (utils:contains? input-list i))
        (format "y~a" i)
        (list-ref xlist i)
    )
))
(printf "# xlist0: ~a.\n" xlist0)
; then interpret again
(printf "# interpreting alternative r1cs...\n")
(define-values (_ alternative-raw) (rint:interpret-r1cs r0 xlist0))

(define partial-raw (append
    (list "; ================================ ;")
    (list "; ======== original block ======== ;")
    (list "; ================================ ;")
    (list "")
    original-raw
    (list "; =================================== ;")
    (list "; ======== alternative block ======== ;")
    (list "; =================================== ;")
    (list "")
    alternative-raw))

; keep track of index of xlist (not xlist0 since that's incomplete)
(define known-list (filter
    (lambda (x) (! (null? x)))
    (for/list ([i (range (+ 1 nwires))])
        (if (utils:contains? xlist0 (list-ref xlist i))
            i
            null
        )
    )
))
(define unknown-list (filter
    (lambda (x) (! (null? x)))
    (for/list ([i (range (+ 1 nwires))])
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
        (define known-raw (for/list ([j tmp-kl])
            (format "(assert (= ~a ~a))" (list-ref xlist j) (list-ref xlist0 j))
        ))
        (define final-raw (append
            partial-raw
            (list "; =================================== ;")
            (list "; ======== known constraints ======== ;")
            (list "; =================================== ;")
            (list "")
            known-raw
            (list "")
            (list "; =================================== ;")
            (list "; ======== query constraints ======== ;")
            (list "; =================================== ;")
            (list "")
            (list (format "(assert (not (= ~a ~a)))" (list-ref xlist i) (list-ref xlist0 i))) (list "")
            (list "(check-sat)\n(get-model)") (list "")
        ))
        ; (define final-str (string-join final-raw "\n"))
        (define final-str (string-append
            "(set-logic QF_NIA)\n\n"
            (optimization-p (string-join final-raw "\n"))
        ))
        (define res (do-solve final-str arg-timeout))
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
            (printf "    # smt path: ~a\n" state-smt-path))
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
