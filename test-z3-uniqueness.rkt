#lang rosette
(require racket/engine)
(require json rosette/solver/smt/z3
    (prefix-in tokamak: "./picus/tokamak.rkt")
    (prefix-in utils: "./picus/utils.rkt")
    (prefix-in config: "./picus/config.rkt")
    (prefix-in r1cs: "./picus/r1cs.rkt")
    (prefix-in rint: "./picus/r1cs-z3-interpreter.rkt")
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
    (when verbose?
        (printf "# written to: ~a\n" temp-path)
    )

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

; parse command line arguments
(define arg-r1cs null)
(command-line
    #:once-each
    [("--r1cs") p-r1cs "path to target r1cs"
        (begin
            (set! arg-r1cs p-r1cs)
            (printf "# r1cs file: ~a\n" arg-r1cs)
            (when (! (string-suffix? arg-r1cs ".r1cs"))
                (printf "# error: file need to be *.r1cs\n")
                (exit 0)
            )
        )
    ]
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
; (printf "# original-raw ~a\n" original-raw)

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
; existence of different valuation of outputs
(define tmp-diff (for/list ([i (range (+ 1 nwires))])
    (if (utils:contains? output-list i) (format "(not (= ~a ~a))" (list-ref xlist i) (list-ref xlist0 i)) null)))
(define diff-list (filter (lambda (x) (! (null? x))) tmp-diff))
(define diff-raw (list
    (string-join diff-list "\n  " #:before-first "(assert (or \n  " #:after-last "))\n")
))
; (printf "# diff-raw is:\n~a\n" diff-raw)
; =======================================

(define final-raw (append (list "(set-logic QF_NIA)\n") original-raw (list "") alternative-raw (list "") diff-raw (list "(check-sat)\n(get-model)")))
(define final-str (string-join final-raw "\n"))

; solve!
(define res (do-solve final-str 10000))
(if (equal? 'unsat (car res))
    (printf "# verified.\n")
    (printf "# failed / reason: ~a\n" res)
)