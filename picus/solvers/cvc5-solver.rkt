#lang racket
(require racket/engine)
(provide (all-defined-out))

; stateful variable that stores smt path
(define state-smt-path null)

; solving component
(define (solve smt-str timeout #:verbose? [verbose? #f] #:output-smt? [output-smt? #f])
    (define temp-folder (find-system-path 'temp-dir))
    (define temp-file (format "picus~a.smt2"
        (string-replace (format "~a" (current-inexact-milliseconds)) "." "")))
    (define temp-path (build-path temp-folder temp-file))
    (set! state-smt-path temp-path)
    (define smt-file (open-output-file temp-path))
    (display smt-str smt-file)
    (close-output-port smt-file)
    (when (or verbose? output-smt?)
        (printf "(written to: ~a)\n" temp-path)
    )

    (when verbose?
        (printf "# solving...\n")
    )
    (define-values (sp out in err)
            ; (note) use `apply` to expand the last argument
            (apply subprocess #f #f #f (find-executable-path "cvc5") (list temp-path))
            ; (apply subprocess #f #f #f (find-executable-path "cvc5") (list temp-path "--produce-models"))
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
        [(not eres)
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