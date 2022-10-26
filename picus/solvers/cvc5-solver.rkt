#lang rosette
(require racket/engine)
(provide (all-defined-out))

; stateful variable that stores smt path
(define state-smt-path null)

; solving component
; arguments:
;   - timeout: (in seconds)
;   - smt-strs: a list of smt strings, even for 1 thread this needs to be a list
;   - nthreads: number of threads
;   (note) actual threads will be the smaller number between nthreads and number smt strings
;   i.e., if there's only 2 strings but nthread is 4, then only 2 threads will be invoked
; returns:
;   - a list of pairs of result tag and info
(define (solve smt-strs timeout #:nthreads [nthreads 1] #:verbose? [verbose? #f] #:output-smt? [output-smt? #f])
    (define temp-folder (find-system-path 'temp-dir))
    (set! state-smt-path (list ))

    (define nt (min (length smt-strs) nthreads))
    (define spe-list (for/list ([i (range nt)])
        (define smt-str (list-ref smt-strs i)) ; fetch the smt string

        (define temp-file (format "picus~a_~a.smt2"
            (string-replace (format "~a" (current-inexact-milliseconds)) "." "") i))
        (define temp-path (build-path temp-folder temp-file))
        (set! state-smt-path (append state-smt-path (list temp-path)))
        (define smt-file (open-output-file temp-path))
        (display smt-str smt-file)
        (close-output-port smt-file)
        (when (|| verbose? output-smt?)
            (printf "(written to: ~a)\n" temp-path)
        )

        (when verbose? (printf "# solving...\n"))
        (define-values (sp out in err)
            ; (note) use `apply` to expand the last argument
            (apply subprocess #f #f #f (find-executable-path "cvc5") (list temp-path))
        )

        (close-output-port in)
        ; store the engine
        (list sp out err)
    ))

    ; fetch results
    (define res-list (for/list ([i (range nt)])

        (define sp (list-ref (list-ref spe-list i) 0))
        (define out (list-ref (list-ref spe-list i) 1))
        (define err (list-ref (list-ref spe-list i) 2))

        ; (fixme) this is wrong since each engine will give 5s separately
        ;         for those that would timeout, you are giving 5s * nt in total
        ;         which is wrong since you should only give 5s in total
        (define engine0 (engine (lambda (_)
            (define out-str (port->string out))
            (define err-str (port->string err))
            (close-input-port out)
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


    ))
    ; return
    res-list
)