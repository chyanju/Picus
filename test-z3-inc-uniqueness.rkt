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
(define arg-order null)
(define arg-preconditions null)
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
    [("--order") p-order "path to file with order for the signals"
        (begin
            (set! arg-order p-order)
        )
    ]
    [("--prec") p-preconditions "path to file with the preconditions"
        (begin
            (set! arg-preconditions p-preconditions)
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
        (format "(declare-fun div (Int Int) Int)\n")
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
(printf "# number of wires: ~a\n" nwires)
(printf "# number of constraints: ~a\n" (r1cs:get-mconstraints r0))
(printf "# field size (how many bytes): ~a\n" (r1cs:get-field-size r0))

(printf "# interpreting original r1cs...\n")
(define-values (original-constraints signal2constraints constraint2signals) (rint:interpret-r1cs r0)) ; interpret the constraint system
(define input-list (r1cs:r1cs-inputs r0))
(define output-list (r1cs:r1cs-outputs r0))
(printf "# inputs: ~a.\n" input-list)
(printf "# outputs: ~a.\n" output-list)


; fix inputs, create alternative outputs
; =======================================
; output verification (weak verification)
; clara fixed version
;   |- create alternative variables for all non-input variables
;   |- but restrict output variables as weak verification states


; keep track of index of xlist (not xlist0 since that's incomplete)
(define known-list (filter
    (lambda (x) (! (null? x)))
    (for/list ([i nwires])
        (if (utils:contains? input-list i)
            i
            null
        )
    )
))

(define unknown-list (if (null? arg-order)
    (filter (lambda (x) (! (null? x)))
        (for/list ([i (range nwires)])
            (if (utils:contains? input-list i)
                null
                i
            )
        )
    )
    (call-with-input-file arg-order read-json)
))

(define list-preconditions (if (null? arg-preconditions)
    '()
    (file->lines arg-preconditions)
))


(printf "# initial knwon-list: ~a\n" known-list)
(printf "# initial unknown-list: ~a\n" unknown-list)

(printf "# signal2constraints: ~a.\n" signal2constraints)
(printf "# constraint2signals: ~a.\n" constraint2signals)

(define signal2neighborconstraints 
    (for/list ([i (range nwires)])
        (foldl 
           (lambda (x y) 
                (set-union y (foldl (lambda (x1 y1) (
                    set-union y1 (if (utils:contains? known-list x1) '() (list-ref signal2constraints x1))))
                    '()
                    (list-ref constraint2signals x)
                ) )
            )
            (list-ref signal2constraints i)
            (list-ref signal2constraints i)
        )
     )
) 
(define signal2neighborsignals
    (for/list ([i (range nwires)])
        (foldl 
           (lambda (x y) (set-union y (list-ref constraint2signals x)))
            '()
            (list-ref signal2neighborconstraints i)
        )
     )
) 

(define signal2signals
    (for/list ([i (range nwires)])
        (foldl 
           (lambda (x y) (set-union y (list-ref constraint2signals x)))
            '()
            (list-ref signal2constraints i)
        )
     )
) 

(printf "# signal2neighborconstraints: ~a.\n" signal2neighborconstraints)
(printf "# signal2neighborsignals: ~a.\n" signal2neighborsignals)

; strictly align with wid
(define xlist-original
    (for/list ([i nwires]) (format "x~a" i))
)

(printf "# xlist: ~a.\n" xlist-original)

; strictly align with wid
(define (xlist-alternative known)
    (for/list ([i nwires])
        (if (utils:contains? known i)
            (format "x~a" i)
            (format "y~a" i)
        )
    )
)

(define original-signal-definitions 
    (rint:write-signal-definitions nwires xlist-original #f)
)

(define (alternative-signal-definitions xlist)
    (rint:write-signal-definitions nwires xlist #t)
)

(define original-constraints-z3 
    (for/list ([cnst original-constraints])
        (rint:write-constraint cnst xlist-original)
    )
)

(define partial-original-constraints-level-0
    (for/list ([s nwires])
        (define list_index (list-ref signal2constraints s))
        (for/list ([index list_index])
            (list-ref original-constraints-z3 index)
        )
    )
)

(define (partial-alternative-constraints-level-0 s xlist-alt)
    (define list_index (list-ref signal2constraints s))
    (for/list ([index list_index])
        (rint:write-constraint (list-ref original-constraints index) xlist-alt)
    )
)


(define partial-original-constraints-level-1
    (for/list ([s nwires])
        (define list_index (list-ref signal2neighborconstraints s))
        (for/list ([index list_index])
            (list-ref original-constraints-z3 index)
        )
    )
)

(define (partial-alternative-constraints-level-1 s xlist-alt)
    (define list_index (list-ref signal2neighborconstraints s))
    (for/list ([index list_index])
        (rint:write-constraint (list-ref original-constraints index) xlist-alt)
    )
)

(define partial-original-constraints-level-2
    original-constraints-z3
)

(define (partial-alternative-constraints-level-2 xlist-alt)
    (for/list ([index (r1cs:get-mconstraints r0)])
        (rint:write-constraint (list-ref original-constraints index) xlist-alt)
    )
)



; returns final unknown list, and if it's empty, it means all are known
; and thus verified
(define (inc-solve kl ul arg-level changed-0 changed-1)
    (printf "# ==== new round inc-solve ===\n")
    (define tmp-kl (for/list ([i kl]) i))
    (define tmp-ul (list ))
    (define changed? #f)
    
    (define new-changed-0 '())
    
    (define new-changed-1 (if (= arg-level 0)
        changed-1
        '()
    ))
   
    
    (for ([i ul])
        ; strictly align with wid
       (define xlist-alt (xlist-alternative tmp-kl))

        (define alt-def (alternative-signal-definitions xlist-alt))

        (define  partial-original-constraints 
            (if (= arg-level 0)
                 partial-original-constraints-level-0
                 (if (= arg-level 1)
                   partial-original-constraints-level-1
                   partial-original-constraints-level-2
                 )
            )
        )
    
        (define  partial-alternative-constraints 
            (if (= arg-level 0)
                 (partial-alternative-constraints-level-0 i xlist-alt)
                 (if (= arg-level 1)
                     (partial-alternative-constraints-level-1 i xlist-alt)
                     (partial-alternative-constraints-level-2 xlist-alt)
                 )
            )
        )
    
        (define to_study (if (= 0 arg-level) 
             (not (utils:empty_inter? changed-0 (list-ref signal2signals i)))
             (if (= 1 arg-level)
                 (not (utils:empty_inter? changed-1 (list-ref signal2neighborsignals i)))
                 #t
             )
        ))
        (printf "Studying ~a :~a." (list-ref xlist-alt i) to_study)
        (printf "  # checking: (~a ~a), " (list-ref xlist-original i) (list-ref xlist-alt i))
       
        
        (define final-raw (append
            (list "; =================================== ;")
            (list "; ======== original definitions ======== ;")
            (list "; =================================== ;") 
            (list "")
            original-signal-definitions 
            (list "")
            (list "; =================================== ;")
            (list "; ======== alternative definitions ======== ;")
            (list "; =================================== ;") 
            (list "")
            (alternative-signal-definitions xlist-alt)
            (list "")
            (list "; =================================== ;")
            (list "; ======== original constraints ======== ;")
            (list "; =================================== ;") 
            (list "")
            (if (= 2 arg-level)
               partial-original-constraints
               (list-ref partial-original-constraints i)
            )

            (list "")
            (list "; =================================== ;")
            (list "; ======== alternative constraints ======== ;")
            (list "; =================================== ;") 
            (list "")
            partial-alternative-constraints
            (list "")
            (list "; =================================== ;")
            (list "; ======== preconditions ======== ;")
            (list "; =================================== ;")
            (list "")
            list-preconditions
            (list "")
            (list "; =================================== ;")
            (list "; ======== query constraints ======== ;")
            (list "; =================================== ;")
            (list "")
            (list (format "(assert (not (= ~a ~a)))" (list-ref xlist-original i) (list-ref xlist-alt i))) (list "")
            (list "(check-sat)\n(get-model)") (list "")
        ))
        ; (define final-str (string-join final-raw "\n"))
        (define final-str (string-append
            "(set-logic QF_UFNIA)\n\n"
            (optimization-p (string-join final-raw "\n"))
        ))
        (define res (if to_study (do-solve final-str arg-timeout) (cons #f '())))
        (cond
            [(equal? 'unsat (car res))
                (printf "verified.\n")
                (set! tmp-kl (cons i tmp-kl))
                (set! changed? #t)
                (set! new-changed-0 (cons i new-changed-0))
                (set! new-changed-1 (cons i new-changed-1))
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
        (inc-solve (reverse tmp-kl) (reverse tmp-ul) 0 new-changed-0 new-changed-1)
        (if (= arg-level 0)
           (inc-solve (reverse tmp-kl) (reverse tmp-ul) 1 new-changed-0 new-changed-1)
           (if (= arg-level 1)
               (inc-solve (reverse tmp-kl) (reverse tmp-ul) 2 new-changed-0 new-changed-1)
               tmp-ul
           )
        )
    )
)

(define res-ul (inc-solve known-list unknown-list 0 unknown-list unknown-list))
(printf "# final unknown list: ~a\n" res-ul)
(if (empty? res-ul)
    (printf "# Strong safety verified.\n")
    (printf "# Strong safey failed.\n")
)

(if (utils:empty_inter? res-ul output-list)
    (printf "# Weak safety verified.\n")
    (printf "# Weak safey failed.\n")
)
