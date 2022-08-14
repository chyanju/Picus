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
(define-values (xlist original-definitions original-constraints signal2constraints constraint2signals) (rint:interpret-r1cs r0 null)) ; interpret the constraint system
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
(define xlist0 (for/list ([i (range nwires)])
    (if (not (utils:contains? input-list i))
        (format "y~a" i)
        (list-ref xlist i)
    )
))
(printf "# xlist0: ~a.\n" xlist0)
; then interpret again
(printf "# interpreting alternative r1cs...\n")
(define-values (_1 alternative-definitions alternative-constraints _2 _3) (rint:interpret-r1cs r0 xlist0))

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

(define unknown-list (if (null? arg-order)
    (filter (lambda (x) (! (null? x)))
        (for/list ([i (range nwires)])
            (if (utils:contains? xlist0 (list-ref xlist i))
                null
                i
            )
        )
    )
    (call-with-input-file arg-order read-json)
))

;(define unknown-list (file->list arg-order))	

;(define unknown-list (filter
;    (lambda (x) (! (null? x)))
;    (for/list ([i (range nwires)])
;        (if (utils:contains? xlist0 (list-ref xlist i))
;            null
;            i
;        )
;    )
;))
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

(define partial-original-definitions-level-0
    (for/list ([s nwires])
        (define list_index (list-ref signal2signals s))
        (for/list ([index list_index])
            (list-ref original-definitions index)
        )
    )
)

(define partial-alternative-definitions-level-0
    (for/list ([s nwires])
        (define list_index (list-ref signal2signals s))
        (for/list ([index list_index])
            (list-ref alternative-definitions index)
        )
    )
)

(define partial-original-constraints-level-0
    (for/list ([s nwires])
        (define list_index (list-ref signal2constraints s))
        (for/list ([index list_index])
            (list-ref original-constraints index)
        )
    )
)

(define partial-alternative-constraints-level-0
    (for/list ([s nwires])
        (define list_index (list-ref signal2constraints s))
        (for/list ([index list_index])
            (list-ref alternative-constraints index)
        )
    )
)

(define partial-original-definitions-level-1
    (for/list ([s nwires])
        (define list_index (list-ref signal2neighborsignals s))
        (for/list ([index list_index])
            (list-ref original-definitions index)
        )
    )
)

(define partial-alternative-definitions-level-1
    (for/list ([s nwires])
        (define list_index (list-ref signal2neighborsignals s))
        (for/list ([index list_index])
            (list-ref alternative-definitions index)
        )
    )
)

(define partial-original-constraints-level-1
    (for/list ([s nwires])
        (define list_index (list-ref signal2neighborconstraints s))
        (for/list ([index list_index])
            (list-ref original-constraints index)
        )
    )
)

(define partial-alternative-constraints-level-1
    (for/list ([s nwires])
        (define list_index (list-ref signal2neighborconstraints s))
        (for/list ([index list_index])
            (list-ref alternative-constraints index)
        )
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
    
    (define  partial-original-definitions 
        (if (= arg-level 0)
             partial-original-definitions-level-0
             partial-original-definitions-level-1
        )
    )
    
    (define  partial-alternative-definitions 
        (if (= arg-level 0)
             partial-alternative-definitions-level-0
             partial-alternative-definitions-level-1
        )
    )
    
    (define  partial-original-constraints 
        (if (= arg-level 0)
             partial-original-constraints-level-0
             partial-original-constraints-level-1
        )
    )
    
    (define  partial-alternative-constraints 
        (if (= arg-level 0)
             partial-alternative-constraints-level-0
             partial-alternative-constraints-level-1
        )
    )
    
    
    (for ([i ul])
        (define to_study (if (= 0 arg-level) 
             (not (utils:empty_inter? changed-0 (list-ref signal2signals i)))
             (not (utils:empty_inter? changed-1 (list-ref signal2neighborsignals i)))
        ))
        (printf "Studying ~a :~a." (list-ref xlist i) to_study)
        (printf "  # checking: (~a ~a), " (list-ref xlist i) (list-ref xlist0 i))
        
        (define known-raw (for/list ([j tmp-kl])
            (if (utils:contains? (if (= arg-level 0) (list-ref signal2signals i) (list-ref signal2neighborsignals i)) j) (format "(assert (= ~a ~a))" (list-ref xlist j) (list-ref xlist0 j)) (format "; not adding known"))
        ))
        
        (define final-raw (append
            (list "; =================================== ;")
            (list "; ======== original definitions ======== ;")
            (list "; =================================== ;") 
            (list "")
            (list-ref partial-original-definitions i)
            (list "")
            (list "; =================================== ;")
            (list "; ======== alternative definitions ======== ;")
            (list "; =================================== ;") 
            (list "")
            (list-ref partial-alternative-definitions i)
            (list "")
            (list "; =================================== ;")
            (list "; ======== original constraints ======== ;")
            (list "; =================================== ;") 
            (list "")
            (list-ref partial-original-constraints i)
            (list "")
            (list "; =================================== ;")
            (list "; ======== alternative constraints ======== ;")
            (list "; =================================== ;") 
            (list "")
            (list-ref partial-alternative-constraints i)
            (list "")
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
        (if (= arg-level 1)
           tmp-ul
           (inc-solve (reverse tmp-kl) (reverse tmp-ul) 1 new-changed-0 new-changed-1)
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
