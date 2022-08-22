#lang rosette
; this contains a list of simple and basic optimization steps
;   - add p related definition and replace p
;   - remove *1 in mul
;   - remove +0 in add
;   - remove -0 in sub
;   - rewrite *x as x
;   - rewrite -x as -x
;   - rewrite +x as x
;   - replace x0 with 1
;   - rewrite 0 = -x mod p to 0 = x mod p (also -x = 0)
;   - partial evaluation: compute concrete results, e.g., 0*0 => 0
;     - (fixme) current only modify 0*...*x to 0
(require
    (prefix-in tokamak: "../tokamak.rkt")
    (prefix-in utils: "../utils.rkt")
    (prefix-in config: "../config.rkt")
    (prefix-in r1cs: "../r1cs-grammar.rkt")
)
(provide (rename-out
    [optimize-r1cs optimize-r1cs]
))

(define (is-rint-zero x)
    (if (r1cs:rint? x)
        (if (= 0 (r1cs:rint-v x))
            #t
            #f
        )
        #f
    )
)

(define (is-rint-one x)
    (if (r1cs:rint? x)
        (if (= 1 (r1cs:rint-v x))
            #t
            #f
        )
        #f
    )
)

(define (contains-rint-zero l)
    (if (null? l)
        #f
        (let ([x (car l)])
            (if (r1cs:rint? x)
                (if (= 0 (r1cs:rint-v x))
                    #t
                    (contains-rint-zero (cdr l))
                )
                (contains-rint-zero (cdr l))
            )
        )
    )
)

(define (optimize-r1cs arg-r1cs)
    (match arg-r1cs

        ; command level
        [(r1cs:rcmds (list (r1cs:rlogic v0) vs ...))
            (r1cs:rcmds
                (append
                    (list (r1cs:rlogic v0))
                    ; add p definition
                    (list
                        (r1cs:rdef (r1cs:rvar "p") (r1cs:rtype "Int"))
                        (r1cs:rassert (r1cs:req (r1cs:rvar "p") (r1cs:rint config:p)))
                    )
                    (for/list ([v vs]) (optimize-r1cs v))
                )
            )
        ]
        [(r1cs:rcmds vs) (r1cs:rcmds
            (append
                (list
                    (r1cs:rdef (r1cs:rvar "p") (r1cs:rtype "Int"))
                    (r1cs:rassert (r1cs:req (r1cs:rvar "p") (r1cs:rint config:p)))
                )
                (for/list ([v vs]) (optimize-r1cs v))
            )
        )]

        [(r1cs:rraw v) (r1cs:rraw v)]
        [(r1cs:rlogic v) (r1cs:rlogic (optimize-r1cs v))]
        ; (note) don't optimize declaration line
        [(r1cs:rdef v t) (r1cs:rdef v (optimize-r1cs t))]
        [(r1cs:rassert v) (r1cs:rassert (optimize-r1cs v))]
        [(r1cs:rcmt v) (r1cs:rcmt (optimize-r1cs v))]
        [(r1cs:rsolve ) (r1cs:rsolve )]

        ; sub-command level
        [(r1cs:req lhs rhs)
            ; post order
            (define new-lhs (optimize-r1cs lhs))
            (define new-rhs (optimize-r1cs rhs))
            (cond
                [(&& (is-rint-zero new-lhs) (r1cs:rmod? new-rhs))
                    (if (r1cs:rneg? (r1cs:rmod-v new-rhs))
                        ; remove neg
                        (r1cs:req new-lhs (r1cs:rmod (r1cs:rneg-v (r1cs:rmod-v new-rhs)) (r1cs:rmod-mod new-rhs)))
                        ; else do nothing
                        (r1cs:req new-lhs new-rhs)
                    )
                ]
                [(&& (is-rint-zero new-rhs) (r1cs:rmod? new-lhs))
                    (if (r1cs:rneg? (r1cs:rmod-v new-lhs))
                        ; remove neg
                        (r1cs:req (r1cs:rmod (r1cs:rneg-v (r1cs:rmod-v new-lhs)) (r1cs:rmod-mod new-lhs)) new-rhs)
                        ; else do nothing
                        (r1cs:req new-lhs new-rhs)
                    )
                ]
                [else (r1cs:req new-lhs new-rhs)]
            )
        ]
        [(r1cs:rneq lhs rhs) (r1cs:rneq (optimize-r1cs lhs) (optimize-r1cs rhs))]
        [(r1cs:rleq lhs rhs) (r1cs:rleq (optimize-r1cs lhs) (optimize-r1cs rhs))]
        [(r1cs:rlt lhs rhs) (r1cs:rlt (optimize-r1cs lhs) (optimize-r1cs rhs))]
        [(r1cs:rgeq lhs rhs) (r1cs:rgeq (optimize-r1cs lhs) (optimize-r1cs rhs))]
        [(r1cs:rgt lhs rhs) (r1cs:rgt (optimize-r1cs lhs) (optimize-r1cs rhs))]

        [(r1cs:rand vs)
            (define new-vs (for/list ([v vs]) (optimize-r1cs v)))
            ; if there's only one element, extract content directly
            (if (= 1 (length new-vs))
                (car new-vs)
                (r1cs:rand (for/list ([v new-vs]) v))
            )
        ]
        [(r1cs:ror vs)
            (define new-vs (for/list ([v vs]) (optimize-r1cs v)))
            ; if there's only one element, extract content directly
            (if (= 1 (length new-vs))
                (car new-vs)
                (r1cs:ror (for/list ([v vs]) v))
            )
        ]

        [(r1cs:rint v)
            (cond
                ; replace as p
                [(= config:p v) (r1cs:rvar "p")]
                [(= (- config:p 1) v) (r1cs:rsub (list (r1cs:rvar "p") (r1cs:rint 1)))]
                [(= (- config:p 2) v) (r1cs:rsub (list (r1cs:rvar "p") (r1cs:rint 2)))]
                [(= (- config:p 3) v) (r1cs:rsub (list (r1cs:rvar "p") (r1cs:rint 3)))]
                [(= (- config:p 4) v) (r1cs:rsub (list (r1cs:rvar "p") (r1cs:rint 4)))]
                [(= (- config:p 5) v) (r1cs:rsub (list (r1cs:rvar "p") (r1cs:rint 5)))]
                ; do nothing
                [else (r1cs:rint v)]
            )
        ]
        [(r1cs:rstr v) (r1cs:rstr v)]
        ; (note) we assume "x0" is the first wire with prefix "x"
        [(r1cs:rvar v)
            (cond
                [(equal? "x0" v) (r1cs:rint 1)]
                [else (r1cs:rvar v)]
            )
        ]
        [(r1cs:rtype v) (r1cs:rtype v)]

        [(r1cs:radd vs)
            ; remove 0
            (define new-vs (filter
                (lambda (x) (! (is-rint-zero x)))
                (for/list ([v vs]) (optimize-r1cs v))
            ))
            ; (printf "radd new-vs is: ~a\n" new-vs)
            (cond
                ; no element, all values are 0 and filtered out, return base 0
                [(= 0 (length new-vs)) (r1cs:rint 0)]
                ; if there's only one element, rewrite to neg
                [(= 1 (length new-vs)) (car new-vs)]
                ; do nothing
                [else (r1cs:radd new-vs)]
            )
        ]
        ; (fixme) this could have rewrite issues
        [(r1cs:rsub vs)
            ; remove 0
            (define new-vs (filter
                (lambda (x) (! (is-rint-zero x)))
                (for/list ([v vs]) (optimize-r1cs v))
            ))
            (cond
                ; no element, all values are 0 and filtered out, return base 0
                [(= 0 (length new-vs)) (r1cs:rint 0)]
                ; if there's only one element, rewrite to neg
                [(= 1 (length new-vs)) (r1cs:rneg (car new-vs))]
                ; do nothing
                [else (r1cs:rsub new-vs)]
            )
        ]
        [(r1cs:rmul vs)
            (define new-vs (filter
                (lambda (x) (! (is-rint-one x)))
                (for/list ([v vs]) (optimize-r1cs v))
            ))
            ; (printf "# rmul new-vs is: ~a\n" new-vs)
            ; (printf "# cont: ~a\n vs ~a\n" (contains-rint-zero vs) vs)
            (cond
                ; if there's zero already in multiplication, directly return 0
                [(contains-rint-zero new-vs) (r1cs:rint 0)]
                ; no element, all values are 1 and filtered out, return base 1
                [(= 0 (length new-vs)) (r1cs:rint 1)]
                ; if there's only one element, extract content directly
                [(= 1 (length new-vs)) (car new-vs)]
                ; do nothing
                [else (r1cs:rmul new-vs)]
            )
        ]
        [(r1cs:rneg v) (r1cs:rneg (optimize-r1cs v))]
        [(r1cs:rmod v mod) (r1cs:rmod (optimize-r1cs v) (optimize-r1cs mod))]

        [else (tokamak:exit "not supported: ~a" arg-r1cs)]
    )
)