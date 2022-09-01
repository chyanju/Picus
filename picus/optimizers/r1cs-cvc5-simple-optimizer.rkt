#lang rosette
; this contains a list of simple and basic optimization steps
;   - add p related definition and replace p
;   - remove *1 in mul
;   - remove +0 in add
;   - rewrite *x as x
;   - rewrite -x as -x
;   - rewrite +x as x
;   - replace x0 with 1
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
        ; probably the original block
        [(r1cs:rcmds (list (r1cs:rlogic v0) vs ...))
            (r1cs:rcmds
                (append
                    (list
                        (r1cs:rlogic v0)
                        (r1cs:rraw "(set-info :smt-lib-version 2.6)")
                        (r1cs:rraw "(set-info :category \"crafted\")")
                        (r1cs:rraw "(define-sort F () (_ FiniteField 21888242871839275222246405745257275088548364400416034343698204186575808495617))")
                        ; add p definition
                        (r1cs:rdef (r1cs:rvar "p") (r1cs:rtype "F"))
                        (r1cs:rassert (r1cs:req (r1cs:rvar "p") (r1cs:rint config:p)))
                        (r1cs:rdef (r1cs:rvar "ps1") (r1cs:rtype "F"))
                        (r1cs:rassert (r1cs:req (r1cs:rvar "ps1") (r1cs:rint (- config:p 1))))
                        (r1cs:rdef (r1cs:rvar "ps2") (r1cs:rtype "F"))
                        (r1cs:rassert (r1cs:req (r1cs:rvar "ps2") (r1cs:rint (- config:p 2))))
                        (r1cs:rdef (r1cs:rvar "ps3") (r1cs:rtype "F"))
                        (r1cs:rassert (r1cs:req (r1cs:rvar "ps3") (r1cs:rint (- config:p 3))))
                        (r1cs:rdef (r1cs:rvar "ps4") (r1cs:rtype "F"))
                        (r1cs:rassert (r1cs:req (r1cs:rvar "ps4") (r1cs:rint (- config:p 4))))
                        (r1cs:rdef (r1cs:rvar "ps5") (r1cs:rtype "F"))
                        (r1cs:rassert (r1cs:req (r1cs:rvar "ps5") (r1cs:rint (- config:p 5))))
                        ; add 0 definition
                        (r1cs:rdef (r1cs:rvar "zero") (r1cs:rtype "F"))
                        (r1cs:rassert (r1cs:req (r1cs:rvar "zero") (r1cs:rint 0)))
                        ; add 1 definition
                        (r1cs:rdef (r1cs:rvar "one") (r1cs:rtype "F"))
                        (r1cs:rassert (r1cs:req (r1cs:rvar "one") (r1cs:rint 1)))
                    )
                    (for/list ([v vs]) (optimize-r1cs v))
                )
            )
        ]
        ; probably the alternative block, no need to define F again
        [(r1cs:rcmds vs) (r1cs:rcmds
            (append
                (list
                    ; add p definition
                    (r1cs:rdef (r1cs:rvar "p") (r1cs:rtype "F"))
                    (r1cs:rassert (r1cs:req (r1cs:rvar "p") (r1cs:rint config:p)))
                    (r1cs:rdef (r1cs:rvar "ps1") (r1cs:rtype "F"))
                    (r1cs:rassert (r1cs:req (r1cs:rvar "ps1") (r1cs:rint (- config:p 1))))
                    (r1cs:rdef (r1cs:rvar "ps2") (r1cs:rtype "F"))
                    (r1cs:rassert (r1cs:req (r1cs:rvar "ps2") (r1cs:rint (- config:p 2))))
                    (r1cs:rdef (r1cs:rvar "ps3") (r1cs:rtype "F"))
                    (r1cs:rassert (r1cs:req (r1cs:rvar "ps3") (r1cs:rint (- config:p 3))))
                    (r1cs:rdef (r1cs:rvar "ps4") (r1cs:rtype "F"))
                    (r1cs:rassert (r1cs:req (r1cs:rvar "ps4") (r1cs:rint (- config:p 4))))
                    (r1cs:rdef (r1cs:rvar "ps5") (r1cs:rtype "F"))
                    (r1cs:rassert (r1cs:req (r1cs:rvar "ps5") (r1cs:rint (- config:p 5))))
                    ; add 0 definition
                    (r1cs:rdef (r1cs:rvar "zero") (r1cs:rtype "F"))
                    (r1cs:rassert (r1cs:req (r1cs:rvar "zero") (r1cs:rint 0)))
                    ; add 1 definition
                    (r1cs:rdef (r1cs:rvar "one") (r1cs:rtype "F"))
                    (r1cs:rassert (r1cs:req (r1cs:rvar "one") (r1cs:rint 0)))
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
        [(r1cs:req lhs rhs) (r1cs:req (optimize-r1cs lhs) (optimize-r1cs rhs))]
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
        [(r1cs:rimp lhs rhs) (r1cs:rimp (optimize-r1cs lhs) (optimize-r1cs rhs))]


        [(r1cs:rint v)
            (cond
                ; replace as p
                [(= config:p v) (r1cs:rint 0)]
                ;[(= (- config:p 1) v) (r1cs:rvar "ps1")]
                ;[(= (- config:p 2) v) (r1cs:rvar "ps2")]
                ;[(= (- config:p 3) v) (r1cs:rvar "ps3")]
                ;[(= (- config:p 4) v) (r1cs:rvar "ps4")]
                ;[(= (- config:p 5) v) (r1cs:rvar "ps5")]
                ; replace as zero
                ;[(= 0 v) (r1cs:rvar "zero")]
                ; replace as one
                ;[(= 1 v) (r1cs:rvar "one")]
                ; do nothing
                [else (r1cs:rint v)]
            )
        ]
        [(r1cs:rstr v) (r1cs:rstr v)]
        ; (note) we assume "x0" is the first wire with prefix "x"
        [(r1cs:rvar v)
            (cond
                [(equal? "x0" v) (optimize-r1cs (r1cs:rint 1))]
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
        [(r1cs:rsub vs) (tokamak:exit "cvc5 doesn't support sub")]
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
        [(r1cs:rmod v mod) (tokamak:exit "cvc5 doesn't support mod")]

        [else (tokamak:exit "not supported: ~a" arg-r1cs)]
    )
)