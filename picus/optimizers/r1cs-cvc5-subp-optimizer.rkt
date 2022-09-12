#lang rosette
; this contains the following optimizations:
;   - add p related definition and replace p
(require
    (prefix-in tokamak: "../tokamak.rkt")
    (prefix-in utils: "../utils.rkt")
    (prefix-in config: "../config.rkt")
    (prefix-in r1cs: "../r1cs/r1cs-grammar.rkt")
)
(provide (rename-out
    [optimize-r1cs optimize-r1cs]
))

(define (optimize-r1cs arg-r1cs)
    (match arg-r1cs

        ; command level
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
        [(r1cs:rlogic v) (r1cs:rlogic v)]
        ; (note) don't optimize declaration line
        [(r1cs:rdef v t) (r1cs:rdef v (optimize-r1cs t))]
        [(r1cs:rassert v) (r1cs:rassert (optimize-r1cs v))]
        [(r1cs:rcmt v) (r1cs:rcmt v)]
        [(r1cs:rsolve ) (r1cs:rsolve )]

        ; sub-command level
        [(r1cs:req lhs rhs) (r1cs:req (optimize-r1cs lhs) (optimize-r1cs rhs))]
        [(r1cs:rneq lhs rhs) (r1cs:rneq (optimize-r1cs lhs) (optimize-r1cs rhs))]

        [(r1cs:rand vs) (r1cs:rand (for/list ([v vs]) (optimize-r1cs v)))]
        [(r1cs:ror vs) (r1cs:ror (for/list ([v vs]) (optimize-r1cs v)))]

        [(r1cs:rint v)
            (cond
                ; replace as p
                [(= config:p v) (r1cs:rint 0)]
                [(= (- config:p 1) v) (r1cs:rvar "ps1")]
                [(= (- config:p 2) v) (r1cs:rvar "ps2")]
                [(= (- config:p 3) v) (r1cs:rvar "ps3")]
                [(= (- config:p 4) v) (r1cs:rvar "ps4")]
                [(= (- config:p 5) v) (r1cs:rvar "ps5")]
                ; replace as zero
                [(= 0 v) (r1cs:rvar "zero")]
                ; replace as one
                [(= 1 v) (r1cs:rvar "one")]
                ; do nothing
                [else (r1cs:rint v)]
            )
        ]
        ; (note) we assume "x0" is the first wire with prefix "x"
        [(r1cs:rvar v) (r1cs:rvar v)]
        [(r1cs:rtype v) (r1cs:rtype v)]

        [(r1cs:radd vs) (r1cs:radd (for/list ([v vs]) (optimize-r1cs v)))]
        [(r1cs:rmul vs) (r1cs:rmul (for/list ([v vs]) (optimize-r1cs v)))]

        [else (tokamak:exit "not supported: ~a" arg-r1cs)]
    )
)