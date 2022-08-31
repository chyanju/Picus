#lang rosette
; this is a template for optimizer
(require
    (prefix-in tokamak: "../tokamak.rkt")
    (prefix-in utils: "../utils.rkt")
    (prefix-in config: "../config.rkt")
    (prefix-in r1cs: "../r1cs-grammar.rkt")
)
(provide (rename-out
    [optimize-r1cs optimize-r1cs]
))

(define (optimize-r1cs arg-r1cs)
    (match arg-r1cs

        ; command level
        [(r1cs:rcmds vs) (r1cs:rcmds (for/list ([v vs]) (optimize-r1cs v)))]
        [(r1cs:rraw v) (r1cs:rraw v)]
        [(r1cs:rlogic v) (r1cs:rlogic (optimize-r1cs v))]
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

        [(r1cs:rand vs) (r1cs:rand (for/list ([v vs]) (optimize-r1cs v)))]
        [(r1cs:ror vs) (r1cs:ror (for/list ([v vs]) (optimize-r1cs v)))]
        [(r1cs:rimp lhs rhs) (r1cs:rimp (optimize-r1cs lhs) (optimize-r1cs rhs))]

        [(r1cs:rint v) (r1cs:rint v)]
        [(r1cs:rstr v) (r1cs:rstr v)]
        [(r1cs:rvar v) (r1cs:rvar v)]
        [(r1cs:rtype v) (r1cs:rtype v)]

        [(r1cs:radd vs) (r1cs:radd (for/list ([v vs]) (optimize-r1cs v)))]
        [(r1cs:rsub vs) (tokamak:exit "cvc5 doesn't support sub")]
        [(r1cs:rmul vs) (r1cs:rmul (for/list ([v vs]) (optimize-r1cs v)))]
        [(r1cs:rneg v) (r1cs:rneg (optimize-r1cs v))]
        [(r1cs:rmod v mod) (tokamak:exit "cvc5 doesn't support mod")]

        [else (tokamak:exit "not supported: ~a" arg-r1cs)]
    )
)