#lang rosette
; this implements the following lemma
;   .....
;
;

(require
    (prefix-in tokamak: "../tokamak.rkt")
    (prefix-in utils: "../utils.rkt")
    (prefix-in config: "../config.rkt")
    (prefix-in r1cs: "../r1cs-grammar.rkt")
)
(provide (rename-out
    [get-base-representations get-base-representations]
    [generate-base-representations-constraints generate-base-representations-constraints]
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

(define (get-single-coefficient v)
    (match v
        [(r1cs:rint v) (list v "x0")]
        [(r1cs:rvar v) (list 1 v)]
        [(r1cs:rmul vs) 
            (define l1 (get-single-coefficient (car vs)))
            (define l2 (get-single-coefficient (car (cdr vs))))
            (list (* (list-ref l1 0) (list-ref l2 0)) (list-ref l2 1))
        ]
        [else (tokamak:exit "not supported for single coefficient ~a" v)]
    )
)

(define (get-list-coefficients vs)
    (for/list ([v vs])
        (get-single-coefficient v)
    )
)

(define (check-base base sorted_coefs)
    (if (= (length sorted_coefs) 1)
        #t
        (if (= (modulo (* base (car sorted_coefs)) config:p) (car (cdr sorted_coefs)))
            (check-base base (cdr sorted_coefs))
            #f
        )
    )
)

(define (is-base-representation coefs-vars)
    (define sorted-coefs-vars (sort coefs-vars (lambda (x y) (< (list-ref x 0)  (list-ref y 0)))))

    (define sorted-coefs 
        (for/list ([v sorted-coefs-vars])
            (list-ref v 0)
        )
    )

    (define sorted-vars
        (for/list ([v sorted-coefs-vars])
            (string->number (substring (list-ref v 1) 1))
        )
    )

    (define pot_base (/ (car (cdr sorted-coefs)) (car sorted-coefs)))
    (if (> pot_base 1)
        (if (utils:contains? sorted-vars 0)
            (values #f 1 '())
            (values (check-base pot_base (cdr sorted-coefs)) pot_base sorted-vars)
        )
        (values #f 1 '())
    )
)

(define (get-potential-inits vs)
    (filter 
        (lambda (v) (and 
            (= 2 (length v)) 
            (or (= 1 (list-ref v 0)) (= (- config:p 1) (list-ref v 0))))
        )
        vs
    )
)

(define (generate-base-constraints vs)
    (define coefs (get-list-coefficients vs))
    (define potential-inits (get-potential-inits coefs))
    (define new-cnst '())
    (for ([init potential-inits])
        (define pos-coefs
            (filter
                (lambda (x) (not (string=? (car (cdr x)) (car (cdr init)))))
                (for/list ([elem coefs])
                    (list 
                        (if (= (car init) 1)
                            (- config:p (car elem))
                            (car elem)
                        )
                        (car (cdr elem))
                    )
                )
            )
        )
        (define-values (is-base base vars) (is-base-representation pos-coefs))
        (cond 
            [is-base (set! new-cnst (cons (list base vars (string->number (substring (list-ref init 1) 1))) new-cnst))]
        )
    )
    
    new-cnst
)

(define (get-base-representations arg-r1cs)
    ;(printf "Studying ~a\n" arg-r1cs)
    (match arg-r1cs

        ; command level
        ; probably the original block
        [(r1cs:rcmds vs) 
            (define new-reps (for/list ([v vs]) (get-base-representations v)))
            (foldl append (list) new-reps)
        ]
        
        [(r1cs:rassert v)(get-base-representations v)]

        ; sub-command level
        [(r1cs:req lhs rhs)
            (cond
                [(is-rint-zero lhs)
                    (match rhs
                        [(r1cs:radd vs)
                            ; apply lemma
                            (if (> (length vs) 2)
                                (generate-base-constraints vs)
                                '()
                            )
                            ;(printf "New cons: ~a\n" cnsts)
                        ]
                        [else '()]
                    )
                ]
                [(is-rint-zero rhs)
                    (match lhs
                        [(r1cs:radd vs)
                            ; apply lemma
                            (if (> (length vs) 2)
                                (generate-base-constraints vs)
                                '()
                            )
                        ]
                        [else '()]
                    )
                ]
                [else '()]
            )
        
        ]



        [(r1cs:rneq lhs rhs) (list)]
        [(r1cs:rleq lhs rhs) (list)]
        [(r1cs:rlt lhs rhs) (list)]
        [(r1cs:rgeq lhs rhs) (list)]
        [(r1cs:rgt lhs rhs) (list)]
        [(r1cs:rraw v) (list)]
        [(r1cs:rlogic v) (list)]
        [(r1cs:rdef v t) (list)]
        [(r1cs:rassert v) (list)]
        [(r1cs:rcmt v) (list)]
        [(r1cs:rsolve ) (list)]

        [(r1cs:rand vs) 
            (define new-reps (for/list ([v vs]) (get-base-representations v)))
            (foldl append (list) new-reps)
        ]
        [(r1cs:ror vs) 
            (list )
        ]
        [(r1cs:rstr v) (list )]

        [else (tokamak:exit "not supported for base representation: ~a" arg-r1cs)]
    )
)

(define (rebuild-addition vs)
    (r1cs:radd 
        (for/list ([v vs])
            (r1cs:rmul (list
                (r1cs:rint (list-ref v 0))
                (r1cs:rvar (list-ref v 1))
            ))
        )
    )
)

(define (belongs-to-base-field s base)
    (r1cs:req
        (r1cs:rmul(for/list [(pos (range base))]
            (r1cs:radd (list (r1cs:rint (- config:p pos)) (r1cs:rvar s)))
        ))
        (r1cs:rint 0)
    )

)

(define (generate-base-representations-constraints list-base-1 list-base-2)
    
    (define new-conds (for/list ([i (range (length list-base-1))])
        (define info-base-1 (list-ref list-base-1 i))
        (define base-1 (list-ref info-base-1 0))
        (define bounded-vars-1 (list-ref info-base-1 1))
        (define right-side-1 (list-ref info-base-1 2))

        (define info-base-2 (list-ref list-base-2 i))
        (define base-2 (list-ref info-base-2 0))
        (define bounded-vars-2 (list-ref info-base-2 1))
        (define right-side-2 (list-ref info-base-2 2))

        (assert (= base-1 base-2))

        (define base-assertions-1
            (r1cs:rand 
                (for/list ([x bounded-vars-1])
                    (belongs-to-base-field x base-1)
                )
            )
        )
        (define base-assertions-2 
            (r1cs:rand 
                (for/list ([x bounded-vars-2])
                    (belongs-to-base-field x base-1)
                )
            )
        )
        (define eq-assertion
            (r1cs:req 
                (rebuild-addition right-side-1)
                (rebuild-addition right-side-2)
            )
        )
        (define impl-conditions
            (r1cs:rand (list base-assertions-1 base-assertions-2 eq-assertion))
        )

        (define impl-postconditions
            (r1cs:rand 
                (for/list ([i (range (length bounded-vars-2))])
                    (r1cs:req 
                        (r1cs:rvar (list-ref bounded-vars-1 i)) 
                        (r1cs:rvar (list-ref bounded-vars-2 i))
                    )
                )
            )
        )
        (r1cs:rassert (r1cs:rimp impl-conditions impl-postconditions))
    
    ))
    (r1cs:rcmds new-conds)
)