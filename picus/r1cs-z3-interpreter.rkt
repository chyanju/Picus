#lang rosette
(require
    (prefix-in tokamak: "./tokamak.rkt")
    (prefix-in utils: "./utils.rkt")
    (prefix-in config: "./config.rkt")
    (prefix-in r1cs: "./r1cs.rkt")
)
(provide (rename-out
    [interpret-r1cs interpret-r1cs]
))

; constants
(define str-zero "0")
(define str-one "1")
; (define p-1 (format "~a" (- config:p 1)))

; x is factor, and y is x
(define (opt-format-mul x y)
    (let ([x0 (format "~a" x)]
          [y0 (format "~a" y)])
        (cond
            [(|| (equal? "0" x0) (equal? "0" y0)) "0"]
            [(&& (equal? "1" x0) (equal? "1" y0)) "1"]
            ; [(&& (equal? "x0" x0) (equal? "x0" y0)) "1"] ; inlining x0==1
            [(equal? "1" x0) (format "~a" y0)]
            [(equal? "1" y0) (format "~a" x0)]
            ; [(equal? "x0" x0) (format "~a" y0)] ; inlining x0==1
            ; [(equal? "x0" y0) (format "~a" x0)] ; inlining x0==1
            [else (format "(* ~a ~a)" x0 y0)]
        )
    )
)

(define (opt-format-add x y)
    (let ([x0 (format "~a" x)]
          [y0 (format "~a" y)])
        (cond
            [(&& (equal? "0" x0) (equal? "0" y0)) "0"]
            [(equal? "0" x0) (format "~a" y0)]
            [(equal? "0" y0) (format "~a" x0)]
            [else (format "(+ ~a ~a)" x0 y0)]
        )
    )
)

(define (opt-format-cases-mul a b c)
    (define case-1
        (format "(=> (not (= 0 (mod ~a ~a))) (= ~a (div (mod ~a ~a) (mod ~a ~a))))"
            a config:p b a config:p c config:p
        )
    )
    (define case-2
        (format "(=> (not (= 0 (mod ~a ~a))) (= ~a (div (mod ~a ~a) (mod ~a ~a))))"
            b config:p a b config:p c config:p
        )
    )
    (define case-3
        (format "(= 0 (mod (- ~a ~a) p))" 
            (opt-format-mul a b) c
        )
    )
    (format "(assert (and ~a ~a ~a))\n"
        case-1 case-2 case-3
    )
)

(define (normalize f0)
    (if (> f0 (quotient config:p 2))
        (- f0 config:p)
        f0
    )
)

(define (get-max-value-linear wids factors)
    (foldl 
        (lambda (x y z) 
            (+ z (if (= x 0) (normalize y) (if (> (normalize y) 0) (* (normalize y)(- config:p 1)) 0)))
        )
    0 wids factors
    )
)

(define (get-min-value-linear wids factors)
    (foldl 
        (lambda (x y z) 
             (+ z (if (= x 0) (normalize y) (if (< (normalize y) 0) (* (normalize y)(- config:p 1)) 0)))
        )
    0 wids factors
    )
)


(define (extract-signals cnst)
    (define curr-block-a (r1cs:constraint-a cnst))
    (define curr-block-b (r1cs:constraint-b cnst))
    (define curr-block-c (r1cs:constraint-c cnst))

    (define wids-a (r1cs:constraint-block-wids curr-block-a))
    (define wids-b (r1cs:constraint-block-wids curr-block-b))
    (define wids-c (r1cs:constraint-block-wids curr-block-c))

    (append wids-a wids-b wids-c)
)


(define (interpret-r1cs arg-r1cs arg-xlist)
    (define raw-smt (list)) ; a list of raw smt strings

    ; first create a list of all symbolic variables according to nwires
    (define nwires (r1cs:get-nwires arg-r1cs))
    ; strictly align with wid
    (define xlist (if (null? arg-xlist)
        ; create fresh new
        (for/list ([i nwires]) (format "x~a" i))
        ; use existing one
        arg-xlist
    ))
    
    
    
    ; update smt
    ;(set! raw-smt (append raw-smt
    ;    (list "; ======== declaration and range constraints ======== ;")
    ;    (list "")
    ;    (for/list ([x xlist])
    ;        (if (&& (! (null? arg-xlist)) (string-prefix? x "x"))
    ;            ; provided list with already defined x, skip
    ;            (format "; ~a: already defined\n" x)
    ;            ; otherwise you need to define this variable
    ;            (format "(declare-const ~a Int)\n(assert (<= 0 ~a))\n(assert (< ~a ~a))\n"
    ;            x x x config:p)
    ;        )
    ;    )
    ;)) ; update smt
    
    ; generate the definitions of the signals
    (define signal-definitions
        (for/list ([x xlist])
            (if (&& (! (null? arg-xlist)) (string-prefix? x "x"))
                ; provided list with already defined x, skip
                (format "; ~a: already defined\n" x)  
                ; otherwise you need to define this variable
                (format "(declare-const ~a Int)\n(assert (<= 0 ~a))\n(assert (< ~a ~a))\n"
                x x x config:p)
            )
        )
    )
    

    ; then start creating constraints
    (define m (r1cs:get-mconstraints arg-r1cs))
    (define rconstraints (r1cs:get-constraints arg-r1cs)) ; r1cs constraints

    ; map from signals to constraints where they appear
    (define signal2constraints (for/list ([i nwires])
        (if (= i 0)
            '()
            (filter
                (lambda (x) (utils:contains? (extract-signals (list-ref rconstraints x)) i)) 
                (range 0 m)
            )
        )
    ))
    
    ; map from constraints to signals where they appear
    (define constraints2signal (for/list ([i m])
        (filter
            (lambda (x) (utils:contains? (list-ref signal2constraints x) i)) 
            (range 1  nwires)
        )
    ))

    ; symbolic constraints
    (define sconstraints (for/list ([index m])

        (define cnst (list-ref rconstraints index))
        ; get block
        (define curr-block-a (r1cs:constraint-a cnst))
        (define curr-block-b (r1cs:constraint-b cnst))
        (define curr-block-c (r1cs:constraint-c cnst))

        ; process block a
        (define nnz-a (r1cs:constraint-block-nnz curr-block-a))
        (define wids-a (r1cs:constraint-block-wids curr-block-a))
        (define factors-a (r1cs:constraint-block-factors curr-block-a))

        ; process block b
        (define nnz-b (r1cs:constraint-block-nnz curr-block-b))
        (define wids-b (r1cs:constraint-block-wids curr-block-b))
        (define factors-b (r1cs:constraint-block-factors curr-block-b))

        ; process block c
        (define nnz-c (r1cs:constraint-block-nnz curr-block-c))
        (define wids-c (r1cs:constraint-block-wids curr-block-c))
        (define factors-c (r1cs:constraint-block-factors curr-block-c))

        ; assemble symbolic terms
        ; note that terms could be empty, in which case 0 is used
        ; (printf "# wids-a is: ~a\n" wids-a)
        (define terms-a (cons str-zero (for/list ([w0 wids-a] [f0 factors-a])
            ; (format "(* ~a ~a)" f0 x0)
            ; optimized form
            (let ([x0 (list-ref xlist w0)])
                (if (= w0 0)
                    (normalize f0)
                    (opt-format-mul (normalize f0) x0)
                )
            )
        )))
        ; (printf "# wids-b is: ~a\n" wids-b)
        (define terms-b (cons str-zero (for/list ([w0 wids-b] [f0 factors-b])
            ; (format "(* ~a ~a)" f0 x0)
            ; optimized form
            (let ([x0 (list-ref xlist w0)])
                (if (= w0 0)
                    (normalize f0)
                    (opt-format-mul (normalize f0) x0)
                )
            )
        )))
        ; (printf "# wids-c is: ~a\n" wids-c)
        (define terms-c (cons str-zero (for/list ([w0 wids-c] [f0 factors-c])
            ; (format "(* ~a ~a)" f0 x0)
            ; optimized form
            (let ([x0 (list-ref xlist w0)])
                (if (= w0 0)
                    (normalize f0)
                    (opt-format-mul (normalize f0) x0)
                )
            )
        )))
        ; (printf "# done wids\n")

        (define sum-a (foldl opt-format-add "0" terms-a))
        (define sum-b (foldl opt-format-add "0" terms-b))
        (define sum-c (foldl (lambda (v l) (opt-format-add v l)) "0" terms-c))
        ; original form
        ; (define ret-cnst (format "(assert (= ~a ~a))\n"
        ;     (format "(mod ~a ~a)" sum-c config:p)
        ;     (format "(mod ~a ~a)"
        ;         (format "(* ~a ~a)" sum-a sum-b)
        ;         config:p
        ;     )
        ; ))
        ; simplified form
        ; (define ret-cnst (format "(assert (= 0 ~a))\n"
        ;     (format "(mod ~a ~a)"
        ;         (format "(- (* ~a ~a) ~a)" sum-a sum-b sum-c)
        ;         config:p
        ;     )
        ; ))
        ; optimized & simplified form
        (define ret-cnst 
            (cond
                [(equal? "0" sum-c)
                    (define max-k-a (floor (/ (get-max-value-linear wids-a factors-a) config:p)))
                    (define min-k-a (ceiling (/ (get-min-value-linear wids-a factors-a) config:p)))
                    ;(printf "Sum ~a : min ~a max ~a \n" sum-a min-k-a max-k-a)
                    (define max-k-b (floor (/ (get-max-value-linear wids-a factors-a) config:p)))
                    (define min-k-b (ceiling (/ (get-min-value-linear wids-a factors-a) config:p)))
                    ;(printf "Sum ~a : min ~a max ~a \n" sum-b min-k-b max-k-b)
                    (format "(assert (or ~a ~a))\n"
                        (if (= max-k-a min-k-a)
                            (format "(= ~a ~a)\n"
                                sum-a
                                (* max-k-a config:p)
                            ) 
                            (format "(= 0 (mod ~a ~a))\n"
                                sum-a
                                config:p
                            )
                        )
                        (if (= max-k-b min-k-b)
                            (format "(= ~a ~a)\n"
                                sum-b
                                (* max-k-b config:p)
                            ) 
                            (format "(= 0 (mod ~a ~a))\n"
                                sum-b
                                config:p
                            )
                        )
                    )
                ]
                [(|| (equal? "0" sum-a) (equal? "0" sum-b))
                    
                    (define max-k (floor (/ (get-max-value-linear wids-c factors-c) config:p)))
                    (define min-k (ceiling (/ (get-min-value-linear wids-c factors-c) config:p)))
                    ;(printf "Sum ~a : min ~a max ~a \n" sum-c min-k max-k)
                        (if (= max-k min-k)
                            (format "(assert (= ~a ~a))\n"
                                sum-c
                                (* max-k config:p)
                            ) 
                            (format "(assert (= 0 (mod ~a ~a)))\n"
                                sum-c
                                config:p
                            )
                    )
                ]    
                [else 
                    (opt-format-cases-mul sum-a sum-b sum-c)
                ]
            )
        )


        ; return this assembled constraint
        ret-cnst
    ))

    ; update smt
    ;(set! raw-smt (append
        ;raw-smt
        ;(list "; ======== r1cs constraints ======== ;")
        ;(list "")
        ;sconstraints
    ;))

    ; return symbolic variable list and symbolic constraint list
    ; note that according to r1cs spec,
    ; "https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md#general-considerations"
    ; so we append an additional constraint here
    ; see: https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md#general-considerations
    ; (values xlist sconstraints)
    (values xlist signal-definitions sconstraints signal2constraints constraints2signal)
)
