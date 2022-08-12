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
    (set! raw-smt (append raw-smt
        (list "; ======== declaration and range constraints ======== ;")
        (list "")
        (for/list ([x xlist])
            (if (&& (! (null? arg-xlist)) (string-prefix? x "x"))
                ; provided list with already defined x, skip
                (format "; ~a: already defined\n" x)
                ; otherwise you need to define this variable
                (format "(declare-const ~a Int)\n(assert (<= 0 ~a))\n(assert (< ~a ~a))\n"
                x x x config:p)
            )
        )
    )) ; update smt

    ; then start creating constraints
    (define m (r1cs:get-mconstraints arg-r1cs))
    (define rconstraints (r1cs:get-constraints arg-r1cs)) ; r1cs constraints

    ; symbolic constraints
    (define sconstraints (for/list ([cnst rconstraints])

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
                (opt-format-mul f0 x0)
            )
        )))
        ; (printf "# wids-b is: ~a\n" wids-b)
        (define terms-b (cons str-zero (for/list ([w0 wids-b] [f0 factors-b])
            ; (format "(* ~a ~a)" f0 x0)
            ; optimized form
            (let ([x0 (list-ref xlist w0)])
                (opt-format-mul f0 x0)
            )
        )))
        ; (printf "# wids-c is: ~a\n" wids-c)
        (define terms-c (cons str-zero (for/list ([w0 wids-c] [f0 factors-c])
            ; (format "(* ~a ~a)" f0 x0)
            ; optimized form
            (let ([x0 (list-ref xlist w0)])
                (opt-format-mul f0 x0)
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
            (if (equal? "0" sum-c)
                (format "(assert (or (= 0 (mod ~a ~a)) (= 0 (mod ~a ~a))))\n"
                    sum-a
                    config:p
                    sum-b
                    config:p
                )
                (format "(assert (= 0 (mod ~a ~a)))\n"
                    (format "(- ~a ~a)" (opt-format-mul sum-a sum-b) sum-c)
                    config:p
                )
            )
        )


        ; return this assembled constraint
        ret-cnst
    ))

    ; update smt
    (set! raw-smt (append
        raw-smt
        (list "; ======== r1cs constraints ======== ;")
        (list "")
        sconstraints
    ))
    (set! raw-smt (append raw-smt (list (format "(assert (= 1 ~a))\n" (list-ref xlist 0)))))

    ; return symbolic variable list and symbolic constraint list
    ; note that according to r1cs spec,
    ; "https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md#general-considerations"
    ; so we append an additional constraint here
    ; see: https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md#general-considerations
    ; (values xlist sconstraints)
    (values xlist raw-smt)
)
