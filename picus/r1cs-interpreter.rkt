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

; helper function
(define (next-symbolic-integer)
    (define-symbolic* r1cs.x integer?)
    ; restrict in prime field
    (assert (&&
        (>= r1cs.x 0)
        (< r1cs.x config:p)
    ))
    r1cs.x
)

; constants
(define int-zero 0)
(define int-one 1)

(define (interpret-r1cs arg-r1cs arg-xlist)
    ; first create a list of all symbolic variables according to nwires
    (define nwires (r1cs:get-nwires arg-r1cs))
    ; strictly align with wid
    (define xlist (if (null? arg-xlist)
        ; create fresh new
        ; (note) need nwires+1 to account for 1st input
        (for/list ([_ (+ 1 nwires)]) (next-symbolic-integer))
        ; use existing one
        arg-xlist
    ))

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
        (define terms-a (cons int-zero (for/list ([w0 wids-a] [f0 factors-a])
            (* f0 (list-ref xlist w0))
        )))
        ; (printf "# wids-b is: ~a\n" wids-b)
        (define terms-b (cons int-zero (for/list ([w0 wids-b] [f0 factors-b])
            (* f0 (list-ref xlist w0))
        )))
        ; (printf "# wids-c is: ~a\n" wids-c)
        (define terms-c (cons int-zero (for/list ([w0 wids-c] [f0 factors-c])
            (* f0 (list-ref xlist w0))
        )))
        ; (printf "# done wids\n")

        ; assemble equation: A*B = C
        (define sum-a (apply + terms-a))
        (define sum-b (apply + terms-b))
        (define sum-c (apply + terms-c))
        ; (define ret-cnst (= sum-c (* sum-a sum-b)))
        ; (define ret-cnst (= sum-c (* sum-a sum-b)))
        (define ret-cnst (=
            (modulo sum-c config:p)
            (modulo (* sum-a sum-b) config:p)
        ))

        ; return this assembled constraint
        ret-cnst
    ))

    ; return symbolic variable list and symbolic constraint list
    ; note that according to r1cs spec,
    ; "https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md#general-considerations"
    ; so we append an additional constraint here
    ; see: https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md#general-considerations
    ; (values xlist sconstraints)
    (values xlist (cons (= int-one (list-ref xlist 0)) sconstraints))
)