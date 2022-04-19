#lang rosette
(require "./tokamak.rkt")
(require "./utils.rkt")
(require "./r1cs.rkt")
(provide (all-defined-out))
; note: this requires rosette, so it's separated from the r1cs library

; (fixme) currently you can only name it "x"
(define (next-symbolic-integer)
    (define-symbolic* x integer?)
    x
)

(define (interpret-r1cs arg-r1cs arg-xlist)
    ; first create a list of all symbolic variables according to nwires
    (define nwires (get-nwires arg-r1cs))
    ; strictly align with wid
    (define xlist (if (null? arg-xlist)
        ; create fresh new
        (for/list ([_ nwires]) (next-symbolic-integer))
        ; use existing one
        arg-xlist
    ))

    ; then start creating constraints
    (define m (get-mconstraints arg-r1cs))
    (define rconstraints (get-constraints arg-r1cs)) ; r1cs constraints

    ; symbolic constraints
    (define sconstraints (for/list ([cnst rconstraints])

        ; get block
        (define curr-block-a (constraint-a cnst))
        (define curr-block-b (constraint-b cnst))
        (define curr-block-c (constraint-c cnst))

        ; process block a
        (define nnz-a (constraint-block-nnz curr-block-a))
        (define wids-a (constraint-block-wids curr-block-a))
        (define factors-a (constraint-block-factors curr-block-a))

        ; process block b
        (define nnz-b (constraint-block-nnz curr-block-b))
        (define wids-b (constraint-block-wids curr-block-b))
        (define factors-b (constraint-block-factors curr-block-b))

        ; process block c
        (define nnz-c (constraint-block-nnz curr-block-c))
        (define wids-c (constraint-block-wids curr-block-c))
        (define factors-c (constraint-block-factors curr-block-c))

        ; assemble symbolic terms
        ; note that terms could be empty, in which case 0 is used
        (define terms-a (cons 0 (for/list ([w0 wids-a] [f0 factors-a])
            (* f0 (list-ref xlist w0))
        )))
        (define terms-b (cons 0 (for/list ([w0 wids-b] [f0 factors-b])
            (* f0 (list-ref xlist w0))
        )))
        (define terms-c (cons 0 (for/list ([w0 wids-c] [f0 factors-c])
            (* f0 (list-ref xlist w0))
        )))

        ; assemble equation: A*B = C
        (define sum-a (apply + terms-a))
        (define sum-b (apply + terms-b))
        (define sum-c (apply + terms-c))
        (define ret-cnst (equal? sum-c (* sum-a sum-b)))

        ; return this assembled constraint
        ret-cnst
    ))

    ; return symbolic variable list and symbolic constraint list
    ; note that according to r1cs spec,
    ; "https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md#general-considerations"
    ; so we append an additional constraint here
    ; see: https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md#general-considerations
    ; (values xlist sconstraints)
    (values xlist (cons (equal? 1 (list-ref xlist 0)) sconstraints))
)