#lang rosette
; this interprets binary r1cs into its grammar representation
(require
    (prefix-in tokamak: "../tokamak.rkt")
    (prefix-in utils: "../utils.rkt")
    (prefix-in config: "../config.rkt")
    (prefix-in r1cs: "./r1cs-grammar.rkt")
)
(provide (rename-out
    [parse-r1cs parse-r1cs]
))

(define (parse-r1cs arg-r1cs arg-xlist)

    ; a list of options
    (define raw-options (list
        (r1cs:rlogic (r1cs:rstr "QF_FF"))
        (r1cs:rraw "(set-info :smt-lib-version 2.6)")
        (r1cs:rraw "(set-info :category \"crafted\")")
        (r1cs:rraw (format "(define-sort F () (_ FiniteField ~a))" config:p))
    ))

    (define raw-declarations (list)) ; a list of commands
    (define raw-cmds (list)) ; a list of commands

    ; first create a list of all symbolic variables according to nwires
    (define nwires (r1cs:get-nwires arg-r1cs))
    ; strictly align with wid
    (define xlist (if (null? arg-xlist)
        ; create fresh new
        (for/list ([i nwires]) (format "x~a" i))
        ; use existing one
        arg-xlist
    ))

    ; add declarations for variables
    ; for cvc5, no range constraints are needed
    (set! raw-declarations (append raw-declarations
        (list (r1cs:rcmt (r1cs:rstr "======== declaration constraints ========")))
        (for/list ([x xlist])
            (if (&& (! (null? arg-xlist)) (string-prefix? x "x"))
                ; provided list with already defined x, skip
                (r1cs:rcmt (r1cs:rstr (format "~a: already defined" x)))
                ; otherwise you need to define this variable
                (r1cs:rdef (r1cs:rvar (format "~a" x)) (r1cs:rtype "F"))
            )
        )
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

        ; ======== parse into original form: A*B = C ========
        ; assemble symbolic terms
        ; note that terms could be empty, in which case 0 is used
        ; (define terms-a (cons (r1cs:rint 0) (for/list ([w0 wids-a] [f0 factors-a])
        ;     ; (format "(* ~a ~a)" f0 x0)
        ;     (let ([x0 (list-ref xlist w0)])
        ;         (r1cs:rmul (list (r1cs:rint f0) (r1cs:rvar x0)))
        ;     )
        ; )))
        ; (define terms-b (cons (r1cs:rint 0) (for/list ([w0 wids-b] [f0 factors-b])
        ;     ; (format "(* ~a ~a)" f0 x0)
        ;     (let ([x0 (list-ref xlist w0)])
        ;         (r1cs:rmul (list (r1cs:rint f0) (r1cs:rvar x0)))
        ;     )
        ; )))
        ; (define terms-c (cons (r1cs:rint 0) (for/list ([w0 wids-c] [f0 factors-c])
        ;     ; (format "(* ~a ~a)" f0 x0)
        ;     (let ([x0 (list-ref xlist w0)])
        ;         (r1cs:rmul (list (r1cs:rint f0) (r1cs:rvar x0)))
        ;     )
        ; )))
        ; (define sum-a (r1cs:radd terms-a))
        ; (define sum-b (r1cs:radd terms-b))
        ; (define sum-c (r1cs:radd terms-c))
        ; ; original form: A*B = C
        ; (define ret-cnst (r1cs:rassert (r1cs:req
        ;     (r1cs:rmod (r1cs:rmul (list sum-a sum-b)) (r1cs:rint config:p))
        ;     (r1cs:rmod sum-c (r1cs:rint config:p))
        ; )))

        ; ======== parse into expanded form: A*B = C but expand A*B into ++terms ========
        ; assemble symbolic terms
        ; note that terms could be empty, in which case 0 is used
        (define terms-a (for/list ([w0 wids-a] [f0 factors-a])
            ; (format "(* ~a ~a)" f0 x0)
            (let ([x0 (list-ref xlist w0)])
                (cons f0 x0)
            )
        ))
        (define terms-b (for/list ([w0 wids-b] [f0 factors-b])
            ; (format "(* ~a ~a)" f0 x0)
            (let ([x0 (list-ref xlist w0)])
                (cons f0 x0)
            )
        ))
        (define terms-c (for/list ([w0 wids-c] [f0 factors-c])
            ; (format "(* ~a ~a)" f0 x0)
            (let ([x0 (list-ref xlist w0)])
                (cons f0 x0)
            )
        ))
        ; A*B = C but expand A*B into ++terms
        (define ret-cnst (r1cs:rassert (r1cs:req
            ; A*B part
            (if (|| (empty? terms-a) (empty? terms-b))
                ; A*B is empty
                (r1cs:rint 0)
                ; A*B is not empty
                (r1cs:radd (for*/list ([va terms-a][vb terms-b])
                    (r1cs:rmul (list
                        (r1cs:rint (remainder (* (car va) (car vb)) config:p))
                        (r1cs:rvar (cdr va))
                        (r1cs:rvar (cdr vb))
                    ))
                ))
            )
            ; C part
            (if (empty? terms-c)
                ; C is empty
                (r1cs:rint 0)
                ; C is not empty
                (r1cs:radd (for/list ([v terms-c]) (r1cs:rmul (list (r1cs:rint (car v)) (r1cs:rvar (cdr v))))))
            )
        )))

        ; return this assembled constraint
        ret-cnst
    ))

    ; update smt with comments and fixed constraints
    (set! raw-cmds (append
        raw-cmds
        sconstraints
        (list (r1cs:rassert (r1cs:req
            (r1cs:rint 1) (r1cs:rvar (format "~a" (list-ref xlist 0)))
        )))
    ))

    (values
        xlist
        (r1cs:rcmds raw-options)
        (r1cs:rcmds raw-declarations)
        (r1cs:rcmds raw-cmds)
    )
)
