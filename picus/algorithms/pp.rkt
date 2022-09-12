#lang rosette
; this implements the propagation & preserving algorithm with base lemma
(require
    (prefix-in tokamak: "../tokamak.rkt")
    (prefix-in utils: "../utils.rkt")
    (prefix-in config: "../config.rkt")
    (prefix-in r1cs: "../r1cs/r1cs-grammar.rkt")
)
(provide (rename-out
    [apply-inc apply-inc]
))

(define (get-dep arg-eq)

)

; get constraint dependency map
; input is the *optimized (by simple) main constraint part* of r1cs ast
;   - main constraints meaning the actual r1cs:eq part
; returns a map of:
;   - key: index of a variable
;   - val: list of list of indices of variables
; meaning: if a key wants to be determined as unique,
;          one of the lists from val should be completely determined
; construction rules (++terms):
;   - only a term with 1 variable can be determined (put to key)
;     because for x*y=k, x can't be guaranteed to be unique,
;     even if knowing y and k (due to field mul)
; (define (get-cdmap arg-eqs)
;     (for ([q arg-eqs])
;         (define cnst-ab (r1cs:req-lhs q))
;         (define cnst-c (r1cs:req-rhs q))

;     )
; )

(define (apply-inc
    r0 nwires mconstraints input-list output-list
    xlist original-options original-definitions original-cnsts
    xlist0 alternative-definitions alternative-cnsts
    arg-timeout arg-smt arg-weak
    solve state-smt-path parse-r1cs optimize interpret-r1cs
    )
    (define partial-cmds (r1cs:append-rcmds
        (r1cs:rcmds (list
            (r1cs:rcmt "================================")
            (r1cs:rcmt "======== original block ========")
            (r1cs:rcmt "================================")
        ))
        original-definitions
        original-cnsts
        (r1cs:rcmds (list
            (r1cs:rcmt "===================================")
            (r1cs:rcmt "======== alternative block ========")
            (r1cs:rcmt "===================================")
        ))
        alternative-definitions
        alternative-cnsts
    ))

    ; keep track of index of xlist (not xlist0 since that's incomplete)
    (define known-list (filter
        (lambda (x) (! (null? x)))
        (for/list ([i (range nwires)])
            (if (utils:contains? xlist0 (list-ref xlist i))
                i
                null
            )
        )
    ))
    (define unknown-list (filter
        (lambda (x) (! (null? x)))
        (for/list ([i (range nwires)])
            (if (utils:contains? xlist0 (list-ref xlist i))
                null
                i
            )
        )
    ))
    (printf "# initial knwon-list: ~a\n" known-list)
    (printf "# initial unknown-list: ~a\n" unknown-list)

)