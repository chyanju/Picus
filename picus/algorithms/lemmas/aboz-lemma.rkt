#lang racket
; this implements the all-but-one-zero lemma
; y0 + ... + yn = (unique)
; y0 * (x-0) = 0
; ...
; yn * (x-n) = 0
;
; then y0, ..., yn are unique

; (fixme) this implements a special case of all-but-one-zero lemma, e.g.,
;   x8 * (x7 - 0) = 0
;   (1 - x8) * (x7 - 1) = 0

; ( (1 * x11) ) * ( (1 * x8) ) = 0
; ( (ps1 * x0) + (1 * x11) ) * ( (1 * x9) ) = 0
; ( 0 ) * ( 0 ) = (1 * x8) + (1 * x9) + (ps1 * x10)
; if x7 is unique, then x8 and (1-x8) are unique

; its p1cnsts form is different, see process below
; (fixme) this implements an inefficient version, could be improved

(require
    (prefix-in config: "../../config.rkt")
    (prefix-in tokamak: "../../tokamak.rkt")
    (prefix-in r1cs: "../../r1cs/r1cs-grammar.rkt")
)
(provide (rename-out
    [apply-lemma apply-lemma]
))

; recursively apply linear lemma
(define (apply-lemma ks us p1cnsts range-vec)
    ; (printf "  # propagation (aboz lemma): ")
    (define tmp-ks (list->set (set->list ks)))
    (define tmp-us (list->set (set->list us)))

    (set!-values (tmp-ks tmp-us) (process tmp-ks tmp-us p1cnsts range-vec))
    ; (let ([s0 (set-subtract tmp-ks ks)])
    ;     (if (set-empty? s0)
    ;         (printf "none.\n")
    ;         (printf "~a added.\n" s0)
    ;     )
    ; )

    ; apply once is enough, return
    (values tmp-ks tmp-us)
)

(define (extract-signal-id x) (string->number (substring x 1)))

(define (process ks us arg-r1cs range-vec)
    (define tmp-ks (list->set (set->list ks)))
    (define tmp-us (list->set (set->list us)))
    (define n (length (r1cs:rcmds-vs arg-r1cs)))
    (for ([i (range (- n 2))])
        (define icnsts (r1cs:rcmds (list
            (r1cs:rcmds-ref arg-r1cs i)
            (r1cs:rcmds-ref arg-r1cs (+ 1 i))
            (r1cs:rcmds-ref arg-r1cs (+ 2 i))
        )))
        (define res (match-full icnsts))
        (when (not (null? res))
            ; matched, analyze vars
            ; list is: x, y0, y1, c
            ; if c and x are unique, then y0 and y1 are unique
            (define xid (extract-signal-id (list-ref res 0)))
            (define cid (extract-signal-id (list-ref res 3)))
            (define y0id (extract-signal-id (list-ref res 1)))
            (define y1id (extract-signal-id (list-ref res 2)))
            (when (and (set-member? tmp-ks xid) (set-member? tmp-ks cid))
                (set! tmp-ks (set-union tmp-ks (set y0id y1id)))
                (set! tmp-us (set-subtract tmp-us (set y0id y1id)))
            )
        )
    )
    (values tmp-ks tmp-us)
)

; (fixme) list-no-order should be enforced
; return a list of: x, y0, y1, c
(define (match-full arg-obj)
    (match arg-obj

        ; ==================================
        ; ==== non finite field version ====
        ; ==================================
        [(r1cs:rcmds (list

            ; eq0
            (r1cs:rassert (r1cs:ror (list
                (r1cs:req (r1cs:rvar "zero") (r1cs:rvar xa)) ; (x-0)
                (r1cs:req (r1cs:rvar "zero") (r1cs:rvar y0a)) ; y0
            )))

            ; eq1
            (r1cs:rassert (r1cs:ror (list
                (r1cs:req (r1cs:rvar "zero") (r1cs:rmod (r1cs:radd (list (r1cs:rvar "ps1") (r1cs:rvar xb))) (r1cs:rvar "p"))) ; (x-1)
                (r1cs:req (r1cs:rvar "zero") (r1cs:rvar y1a)) ; y1
            )))

            ; eq2
            ; y0 + y1 - c = 0, which is y0 + y1 = c
            (r1cs:rassert (r1cs:req
                (r1cs:rvar "zero")
                (r1cs:rmod (r1cs:radd (list (r1cs:rvar y0b) (r1cs:rvar y1b) (r1cs:rmul (list (r1cs:rvar "ps1") (r1cs:rvar c))))) (r1cs:rvar "p"))
            ))

        ))
            ; pattern matched, check for value
            (if (and (equal? xa xb) (equal? y0a y0b) (equal? y1a y1b))
                ; valu matched
                (list xa y0a y1a c)
                ; not matched
                null
            )
        ]

        ; ==============================
        ; ==== finite field version ====
        ; ==============================
        [(r1cs:rcmds (list

            ; eq0
            (r1cs:rassert (r1cs:ror (list
                (r1cs:req (r1cs:rvar "zero") (r1cs:rvar xa)) ; (x-0)
                (r1cs:req (r1cs:rvar "zero") (r1cs:rvar y0a)) ; y0
            )))

            ; eq1
            (r1cs:rassert (r1cs:ror (list
                (r1cs:req (r1cs:rvar "zero") (r1cs:radd (list (r1cs:rvar "ps1") (r1cs:rvar xb)))) ; (x-1)
                (r1cs:req (r1cs:rvar "zero") (r1cs:rvar y1a)) ; y1
            )))

            ; eq2
            ; y0 + y1 - c = 0, which is y0 + y1 = c
            (r1cs:rassert (r1cs:req
                (r1cs:rvar "zero")
                (r1cs:radd (list (r1cs:rvar y0b) (r1cs:rvar y1b) (r1cs:rmul (list (r1cs:rvar "ps1") (r1cs:rvar c)))))
            ))

        ))
            ; pattern matched, check for value
            (if (and (equal? xa xb) (equal? y0a y0b) (equal? y1a y1b))
                ; valu matched
                (list xa y0a y1a c)
                ; not matched
                null
            )
        ]

        ; otherwise, do not rewrite
        [_ null]
    )
)