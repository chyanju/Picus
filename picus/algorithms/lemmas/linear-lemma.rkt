#lang racket
; this implements the linear lemma:
;   if c * x = (unique), and c != 0 is a constant, then x is also uniquely determined
; note that this lemma doesn't apply to the following:
;   c * x0 * x1 = (unique), and c * x0 != 0
(require
    (prefix-in r1cs: "../../r1cs/r1cs-grammar.rkt")
)
(provide (rename-out
    [compute-cdmap compute-cdmap]
    [compute-rcdmap compute-rcdmap]
    [apply-lemma apply-lemma]
))

; global variable, cached rcdmap
; store and ref with tag (key)
(define :cached-rcdmaps (make-hash))

; get constraint dependency map
; input is the *normalized main constraint part* of r1cs ast
;   - main constraints is the `cnsts part (r1cs:rcmds) from parse-r1cs
; returns a map of:
;   - key: index of a variable
;   - val: list of sets of variables
; meaning: if a key wants to be determined as unique,
;          one of the sets from val should be completely determined
; construction rules (++terms):
;   - only non-non-linear (YES, no typo here) variable can be determined (put to key)
;     because for x*y=k, x can't be guaranteed to be unique,
;     even if knowing y and k (due to field mul)
(define (compute-cdmap arg-cnsts [arg-indexonly #f])
    (define res (make-hash))
    ; for every single constraint
    (for ([p (r1cs:rcmds-vs arg-cnsts)])
        (define all-vars (r1cs:get-assert-variables p arg-indexonly))
        (define nonlinear-vars (r1cs:get-assert-variables/nonlinear p arg-indexonly))
        ; (note) you can't use linears directly, because one var could be both linear and non-linear
        ;        in this case, it's still non-linear in the current constraint
        (define deducible-vars (set-subtract all-vars nonlinear-vars))
        (for ([key deducible-vars])
            (when (not (hash-has-key? res key)) (hash-set! res key (list )))
            (hash-set! res key (cons (set-subtract all-vars (list->set (list key))) (hash-ref res key)))
        )
    )
    res
)

; get a reversed cdmap
;   - arg-indexonly: whether to extract the indices instead of keeping the full variable name
; example output:
;   #<set: x10> => #<set: x4>
;   #<set: x6 x14 x12 x11> => #<set: x13>
;   #<set: x5 x14 x12> => #<set: x11>
;   #<set: x5 x14 x11> => #<set: x12>
;   #<set: x2> => #<set: x6>
;   #<set: x8> => #<set: x4>
;   #<set: x1> => #<set: x5>
;   #<set: x9> => #<set: x3>
;   #<set: x7> => #<set: x3>
(define (compute-rcdmap arg-cnsts [arg-indexonly #f] [arg-tag 'default])
    (cond
        ; there's a cached version for the given tag, no more computation, just fetch & return
        [(hash-has-key? :cached-rcdmaps arg-tag) (hash-ref :cached-rcdmaps arg-tag)]
        ; no cached version, compute, cache and return
        [else
            (define res (compute-cdmap arg-cnsts arg-indexonly))
            (define new-res (make-hash))
            (for ([key (hash-keys res)])
                (define vals (hash-ref res key))
                (for ([val vals])
                    (when (not (hash-has-key? new-res val)) (hash-set! new-res val (list )))
                    (hash-set! new-res val (cons key (hash-ref new-res val)))
                )
            )
            ; make immutable
            (for ([key (hash-keys new-res)])
                (hash-set! new-res key (list->set (hash-ref new-res key)))
            )
            ; store to cache
            (hash-set! :cached-rcdmaps arg-tag new-res)
            ; return
            new-res
        ]
    )
)

; recursively apply linear lemma
(define (apply-lemma rcdmap ks us)
    (printf "  # propagation (linear lemma): ")
    (define new-ks (list->set (set->list ks))) ; (fixme) do this to copy into a mutable set, required by set-* operations
    (define new-us (list->set (set->list us))) ; (fixme) same as above
    (define rec? #f) ; whether propagate should be called again
    (for* ([key (hash-keys rcdmap)])
        (when (set-empty? (set-subtract key ks))
            ; all ks are in key, propagate
            (set! new-ks (set-union new-ks (hash-ref rcdmap key)))
            (set! new-us (set-subtract new-us (hash-ref rcdmap key)))
        )
    )
    (let ([s0 (set-subtract new-ks ks)])
        (if (set-empty? s0)
            (printf "none.\n")
            (printf "~a added.\n" s0)
        )
    )
    (if (= (set-count ks) (set-count new-ks))
        ; no updates, return now
        (values new-ks new-us)
        ; has updates, call again
        (apply-lemma rcdmap new-ks new-us)
    )
)