#lang racket
; this implements the rangecopy lemma (similar to Ecne Rule 4a)
; this will copy both the uniqueness status and ranges
(require
    (prefix-in config: "../../config.rkt")
    (prefix-in tokamak: "../../tokamak.rkt")
    (prefix-in r1cs: "../../r1cs/r1cs-grammar.rkt")
)
(provide (rename-out
    [apply-lemma apply-lemma]
))

; (todo) add later