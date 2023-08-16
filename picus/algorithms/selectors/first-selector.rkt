#lang racket
(provide (rename-out
    [apply-selector apply-selector]
    [selector-init selector-init]
    [selector-feedback selector-feedback]
))

; naive select strategy
; simply choose the first signal from the pool
(define (apply-selector uspool cntx) (set-first uspool))
(define (selector-init nwires) (void))
(define (selector-feedback sid act) (void))