#lang racket
; switcher for selector related components
(require json
    (prefix-in tokamak: "../tokamak.rkt")
    ; selectors
    (prefix-in first: "./selectors/first-selector.rkt")
    (prefix-in counter: "./selectors/counter-selector.rkt")
)
(provide (rename-out
    [apply-selector apply-selector]
    [selector-feedback selector-feedback]
    [selector-init selector-init]
))

(define (apply-selector arg-selector)
    (cond
        [(equal? "first" arg-selector) first:apply-selector]
        [(equal? "counter" arg-selector) counter:apply-selector]
        [else (tokamak:exit "unsupported selector: ~a." arg-selector)]
    )
)
(define (selector-feedback arg-selector)
    (cond
        [(equal? "first" arg-selector) first:selector-feedback]
        [(equal? "counter" arg-selector) counter:selector-feedback]
        [else (tokamak:exit "unsupported selector: ~a." arg-selector)]
    )
)
(define (selector-init arg-selector)
    (cond
        [(equal? "first" arg-selector) first:selector-init]
        [(equal? "counter" arg-selector) counter:selector-init]
        [else (tokamak:exit "unsupported selector: ~a." arg-selector)]
    )
)