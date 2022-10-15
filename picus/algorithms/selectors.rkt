#lang rosette
(provide (rename-out
    ; shared methods
    [signal-weights-reset! signal-weights-reset!]
    [signal-weights-set! signal-weights-set!]
    [signal-weights-ref signal-weights-ref]
    [signal-weights-inc! signal-weights-inc!]
    [signal-weights-dec! signal-weights-dec!]

    [pp-counter-select pp-counter-select]
    [pp-naive-select pp-naive-select]
))

; shared stateful variables and methods
; signal weights
(define signal-weights null)
(define (signal-weights-reset!) (set! signal-weights (make-hash)))
(define (signal-weights-set! k v) (hash-set! signal-weights k v))
(define (signal-weights-ref k) (hash-ref signal-weights k))
(define (signal-weights-inc! k v) (hash-set! signal-weights k (+ (hash-ref signal-weights k) v)))
(define (signal-weights-dec! k v) (hash-set! signal-weights k (- (hash-ref signal-weights k) v)))

; =======================
; counter select strategy
; choose the signal that appears the most in the keys of rcdmap
; i.e. the most "critical" one for propagation
(define state-rcdkey-counter null) ; cached rcdkey counter, key: index, val: count
; key first select: select the key with higher appearance in rcdmap
(define (pp-counter-select rcdmap uspool)
    ; check for existence of counter
    (when (null? state-rcdkey-counter)
        ; counter not created yet, create one
        (define tmp-counter (make-hash))
        (for ([keys (hash-keys rcdmap)])
            (for ([key keys])
                (when (! (hash-has-key? tmp-counter key)) (hash-set! tmp-counter key 0))
                (hash-set! tmp-counter key (+ 1 (hash-ref tmp-counter key)))
            )
        )
        (set! state-rcdkey-counter tmp-counter)
    )
    ; copy the counter and filter out non uspool ones
    (define tmp-counter (make-hash))
    (for ([key (hash-keys state-rcdkey-counter)])
        (when (set-member? uspool key)
            ; copy and calculate the weight
            (hash-set! tmp-counter key
                (+ (hash-ref state-rcdkey-counter key) (signal-weights-ref key))
            )
        )
    )
    ; add remaining uspool ones into the counter
    (for ([key uspool])
        (when (! (hash-has-key? tmp-counter key)) (hash-set! tmp-counter key 0)))
    ; sort and pick
    (define p0 (argmax cdr (hash->list tmp-counter)))
    ; return
    (car p0)
)

; =====================
; naive select strategy
; simply choose the first signal from the pool
(define (pp-naive-select rcdmap uspool) (set-first uspool))