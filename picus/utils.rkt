#lang racket
(provide (all-defined-out))

(define (contains? l e)
    (if (null? l)
        #f
        (if (equal? e (car l))
            #t
            (contains? (cdr l) e)
        )
    )
)
(define (slice l offset n) (take (drop l offset) n))

; (note) this is little endian (i.e., little bytes come first)
(define (bytes->number b)
    (define (accu p0 rb0) 
        (if (null? rb0)
            0 ; done
            (+ (* p0 (car rb0)) (accu (* 256 p0) (cdr rb0))) ; (note) a byte contains 8 bits, which is 2^8=256
        )
    )
    (accu 1 (bytes->list b))
)