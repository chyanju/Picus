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

(define (get-elem-map l x)
    (if (null? l)
        (values #f -1)
        (if (= (car (list-ref l 0)) x)
            (values #t (list-ref (car l) 1))
            (get-elem-map (cdr l) x)
        )
    )
)

(define (union a b)
    (if (null? b) 
        a
        (if (contains? a (car b))
            (union a (cdr b))
            (union (cons (car b) a) (cdr b))
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

; (note) this only detects first elems
;        no checking for full shapes
(define (get-list-dims0 l)
    (cond
        [(list? l) (cons (length l) (get-list-dims0 (car l)))]
        [else (list)]
    )
)

; provide an access path to access element of a list
(define (nested-list-ref l rs)
    (cond
        [(null? rs) l]
        [else (nested-list-ref (list-ref l (car rs)) (cdr rs))]
    )
)
