#lang rosette
(provide (prefix-out circomlib: (all-defined-out)))

(define (XOR context)
    (define-symbolic* a integer?)
    (define-symbolic* b integer?)
    (define-symbolic* out integer?)

    (assert 
        (equal? 
            out 
            (- (+ a b) (* 2 a b))
        )
    )

    (define env (make-hash))
    (hash-set! env (string-append context ".a") a)
    (hash-set! env (string-append context ".b") b)
    (hash-set! env (string-append context ".out") out)
    env
)

(define (AND context)
    (define-symbolic* a integer?)
    (define-symbolic* b integer?)
    (define-symbolic* out integer?)

    (assert (equal? out (* a b)))

    (define env (make-hash))
    (hash-set! env (string-append context ".a") a)
    (hash-set! env (string-append context ".b") b)
    (hash-set! env (string-append context ".out") out)
    env
)

(define (OR context)
    (define-symbolic* a integer?)
    (define-symbolic* b integer?)
    (define-symbolic* out integer?)

    (assert 
        (equal? 
            out 
            (- (+ a b) (* a b))
        )
    )

    (define env (make-hash))
    (hash-set! env (string-append context ".a") a)
    (hash-set! env (string-append context ".b") b)
    (hash-set! env (string-append context ".out") out)
    env
)

(define (NOT context)
    (define-symbolic* in integer?)
    (define-symbolic* out integer?)

    (assert 
        (equal? 
            out 
            (- (+ 1 in) (* 2 in))
        )
    )

    (define env (make-hash))
    (hash-set! env (string-append context ".in") in)
    (hash-set! env (string-append context ".out") out)
    env
)

(define (NAND context)
    (define-symbolic* a integer?)
    (define-symbolic* b integer?)
    (define-symbolic* out integer?)

    (assert 
        (equal? 
            out 
            (- 1 (* a b))
        )
    )

    (define env (make-hash))
    (hash-set! env (string-append context ".a") a)
    (hash-set! env (string-append context ".b") b)
    (hash-set! env (string-append context ".out") out)
    env
)

(define (NOR context)
    (define-symbolic* a integer?)
    (define-symbolic* b integer?)
    (define-symbolic* out integer?)

    (assert 
        (equal? 
            out 
            (- (+ (* a b) 1) a b)
        )
    )

    (define env (make-hash))
    (hash-set! env (string-append context ".a") a)
    (hash-set! env (string-append context ".b") b)
    (hash-set! env (string-append context ".out") out)
    env
)

(define (MultiAND context n)
    (define (new-symbolic-ein)
        (define-symbolic* ein integer?)
        ein
    )

    (define in (for/list ([i n]) (new-symbolic-ein)))
    (define-symbolic* out integer?)

    (cond 
        [(equal? 1 n)
            (assert (equal? out (list-ref in 0)))

            (define env (make-hash))
            (for ([i (range n)])
                (hash-set! env (string-append context ".in[" (number->string i) "]") (list-ref in i))
            )
            (hash-set! env (string-append context ".out") out)
            env
        ]
        [(equal? 2 n)
            (define env1 (AND "and1"))
            (assert (equal? (hash-ref env1 "and1.a") (list-ref in 0)))
            (assert (equal? (hash-ref env1 "and1.b") (list-ref in 1)))
            (assert (equal? out (hash-ref env1 "and1.out")))

            (define env (make-hash))
            (for ([i (range n)])
                (hash-set! env (string-append context ".in[" (number->string i) "]") (list-ref in i))
            )
            (hash-set! env (string-append context ".out") out)
            ; additional witness
            (hash-set! env (string-append context ".and1.out") (hash-ref env1 "and1.out"))
            (hash-set! env (string-append context ".and1.a") (hash-ref env1 "and1.a"))
            (hash-set! env (string-append context ".and1.b") (hash-ref env1 "and1.b"))
            env
        ]
        [else
            (define env2 (AND "and2"))
            (define n1 (quotient n 2))
            (define n2 (- n (quotient n 2)))
            (define env3 (MultiAND "ands[0]" n1))
            (define env4 (MultiAND "ands[1]" n2))
            (for ([i (range n1)])
                (assert (equal? 
                    (hash-ref env3 (string-append "ands[0].in[" (number->string i) "]"))
                    (list-ref in i)
                ))
            )
            (for ([i (range n2)])
                (assert (equal?
                    (hash-ref env4 (string-append "ands[1].in[" (number->string i) "]"))
                ))
            )
            (assert (equal? 
                (hash-ref env2 "and2.a")
                (hash-ref env3 "ands[0].out")
            ))
            (assert (equal? 
                (hash-ref env2 "and2.b")
                (hash-ref env4 "ands[1].out")
            ))
            (assert (equal? out (hash-ref env2 "and2.out")))

            (define env (make-hash))
            (for ([i (range n)])
                (hash-set! env (string-append context ".in[" (number->string i) "]") (list-ref in i))
            )
            (hash-set! env (string-append context ".out") out)
            ; additional witness
            ; (fixme) what should appear here? should ands[0].a appear here (it's not appearing above)?
            env
        ]
    )
)