#lang racket
(require "./utils.rkt")
(provide (all-defined-out))

; reference: https://github.com/franklynwang/EcneProject/blob/master/src/R1CSConstraintSolver.jl#L10
(define big-prime 21888242871839275222246405745257275088548364400416034343698204186575808495617)
; reference: https://github.com/franklynwang/EcneProject/blob/master/src/R1CSConstraintSolver.jl#L13
; Galois Field
(define (F x)
    ; yes, behaviorly you should use remainder
    (remainder x big-prime)
)

; reference: https://github.com/franklynwang/EcneProject/blob/master/src/R1CSConstraintSolver.jl#L414
(define (fix-number x)
    (if (> x 21888242871839275222246405745257275088548363400416034343698204186575808495517)
        (- x 21888242871839275222246405745257275088548364400416034343698204186575808495617)
        x
    )
)

; r1cs structs
(struct header-section (field-size prime-number nwires npubout npubin nprvin nlabels mconstraints) #:mutable #:transparent #:reflection-name 'header-section)
(struct constraint-block (nnz wids factors) #:mutable #:transparent #:reflection-name 'constraint-block)
(struct constraint (a b c) #:mutable #:transparent #:reflection-name 'constraint)
(struct constraint-section (constraints) #:mutable #:transparent #:reflection-name 'constraint-section)
(struct w2l-section (v) #:mutable #:transparent #:reflection-name 'w2l-section)
(struct r1cs (magic version nsec sections) #:mutable #:transparent #:reflection-name 'r1cs)

(define (extract-header-section arg-raw)
    (define field-size (bytes->number (subbytes arg-raw 0 4))) ; field size in bytes
    (when (not (zero? (remainder field-size 8)))
        (println-and-exit "# [exception][extract-header-section] field size should be a multiple of 8, got: ~a.") field-size)
    ; (fixme) is the prime number in little endian?
    ; (fixme) it's still in bytes type
    (define prime-number (subbytes arg-raw 4 (+ 4 field-size))) ; prime number
    (define nwires (bytes->number (subbytes arg-raw (+ 4 field-size) (+ 8 field-size))))
    (define npubout (bytes->number (subbytes arg-raw (+ 8 field-size) (+ 12 field-size))))
    (define npubin (bytes->number (subbytes arg-raw (+ 12 field-size) (+ 16 field-size))))
    (define nprvin (bytes->number (subbytes arg-raw (+ 16 field-size) (+ 20 field-size))))
    (define nlabels (bytes->number (subbytes arg-raw (+ 20 field-size) (+ 28 field-size))))
    (define mconstraints (bytes->number (subbytes arg-raw (+ 28 field-size) (+ 32 field-size))))
    (printf "mconstraints: ~a\n" mconstraints)
    ; return
    (header-section field-size prime-number nwires npubout npubin nprvin nlabels mconstraints)
)

(define (extract-single-constraint arg-raw arg-fs)
    (define (extract-constraint-block arg-block arg-n)
        (define tmp-wids
            (for/list ([i arg-n])
                (define s0 (* i (+ 4 arg-fs)))
                (bytes->number (subbytes arg-block s0 (+ 4 s0)))
            )
        )
        (define tmp-factors
            (for/list ([i arg-n])
                (define s0 (+ 4 (* i (+ 4 arg-fs))))
                (fix-number (F (bytes->number (subbytes arg-block s0 (+ arg-fs s0)))))
            )
        )
        ; return
        (values tmp-wids tmp-factors)
    )

    ; block A
    (define nnz-a (bytes->number (subbytes arg-raw 0 4))) ; number of non-zero factors
    (define block-a-start 4)
    (define block-a-end (+ block-a-start (* nnz-a (+ 4 arg-fs))))
    (define block-a (subbytes arg-raw block-a-start block-a-end)) ; fetch a whole block
    (define-values (wids-a factors-a) (extract-constraint-block block-a nnz-a))

    ; block B
    (define nnz-b (bytes->number (subbytes arg-raw block-a-end (+ 4 block-a-end))))
    (define block-b-start (+ 4 block-a-end))
    (define block-b-end (+ block-b-start (* nnz-b (+ 4 arg-fs))))
    (define block-b (subbytes arg-raw block-b-start block-b-end))
    (define-values (wids-b factors-b) (extract-constraint-block block-b nnz-b))

    ; block C
    (define nnz-c (bytes->number (subbytes arg-raw block-b-end (+ 4 block-b-end))))
    (define block-c-start (+ 4 block-b-end))
    (define block-c-end (+ block-c-start (* nnz-c (+ 4 arg-fs))))
    (define block-c (subbytes arg-raw block-c-start block-c-end))
    (define-values (wids-c factors-c) (extract-constraint-block block-c nnz-c))

    (define ret0
        (constraint
            (constraint-block nnz-a wids-a factors-a)
            (constraint-block nnz-b wids-b factors-b)
            (constraint-block nnz-c wids-c factors-c)
        )
    )
    ; return
    (values block-c-end ret0)
)

(define (extract-constraint-section arg-raw arg-fs arg-m)
    (define (do-extract raw0)
        (cond 
            [(zero? (bytes-length raw0))
                (list ) ; base
            ]
            [else
                ; recursive
                (define-values (block-end cs) (extract-single-constraint raw0 arg-fs))
                ; return
                (cons cs (do-extract (subbytes raw0 block-end)))
            ]
        )
    )
    (define clist (do-extract arg-raw))
    (when (not (equal? arg-m (length clist)))
        (println-and-exit 
            (format "# [exception][extract-constraint-section] number of constraints is not equal to mconstraints, got: ~a and ~a." (length clist) arg-m)))
    ; return
    (constraint-section clist)
)

(define (extract-w2l-section arg-raw)
    ; every label id takes 8 bytes
    (when (not (zero? (remainder (bytes-length arg-raw) 8)))
        (println-and-exit 
            (format "# [exception][extract-w2l-section] bytes length should be a multiple of 8, got: ~a." (bytes-length arg-raw))))
    (define n (/ (bytes-length arg-raw) 8))
    (define map0 
        (for/list ([i n])
            (define s0 (* i 8))
            (bytes->number (subbytes arg-raw s0 (+ 8 s0)))
        )
    )
    ; return
    (w2l-section map0)
)

; sections have dependencies (e.g., constraint section requires field size and mconstraints from header section),
; this reorder the sections to respect such dependencies
(define (find-header-pos arg-raw)
    (cond 
        [(zero? (bytes-length arg-raw))
            (println-and-exit "# [exception][find-header-pos] cannot find position of header section.")
        ]
        [else
            ;recursive
            (define section0-type (bytes->number (subbytes arg-raw 0 4))) ; top section type
            (define section0-size (bytes->number (subbytes arg-raw 4 12))) ; top section size, number of bytes
            (printf "# [debug] section type: ~a, section size: ~a\n" section0-type section0-size)
            
            (cond
                [(equal? 1 section0-type) 0]
                [else
                    (define bs0 (+ 12 section0-size))
                    (+ bs0 (find-header-pos (subbytes arg-raw bs0)))
                ]
            )
        ]
    )
)

(define (extract-sections arg-raw arg-fs arg-m)
    (cond 
        [(zero? (bytes-length arg-raw))
            ; base
            (list )
        ]
        [else
            ;recursive
            (define section0-type (bytes->number (subbytes arg-raw 0 4))) ; top section type
            (define section0-size (bytes->number (subbytes arg-raw 4 12))) ; top section size, number of bytes
            
            (cond
                [(equal? 1 section0-type) 
                    (define section0 (extract-header-section (subbytes arg-raw 12 (+ 12 section0-size))))
                    (define fs0 (header-section-field-size section0))
                    (define m0 (header-section-mconstraints section0))
                    (printf "defined arg-fs: ~a, arg-m: ~a\n" fs0 m0)
                    ; recursive return
                    (cons 
                        section0 
                        (extract-sections 
                            (subbytes arg-raw (+ 12 section0-size))
                            (header-section-field-size section0) ; provide field size
                            (header-section-mconstraints section0) ; provide mconstraints
                        )
                    )
                ]
                [(equal? 2 section0-type) 
                    (printf "arg-fs: ~a, arg-m: ~a\n" arg-fs arg-m)
                    (define section0 (extract-constraint-section (subbytes arg-raw 12 (+ 12 section0-size)) arg-fs arg-m))
                    ; recursive return
                    (cons 
                        section0 
                        (extract-sections
                            (subbytes arg-raw (+ 12 section0-size))
                            arg-fs
                            arg-m
                        )
                    )
                ]
                [(equal? 3 section0-type) 
                    (define section0 (extract-w2l-section (subbytes arg-raw 12 (+ 12 section0-size))))
                    ; recursive return
                    (cons 
                        section0 
                        (extract-sections 
                            (subbytes arg-raw (+ 12 section0-size))
                            arg-fs
                            arg-m
                        )
                    )
                ]
                [else
                    ; if containing other types, they should be ignored
                    (printf "# [warning][extract-sections] section type is not supported, got: ~a, will ignore according to spec.\n" section0-type)
                    (void)
                ]
            )
        ]
    )
)


; format spec: https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md
(define (read-r1cs arg-path)
    (define raw (file->bytes arg-path))

    (define magic-number (subbytes raw 0 4)) ; should be #x72 #x31 #x63 #x72
    (when (not (equal? magic-number (bytes #x72 #x31 #x63 #x73)))
        (println-and-exit (format "# [exception][read-r1cs] magic number is incorrect, got: ~a." magic-number)))

    (define version (bytes->number (subbytes raw 4 8)))
    (when (not (equal? 1 version ))
        (println-and-exit (format "# [exception][read-r1cs] version is not supported, got: ~a." version)))

    (define nsec (bytes->number (subbytes raw 8 12)))

    (define raw-sections (subbytes raw 12)) ; 12=4+4+4
    (define raw-header-pos (find-header-pos raw-sections))
    (define raw-sections-reordered
        (bytes-append
            (subbytes raw-sections raw-header-pos)
            (subbytes raw-sections 0 raw-header-pos)
        )
    )

    (define sections (extract-sections raw-sections-reordered null null))

    (r1cs magic-number version nsec sections)
)