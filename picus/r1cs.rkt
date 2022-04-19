#lang racket
(require "./tokamak.rkt")
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
(struct r1cs (magic version nsec header constraint w2l inputs outputs) #:mutable #:transparent #:reflection-name 'r1cs)
    (struct header-section (field-size prime-number nwires npubout npubin nprvin nlabels mconstraints) #:mutable #:transparent #:reflection-name 'header-section)
    (struct constraint-section (constraints) #:mutable #:transparent #:reflection-name 'constraint-section)
        (struct constraint (a b c) #:mutable #:transparent #:reflection-name 'constraint) ; a, b and c are constraint-blocks
            (struct constraint-block (nnz wids factors) #:mutable #:transparent #:reflection-name 'constraint-block)
    (struct w2l-section (v) #:mutable #:transparent #:reflection-name 'w2l-section)

; quick functions
(define (get-mconstraints arg-r1cs) (header-section-mconstraints (r1cs-header arg-r1cs)))
(define (get-nwires arg-r1cs) (header-section-nwires (r1cs-header arg-r1cs)))
(define (get-npubout arg-r1cs) (header-section-npubout (r1cs-header arg-r1cs)))
(define (get-npubin arg-r1cs) (header-section-npubin (r1cs-header arg-r1cs)))
(define (get-nprvin arg-r1cs) (header-section-nprvin (r1cs-header arg-r1cs)))
(define (get-nlabels arg-r1cs) (header-section-nlabels (r1cs-header arg-r1cs)))
(define (get-constraints arg-r1cs) (constraint-section-constraints (r1cs-constraint arg-r1cs)))
(define (get-field-size arg-r1cs) (header-section-field-size (r1cs-header arg-r1cs)))

(define (extract-header-section arg-raw)
    (define field-size (bytes->number (subbytes arg-raw 0 4))) ; field size in bytes
    (when (not (zero? (remainder field-size 8)))
        (tokamak:exit "# [exception][extract-header-section] field size should be a multiple of 8, got: ~a.") field-size)
    ; (fixme) is the prime number in little endian?
    ; (fixme) it's still in bytes type
    (define prime-number (subbytes arg-raw 4 (+ 4 field-size))) ; prime number
    (define nwires (bytes->number (subbytes arg-raw (+ 4 field-size) (+ 8 field-size))))
    (define npubout (bytes->number (subbytes arg-raw (+ 8 field-size) (+ 12 field-size))))
    (define npubin (bytes->number (subbytes arg-raw (+ 12 field-size) (+ 16 field-size))))
    (define nprvin (bytes->number (subbytes arg-raw (+ 16 field-size) (+ 20 field-size))))
    (define nlabels (bytes->number (subbytes arg-raw (+ 20 field-size) (+ 28 field-size))))
    (define mconstraints (bytes->number (subbytes arg-raw (+ 28 field-size) (+ 32 field-size))))
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
        (tokamak:exit 
            (format "# [exception][extract-constraint-section] number of constraints is not equal to mconstraints, got: ~a and ~a." (length clist) arg-m)))
    ; return
    (constraint-section clist)
)

(define (extract-w2l-section arg-raw)
    ; every label id takes 8 bytes
    (when (not (zero? (remainder (bytes-length arg-raw) 8)))
        (tokamak:exit 
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

; count the total number of sections
; arg-raw: bytes of sections without meta zone
(define (count-sections arg-raw)
    (cond 
        [(zero? (bytes-length arg-raw)) 0]
        [else
            (define section0-type (bytes->number (subbytes arg-raw 0 4)))
            (define section0-size (bytes->number (subbytes arg-raw 4 12)))
            (define bs0 (+ 12 section0-size)) ; next section start position
            (+ 1 (count-sections (subbytes arg-raw bs0)))
        ]
    )
)

(define (extract-section-types arg-raw)
    (cond 
        [(zero? (bytes-length arg-raw)) (list)]
        [else
            (define section0-type (bytes->number (subbytes arg-raw 0 4)))
            (define section0-size (bytes->number (subbytes arg-raw 4 12)))
            (define bs0 (+ 12 section0-size)) ; next section start position
            (cons section0-type (extract-section-types (subbytes arg-raw bs0)))
        ]
    )
)

; remove sections with unrecognized section type
; currently the spec only mentions types of 1, 2 and 3
(define (filter-sections arg-raw)
    (define accepted-types (list 1 2 3))
    (cond
        [(zero? (bytes-length arg-raw)) (bytes)]
        [else
            (define section0-type (bytes->number (subbytes arg-raw 0 4)))
            (define section0-size (bytes->number (subbytes arg-raw 4 12)))
            (define bs0 (+ 12 section0-size)) ; next section start position
            (if (contains? accepted-types section0-type)
                ; yes, include this section
                (bytes-append (subbytes arg-raw 0 bs0) (filter-sections (subbytes arg-raw bs0)))
                ; no, drop this section
                (filter-sections (subbytes arg-raw bs0))
            )
        ]
    )
)

; find section start pos and size of designated section type
; arg-raw: bytes of sections without meta zone
(define (find-section arg-raw arg-type)
    (cond 
        [(zero? (bytes-length arg-raw))
            (tokamak:exit (format "# [exception][find-section-pos] cannot find position of section given type: ~a." arg-type))
        ]
        [else
            (define section0-type (bytes->number (subbytes arg-raw 0 4)))
            (define section0-size (bytes->number (subbytes arg-raw 4 12)))
            (cond
                [(equal? arg-type section0-type) (values 0 section0-size)] ; found
                [else
                    (define offset (+ 12 section0-size))
                    (define-values (pos0 size0) (find-section (subbytes arg-raw offset) arg-type))
                    (values (+ offset pos0) size0)
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
        (tokamak:exit (format "# [exception][read-r1cs] magic number is incorrect, got: ~a." magic-number)))

    (define version (bytes->number (subbytes raw 4 8)))
    (when (not (equal? 1 version ))
        (tokamak:exit (format "# [exception][read-r1cs] version is not supported, got: ~a." version)))

    (define nsec (bytes->number (subbytes raw 8 12)))

    (define raw-sections (subbytes raw 12)) ; 12=4+4+4, remove the meta zone
    (define fraw-sections (filter-sections raw-sections)) ; remove sections with undefined section types
    (when (not (equal? 3 (count-sections fraw-sections)))
        (tokamak:exit (format "# [exception][read-r1cs] r1cs needs to contain 3 sections, got: ~a." (count-sections fraw-sections))))


    ; find aand process header section, +12 to skip section meta zone
    (define-values (hs-pos hs-size) (find-section fraw-sections 1))
    (define hs0 (extract-header-section (subbytes fraw-sections (+ 12 hs-pos) (+ 12 hs-pos hs-size))))
    (define fs0 (header-section-field-size hs0))
    (define m0 (header-section-mconstraints hs0))

    ; find and process constraint section, +12 to skip section meta zone
    (define-values (cs-pos cs-size) (find-section fraw-sections 2))
    (define cs0 (extract-constraint-section 
        (subbytes fraw-sections (+ 12 cs-pos) (+ 12 cs-pos cs-size))
        fs0 m0
    ))

    ; find and process w2l section, +12 to skip section meta zone
    (define-values (ws-pos ws-size) (find-section fraw-sections 3))
    (define ws0 (extract-w2l-section (subbytes fraw-sections (+ 12 ws-pos) (+ 12 ws-pos ws-size))))

    ; compute the list of input variables (aka `knowns` in Ecne) and output variables (aka `outputs` in Ecne)
    (define istart (+ 2 (header-section-npubout hs0))) ; inclusive
    (define iend (+ 1 (header-section-npubout hs0) (header-section-npubin hs0) (header-section-nprvin hs0))) ; inclusive
    (define input-list-ecne (cons 1 
        (for/list ([i (range istart (+ 1 iend))]) i)
    ))
    (define input-list (for/list ([i input-list-ecne]) (- i 1))) ; translate back to 0-based index

    (define ostart 2) ; inclusive
    (define oend (+ 1 (header-section-npubout hs0))) ; inclusive
    (define output-list-ecne (for/list ([i (range ostart (+ 1 oend))]) i))
    (define output-list (for/list ([i output-list-ecne]) (- i 1))) ; translate back to 0-based index

    ; return
    (r1cs magic-number version nsec hs0 cs0 ws0 input-list output-list)
)

; returns a human readable string of one specified equation
; original form is A*B-C=0, but we do A*B=C
(define (r1cs->string arg-r1cs arg-id)
    (define w2l (w2l-section-v (r1cs-w2l arg-r1cs))) ; w2l mapping, a list
    (define clist (constraint-section-constraints (r1cs-constraint arg-r1cs))) ; a list of constraints

    (define example-constraint (list-ref clist arg-id)) ; a constraint
    (define example-block-a (constraint-a example-constraint))
    (define example-block-b (constraint-b example-constraint))
    (define example-block-c (constraint-c example-constraint))

    ; process block a
    (define nnz-a (constraint-block-nnz example-block-a))
    (define wids-a (constraint-block-wids example-block-a))
    (define factors-a (constraint-block-factors example-block-a))
    (define str-a (string-join
        (for/list ([w0 wids-a] [f0 factors-a])
            (string-join (list
                "("
                (number->string f0)
                " * x"
                (number->string w0)
                ")"
            ) "")
        )
        " + "
    ))

    ; process block b
    (define nnz-b (constraint-block-nnz example-block-b))
    (define wids-b (constraint-block-wids example-block-b))
    (define factors-b (constraint-block-factors example-block-b))
    (define str-b (string-join
        (for/list ([w0 wids-b] [f0 factors-b])
            (string-join (list
                "("
                (number->string f0)
                " * x"
                (number->string w0)
                ")"
            ) "")
        )
        " + "
    ))

    ; process block c
    (define nnz-c (constraint-block-nnz example-block-c))
    (define wids-c (constraint-block-wids example-block-c))
    (define factors-c (constraint-block-factors example-block-c))
    (define str-c (string-join
        (for/list ([w0 wids-c] [f0 factors-c])
            (string-join (list
                "("
                (number->string f0)
                " * x"
                (number->string w0)
                ")"
            ) "")
        )
        " + "
    ))

    (string-join 
        (list 
            "( "
            (if (zero? (string-length str-a)) "0" str-a)
            " ) * ( "
            (if (zero? (string-length str-b)) "0" str-b)
            " ) = "
            (if (zero? (string-length str-c)) "0" str-c)
        ) 
    "")

)