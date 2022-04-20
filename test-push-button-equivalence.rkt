#lang rosette
(require json)
(require csv-reading)
(require "./picus/tokamak.rkt")
(require "./picus/utils.rkt")
(require "./picus/r1cs.rkt")
(require "./picus/r1cs-interpreter.rkt")
(require "./picus/circom-parser.rkt")
(require "./picus/circom-vm.rkt")

; set the example
(define json-path "./examples/test1.json")
(define r1cs-path "./examples/test1.r1cs")
(define sym-path "./examples/test1.sym")

; =======================
; load and interpret r1cs
(printf "# processing r1cs...\n")
(define circuit-r1cs (read-r1cs r1cs-path))
; print some basic r1cs info
(define nwires (get-nwires circuit-r1cs))
(printf "  # number of wires: ~a\n" nwires)
(printf "  # number of constraints: ~a\n" (get-mconstraints circuit-r1cs))
(printf "  # field size (how many bytes): ~a\n" (get-field-size circuit-r1cs))
(printf "  # number of constraints: ~a\n" (length (get-constraints circuit-r1cs)))
(define-values (xlist sconstraints) (interpret-r1cs circuit-r1cs null)) ; interpret
(define input-list (r1cs-inputs circuit-r1cs))
(define output-list (r1cs-outputs circuit-r1cs))

; ==========================
; load and interpret circuit
(printf "# processing circuit...\n")
(define circuit-json (string->jsexpr (file->string json-path)))
(define circuit-node (parse-circom-json circuit-json))
(define vm (new circom-vm%))
(send vm deploy circuit-node) ; deploy
(define circuit-root (get-field circom-root vm))
(send vm interpret circuit-root) ; interpret
; print some basic circuit info
(define input-book (get-field input-book vm))
(define output-book (get-field output-book vm))
(printf "  # vc: ~a\n" (vc))
(printf "  # inputs: ~a\n" input-book)
(printf "  # outputs: ~a\n" output-book)
; combine two books
(define io-book (make-hash (append (hash->list input-book) (hash->list output-book))))

; =====================
; construct symbol link
(printf "# connecting symbols...\n")
(define raw-sym (csv->list (file->string sym-path)))
; use 1st column
(define sym2wid (make-hash (for/list ([p raw-sym]) (cons (car (reverse p)) (string->number (car p))))))
; connect symbolic variables
(for ([k (hash-keys sym2wid)])
  (define w0 (hash-ref sym2wid k))
  (define var-left (list-ref xlist w0))
  (define var-right (hash-ref io-book k))
  ; (printf "  # var-left: ~a\n" var-left)
  (cond
    [(contains? input-list w0)
      ; only bind inputs
      (printf "  # [input, bind] key=~a, r1cs=~a, circom=~a\n" k var-left var-right)
      ; binding constraint
      (assert (equal? var-left var-right))
    ]
    [(contains? output-list w0)
      ; outputs or others are not bound
      (printf "  # [output, detected] key=~a, r1cs=~a, circom=~a\n" k var-left var-right)
      ; negation constraint
      (assert (not (equal? var-left var-right)))
    ]
    [else
     (printf "  # [nothing] key=~a, r1cs=~a, circom=~a\n" k var-left var-right)
    ]
  )
)

(printf "# solving equivalence...\n")
(solve (assert (apply && sconstraints)))
