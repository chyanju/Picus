#lang rosette
(require rosette/solver/smt/boolector)
(define use-boolector #f) ; use boolector or not?
(when (and use-boolector (boolector-available?))
  ; (current-solver (boolector #:logic 'QF_BV))
  (current-solver (boolector))
)
(printf "# using solver: ~a\n" (current-solver))
(output-smt #t)

(require json)
(require csv-reading)
(require "./picus/tokamak.rkt")
(require "./picus/utils.rkt")
(require "./picus/r1cs.rkt")
(require "./picus/r1cs-interpreter.rkt")
(require "./picus/circom-parser.rkt")
(require "./picus/circom-vm.rkt")

; set the example
; (define cname "test7")
(define cname "BinSum@binsum")
;(define json-path (format "./examples/~a.json" cname))
;(define r1cs-path (format "./examples/~a.r1cs" cname))
;(define sym-path (format "./examples/~a.sym" cname))
(define json-path (format "./benchmarks/ecne/~a.json" cname))
(define r1cs-path (format "./benchmarks/ecne/~a.r1cs" cname))
(define sym-path (format "./benchmarks/ecne/~a.sym" cname))

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
; if you include, then the json will have multiple lines
(define circuit-strings (reverse (string-split (file->string json-path) "\n"))) ; (note) reverse!
(define circuit-jsons (for/list ([s circuit-strings]) (string->jsexpr s)))
(define vm (new circom-vm%))
; interpret one by one
(for ([i (range (length circuit-jsons))])
  (define circuit-json (list-ref circuit-jsons i))
  (define is-init (equal? 0 i)) ; do you need to initialize all states or not
  
  (define circuit-node (parse-circom-json circuit-json))
  (send vm deploy circuit-node is-init) ; deploy
  (printf "  # parsing piece ~a...\n" i)
  (define circuit-root (get-field circom-root vm))
  (printf "  # interpreting piece ~a...\n" i)
  (send vm interpret circuit-root is-init) ; interpret
)
; print some basic circuit info
(define input-book (get-field input-book vm))
(define output-book (get-field output-book vm))
(define intermediate-book (get-field intermediate-book vm))
(printf "  # vc: ~a\n" (vc))
(printf "  # inputs: ~a\n" input-book)
(printf "  # outputs: ~a\n" output-book)
(printf "  # intermediates: ~a\n" intermediate-book)
; combine two books
(define io-book (make-hash (append (hash->list input-book) (hash->list output-book) (hash->list intermediate-book))))

; =====================
; construct symbol link
(printf "# connecting symbols...\n")
(define raw-sym (csv->list (file->string sym-path)))
; use 1st column
; (define sym2wid (make-hash (for/list ([p raw-sym]) (cons (car (reverse p)) (string->number (car p))))))
; use 2nd column
(define sym2wid (make-hash (for/list ([p raw-sym]) (cons (car (reverse p)) (string->number (car (cdr p)))))))
; connect symbolic variables
(for ([k (hash-keys sym2wid)])
  (define w0 (hash-ref sym2wid k))
  (cond
    [(< w0 0) (printf "  # [intermediate, NOT in r1cs] key=~a, circom=~a\n" k (hash-ref io-book k))]
    [else
      (define var-left (list-ref xlist w0))
      (define var-right (hash-ref io-book k))
      ; (printf "  # var-left: ~a\n" var-left)
      (cond
        [(contains? input-list w0)
          ; only bind inputs
          (printf "  # [input, eq] key=~a, r1cs=~a, circom=~a\n" k var-left var-right)
          ; binding constraint
          (assert (bveq var-left var-right))
        ]
        [(contains? output-list w0)
          ; outputs are not bound, but go with negation constaint
          (printf "  # [output, neq] key=~a, r1cs=~a, circom=~a\n" k var-left var-right)
          ; negation constraint
          (assert (not (bveq var-left var-right)))
        ]
        [else
          (if (hash-has-key? intermediate-book k)
            ; intermediates are not bound, and we have no constraints on them
            (printf "  # [intermediate, in r1cs] key=~a, r1cs=~a, circom=~a\n" k var-left var-right)
            (printf "  # ---->[something is wrong] key=~a, r1cs=~a, circom=~a\n" k var-left var-right)
          )
        ]
      )
    ]
  )
)

(printf "# solving equivalence...\n")
(error-print-width 1000000)
(define model (solve (assert (apply && sconstraints))))
(if (sat? model)
    (printf "  # found a counterexample:\n~a\n" model)
    (printf "  # no counterexample: verified\n")
)
