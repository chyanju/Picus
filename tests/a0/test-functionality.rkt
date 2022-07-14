#lang rosette
(require rosette/solver/smt/boolector)
(define use-boolector #f) ; use boolector or not?
(when (and use-boolector (boolector-available?))
  ; (current-solver (boolector #:logic 'QF_BV))
  (current-solver (boolector))
)
(printf "# using solver: ~a\n" (current-solver))
(output-smt #t)

(require json csv-reading racket/cmdline)
(require "./picus/tokamak.rkt")
(require "./picus/utils.rkt")
(require "./picus/r1cs.rkt")
(require "./picus/r1cs-interpreter.rkt")
(require "./picus/circom-parser.rkt")
(require "./picus/circom-vm.rkt")

; parse command line arguments
(define arg-cname null)
(command-line
  #:program "picus functionality test"
  #:once-any
  [("--cname") p-cname "ecne circom file name (without extension)" 
    (begin
      (printf "# using: ~a\n" p-cname)
      (set! arg-cname p-cname)
    )
  ]
)
(when (null? arg-cname) (tokamak:exit "cname should not be null."))

; set the example
;(define arg-cname "test9")
;(define json-path (format "./examples/~a.json" arg-cname))
;(define r1cs-path (format "./examples/~a.r1cs" arg-cname))
;(define sym-path (format "./examples/~a.sym" arg-cname))

; (define arg-cname "Num2BitsNeg@bitify")
(define json-path (format "./benchmarks/ecne/~a.json" arg-cname))
(define r1cs-path (format "./benchmarks/ecne/~a.r1cs" arg-cname))
(define sym-path (format "./benchmarks/ecne/~a.sym" arg-cname))

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
; (define input-book (get-field input-book vm))
; (define output-book (get-field output-book vm))
; (define intermediate-book (get-field intermediate-book vm))
; (printf "  # vc: ~a\n" (vc))
; (printf "  # inputs: ~a\n" input-book)
; (printf "  # outputs: ~a\n" output-book)
; (printf "  # intermediates: ~a\n" intermediate-book)
; combine two books
; (define io-book (make-hash (append (hash->list input-book) (hash->list output-book) (hash->list intermediate-book))))