#lang racket
(require
  (prefix-in tokamak: "./picus/tokamak.rkt")
  (prefix-in utils: "./picus/utils.rkt")
  (prefix-in r1cs: "./picus/r1cs/r1cs-grammar.rkt")
)

; parse command line arguments
(define arg-r1cs null)
(command-line
  #:once-any
  [("--r1cs") p-r1cs "path to target r1cs"
    (begin
      (printf "# r1cs file: ~a\n" p-r1cs)
      (set! arg-r1cs p-r1cs)
    )
  ]
)
(when (null? arg-r1cs) (tokamak:exit "r1cs should not be null."))

(define r0 (r1cs:read-r1cs arg-r1cs))
(define t0 (r1cs:get-mconstraints r0))
(define inputs0 (r1cs:r1cs-inputs r0))
(define outputs0 (r1cs:r1cs-outputs r0))
(for ([i (range t0)]) (printf "~a\n" (r1cs:r1cs->string r0 i)))
(printf "# total constraints: ~a.\n" t0)
(printf "# total number of wires: ~a.\n" (r1cs:get-nwires r0))
(printf "# inputs: ~a (total: ~a).\n" inputs0 (length inputs0))
(printf "# outputs: ~a (total: ~a).\n" outputs0 (length outputs0))