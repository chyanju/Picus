#lang racket
(require "./picus/tokamak.rkt")
(require "./picus/utils.rkt")
(require "./picus/r1cs.rkt")

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

(define r0 (read-r1cs arg-r1cs))

(define t0 (get-mconstraints r0))
(define inputs0 (r1cs-inputs r0))
(define outputs0 (r1cs-outputs r0))
(for ([i (range t0)]) (printf "~a\n" (r1cs->string r0 i)))
(printf "# total constraints: ~a.\n" t0)
(printf "# total number of wires: ~a (+1)\n" (get-nwires r0))
(printf "# inputs: ~a.\n" inputs0)
(printf "# outputs: ~a.\n" outputs0)