#lang racket
(require "./picus/tokamak.rkt")
(require "./picus/utils.rkt")
(require "./picus/r1cs.rkt")

; (define r0 (read-r1cs "./examples/test2.r1cs"))
(define r0 (read-r1cs "./benchmarks/ecne/MultiAND@gates.r1cs"))

(define t0 (get-mconstraints r0))
(define inputs0 (r1cs-inputs r0))
(define outputs0 (r1cs-outputs r0))
(for ([i (range t0)]) (printf "~a\n" (r1cs->string r0 i)))
(printf "# total constraints: ~a.\n" t0)
(printf "# total number of wires: ~a\n" (get-nwires r0))
(printf "# inputs: ~a.\n" inputs0)
(printf "# outputs: ~a.\n" outputs0)