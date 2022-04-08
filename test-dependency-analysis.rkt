#lang rosette
(require "./picus/utils.rkt")
(require "./picus/r1cs.rkt")
(require "./picus/r1cs-interpreter.rkt")
;(define r0 (read-r1cs "./examples/test0.r1cs"))
;(define r0 (read-r1cs "./examples/bigmod_5_2.r1cs"))
;(define r0 (read-r1cs "./examples/bigmod_10_2.r1cs"))
(define r0 (read-r1cs "./examples/bigmod_86_3.r1cs"))
;(define r0 (read-r1cs "./examples/bigmult_86_3.r1cs"))

; restrict reasoning precision
; (current-bitwidth 8) ; fast
; (current-bitwidth 16) ; kind of instant
(current-bitwidth 32) ; hmm...
; (current-bitwidth 64) ; hmm...

(define nwires (get-nwires r0))
(printf "# number of wires: ~a\n" nwires)
(printf "# number of constraints: ~a\n" (get-mconstraints r0))
(printf "# field size (how many bytes): ~a\n" (get-field-size r0))

(define constraints (get-constraints r0))

(define dep (for/list ([cnst constraints])
  ; get block
  (define curr-block-a (constraint-a cnst))
  (define curr-block-b (constraint-b cnst))
  (define curr-block-c (constraint-c cnst))
  (define wids-a (constraint-block-wids curr-block-a))
  (define wids-b (constraint-block-wids curr-block-b))
  (define wids-c (constraint-block-wids curr-block-c))
  (append wids-a wids-b wids-c)
))
