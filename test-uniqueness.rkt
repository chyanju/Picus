#lang rosette
(require json)
(require rosette/solver/smt/z3)
(current-solver (z3 #:logic 'QF_NIA))
(printf "# using solver: ~a\n" (current-solver))
(output-smt #t)

(require "./picus/tokamak.rkt")
(require "./picus/utils.rkt")
(require "./picus/config.rkt")
(require "./picus/r1cs.rkt")
(require "./picus/r1cs-int-interpreter.rkt")

; parse command line arguments
(define arg-r1cs null)
(define arg-range null)
(command-line
  #:once-each
  [("--r1cs") p-r1cs "path to target r1cs"
    (begin
      (set! arg-r1cs p-r1cs)
      (printf "# r1cs file: ~a\n" arg-r1cs)
      (when (! (string-suffix? arg-r1cs ".r1cs"))
        (printf "# error: file need to be *.r1cs\n")
        (exit 0)
      )
    )
  ]
  #:once-any
  [("--range") "enable range analysis"
    (begin
      (set! arg-range (string-replace arg-r1cs ".r1cs" ".range.json"))
      (printf "# range file: ~a\n" arg-range)
    )
  ]
)
(when (null? arg-r1cs) (tokamak:exit "r1cs should not be null."))

(define r0 (read-r1cs arg-r1cs))
(define j0 (if (null? arg-range)
  null
  (string->jsexpr (file->string arg-range) #:null null)
))

; restrict reasoning precision, not applicable on bv
; (current-bitwidth 4) ; hmm...

(define nwires (get-nwires r0))
(printf "# number of wires: ~a (+1)\n" nwires)
(printf "# number of constraints: ~a\n" (get-mconstraints r0))
(printf "# field size (how many bytes): ~a\n" (get-field-size r0))
; (printf "# number of constraints: ~a\n" (length (get-constraints r0)))

(printf "# interpreting original r1cs...\n")
(define-values (xlist sconstraints) (interpret-r1cs r0 null)) ; interpret the constraint system
(define input-list (r1cs-inputs r0))
(define output-list (r1cs-outputs r0))
(printf "# inputs: ~a.\n" input-list)
(printf "# outputs: ~a.\n" output-list)
(printf "# xlist: ~a.\n" xlist)

; uniqueness: for all given inputs, the valuations of all outputs should be unique
; that is, inputs are shared
(define (next-symbolic-integer-alternative)
  (define-symbolic* y integer?)
  (assert (&&
    (>= y 0)
    (< y config:p)
  ))
  y
)
; fix inputs, create alternative outputs
; (note) need nwires+1 to account for 1st input

; =======================================
; output verification (weak verification)
; clara fixed version
;   |- create alternative variables for all non-input variables
;   |- but restrict output variables as weak verification states
(define xlist0 (for/list ([i (range (+ 1 nwires))])
  (if (not (contains? input-list i)) (next-symbolic-integer-alternative) (list-ref xlist i))))
(when (! (null? j0))
  ; range support: see if a stricter range should be applied or not
  (for ([i (range (+ 1 nwires))])
    (let ([rg (list-ref j0 i)][vv (list-ref xlist i)][vv0 (list-ref xlist0 i)])
      (when (! (null? rg))
        ; has new range
        (assert (&&
          (<= (list-ref rg 0) vv)
          (<= vv (list-ref rg 1))
        ))
        (assert (&&
          (<= (list-ref rg 0) vv0)
          (<= vv0 (list-ref rg 1))
        ))
      )
    )
  )
)
(printf "# xlist0: ~a.\n" xlist0)
; then interpret again
(printf "# interpreting alternative r1cs...\n")
(define-values (_ sconstraints0) (interpret-r1cs r0 xlist0))
; existence of different valuation of outputs
; (note) we are using || later, so we need #f for all matching cases
(define dconstraints (for/list ([i (range (+ 1 nwires))])
  (if (contains? output-list i) (! (= (list-ref xlist i) (list-ref xlist0 i))) #f)))
; =======================================

; (printf "# constraints are:\n~a\n~a\n~a\n" sconstraints sconstraints0 dconstraints)
; (printf "# ========== sconstraints ========== #\n")
; (for ([p sconstraints]) (printf "~a\n" p))
; (printf "# ========== sconstraints0 ========== #\n")
; (for ([p sconstraints0]) (printf "~a\n" p))
; (printf "# ========== dconstraints ========== #\n")
; (for ([p dconstraints]) (printf "~a\n" p))

; final query
(printf "# solving uniqueness...\n")
(define uniqueness-query (&& (apply && sconstraints) (apply && sconstraints0) (apply || dconstraints)))

; solve
(error-print-width 1000000)
(solve (assert uniqueness-query))