#lang rosette
(require racket/engine)
(require json rosette/solver/smt/z3
  (prefix-in tokamak: "./picus/tokamak.rkt")
  (prefix-in utils: "./picus/utils.rkt")
  (prefix-in config: "./picus/config.rkt")
  (prefix-in r1cs: "./picus/r1cs.rkt")
  (prefix-in rint: "./picus/r1cs-interpreter.rkt")
)
(current-solver (z3 #:logic 'QF_NIA))
(printf "# using solver: ~a\n" (current-solver))
(output-smt #t)

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

(define r0 (r1cs:read-r1cs arg-r1cs))
(define j0 (if (null? arg-range)
  null
  (string->jsexpr (file->string arg-range) #:null null)
))

(define nwires (r1cs:get-nwires r0))
(printf "# number of wires: ~a (+1)\n" nwires)
(printf "# number of constraints: ~a\n" (r1cs:get-mconstraints r0))
(printf "# field size (how many bytes): ~a\n" (r1cs:get-field-size r0))

(printf "# interpreting original r1cs...\n")
(define-values (xlist sconstraints) (rint:interpret-r1cs r0 null)) ; interpret the constraint system
(define input-list (r1cs:r1cs-inputs r0))
(define output-list (r1cs:r1cs-outputs r0))
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

(define known-list (for/list ([i input-list]) i))
(define unknown-list (filter
  (lambda (x) (! (utils:contains? input-list x)))
  (for/list ([i (range (+ 1 nwires))]) i)
))
(printf "# initial known-list is: ~a\n" known-list) ; known to be unique
(printf "# initial unknown-list is: ~a\n" unknown-list)

(define xlist0 (for/list ([i (range (+ 1 nwires))])
  (if (not (utils:contains? input-list i)) (next-symbolic-integer-alternative) (list-ref xlist i))))
(printf "# xlist0: ~a.\n" xlist0)
; then interpret again
(printf "# interpreting alternative r1cs...\n")
(define-values (_ sconstraints0) (rint:interpret-r1cs r0 xlist0))

(define (inc-solve kl ind)
  ; existence of different valuation of outputs
  ; (note) we are using || later, so we need #f for all matching cases
  (define dconstraints (for/list ([i (range (+ 1 nwires))])
    (if (utils:contains? kl i) ; no need to equate inputs because they are by construction equal
      (= (list-ref xlist i) (list-ref xlist0 i)) ; known to be unique, so equal
      #t ; don't know, so no restrictions
      ; (note) because we are applying &&, so this should be #t, not #f
    )
  ))

  ; target constraints
  (define iconstraints (list
    (! (= (list-ref xlist ind) (list-ref xlist0 ind)))
  ))

  ; query
  (define uniqueness-query (&&
    (apply && sconstraints)
    (apply && sconstraints0)
    (apply && dconstraints)
    (apply && iconstraints)
  ))

  ; solve
  (printf "# solving uniqueness for ind=~a...\n" ind)
  (printf "  # dconstraints: ~a\n" dconstraints)
  (printf "  # iconstraints: ~a\n" iconstraints)
  (define sol (solve (assert uniqueness-query)))
  sol
)

(define (loop-solve kl ul)
  (define new-kl (for/list ([v kl]) v))
  (define new-ul (list ))
  (printf "# start looping...\n")
  (printf "------------------\n")
  (for ([ind ul])
    (printf "# curr kl is: ~a\n" new-kl)
    (define engine0 (engine (lambda (_) (inc-solve new-kl ind))))
    (define eres (engine-run 20000 engine0))
    (define sol (engine-result engine0))
    (cond
      [(unsat? sol)
        ; verified, add to kl
        (printf "  # verified.\n")
        (set! new-kl (cons ind new-kl))
      ]
      [(! eres)
        (printf "  # timeout.\n")
        (set! new-ul (cons ind new-ul))
      ]
      [else
        ; not verified, move on
        (printf "  # failed.\n")
        (set! new-ul (cons ind new-ul))
      ]
    )
  )

  (if (equal? kl new-kl)
    ; no changes, end this by returning ul
    new-ul
    ; has changes, loop again
    (loop-solve new-kl new-ul)
  )
)

(define result (loop-solve known-list unknown-list))
(printf "# raw result is: ~a\n" result)