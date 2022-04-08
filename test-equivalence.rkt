#lang rosette
(require csv-reading)
(require "./picus/utils.rkt")
(require "./picus/r1cs.rkt")
(require "./picus/r1cs-interpreter.rkt")
(require "./picus/circomlib/gates.rkt")

; restrict reasoning precision
; (current-bitwidth 16) ; hmm...

; you need to compile the circuit first
; run: circom "./AND@gates.circom" --r1cs --sym
(define sym-path "./examples/ecne_circomlib_tests/OR@gates.sym")
(define r1cs-path "./examples/ecne_circomlib_tests/OR@gates.r1cs")
(define (circom-program)
  (circomlib:OR "main")
  ; (circomlib:MultiAND "main" 2)
)

; construct symbol link
(define raw-sym (csv->list (file->string sym-path)))
; use 2nd column
; (define sym2wid (make-hash (for/list ([p raw-sym]) (cons (car (reverse p)) (string->number (car (cdr p)))))))
; use 1st column
(define sym2wid (make-hash (for/list ([p raw-sym]) (cons (car (reverse p)) (string->number (car p))))))

; load r1cs
(define r0 (read-r1cs r1cs-path))
(printf "# number of wires: ~a\n" (get-nwires r0))
(printf "# number of constraints: ~a\n" (get-mconstraints r0))
(printf "# field size (how many bytes): ~a\n" (get-field-size r0))
; interpret r1cs
(define-values (xlist sconstraints) (interpret-r1cs r0 null)) ; interpret the constraint system
(define input-list (r1cs-inputs r0))
(define output-list (r1cs-outputs r0))

; symbolic compilation of the curcuit
(define env0 (circom-program))

; connect symbolic variables from env0 with sym file
(for ([k (hash-keys sym2wid)])
  (define w0 (hash-ref sym2wid k))
  (define var-left (list-ref xlist w0))
  (define var-right (hash-ref env0 k))
  ; (define var-left (if (< w0 0)
  ;   ; wid<0, not the outer layer, probably intermediate
  ;   -1
  ;   ; wid>=0, valid
  ;   (list-ref xlist w0)
  ; ))
  ; (define var-right (if (< w0 0)
  ;    -1
  ;    (hash-ref env0 k)
  ; ))
  (printf "# var-left: ~a\n" var-left)
  (cond
    [(contains? input-list w0)
      ; only bind inputs
      (printf "# [bind] input ~a with ~a (~a)\n" var-left var-right k)
      ; binding constraint
      (assert (equal? var-left var-right))
    ]
    [(contains? output-list w0)
      ; outputs or others are not bound
      (printf "# [detected] output ~a with ~a (~a)\n" var-left var-right k)
      ; negation constraint
      (assert (not (equal? var-left var-right)))
    ]
    [else
     (printf "# nothing: ~a with ~a (~a)\n" var-left var-right k)
    ]
  )
)

(printf "# solving equivalence...\n")
(solve (assert (apply && sconstraints)))



