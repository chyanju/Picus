#lang rosette
(require json csv-reading racket/cmdline
    (prefix-in tokamak: "./picus/tokamak.rkt")
    (prefix-in utils: "./picus/utils.rkt")
    (prefix-in r1cs: "./picus/r1cs.rkt")
    (prefix-in rint: "./picus/r1cs-interpreter.rkt")
    (prefix-in parser: "./picus/circom-parser.rkt")
    (prefix-in analysis: "./picus/circom-analysis.rkt")
)

; parse command line arguments
(define arg-r1cs null)
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
)
(define arg-json (string-replace arg-r1cs ".r1cs" ".json"))
(define arg-sym (string-replace arg-r1cs ".r1cs" ".sym"))

; =======================
; load and interpret r1cs
(printf "# processing r1cs...\n")
(define circuit-r1cs (r1cs:read-r1cs arg-r1cs))

; print some basic r1cs info
(define nwires (r1cs:get-nwires circuit-r1cs))
(printf "# number of wires: ~a (+1)\n" nwires)
(printf "# number of constraints: ~a\n" (r1cs:get-mconstraints circuit-r1cs))
(printf "# field size (how many bytes): ~a\n" (r1cs:get-field-size circuit-r1cs))

(printf "# interpreting r1cs...\n")
(define-values (xlist sconstraints) (rint:interpret-r1cs circuit-r1cs null)) ; interpret the constraint system
(define input-list (r1cs:r1cs-inputs circuit-r1cs))
(define output-list (r1cs:r1cs-outputs circuit-r1cs))
(printf "# inputs: ~a.\n" input-list)
(printf "# outputs: ~a.\n" output-list)
(printf "# xlist: ~a.\n" xlist)

; ==========================
; load and interpret circom
(printf "# processing circom json...\n")
; if you include, then the json will have multiple lines
(define circuit-strings (string-split (file->string arg-json) "\n")) ; (note) reverse!
(define circuit-jsons (for/list ([s circuit-strings]) (string->jsexpr s)))
(define main-circuit-json (car circuit-jsons))
(define other-circuit-json (cdr circuit-jsons))
(define vm (new analysis:vm%))
(send vm initialize)
; deploy all template circuits
(printf "# deploying templates...\n")
(for ([tmp-json other-circuit-json])
  (define tmp-node (parser:parse-circom-json tmp-json))
  (send vm deploy tmp-node) ; deploy, don't init
)
(printf "# deploying main circuit...\n")
; deploy main circuit
(define main-node (parser:parse-circom-json main-circuit-json))
(send vm deploy main-node)
(define main-root (get-field circom-root vm))
(send vm interpret main-root)

; ; print some basic circuit info
; (define input-book (get-field input-book vm))
; (define output-book (get-field output-book vm))
; (define intermediate-book (get-field intermediate-book vm))
; (printf "  # vc: ~a\n" (vc))
; (printf "  # inputs: ~a\n" input-book)
; (printf "  # outputs: ~a\n" output-book)
; (printf "  # intermediates: ~a\n" intermediate-book)
; ; combine two books
; (define io-book (make-hash (append (hash->list input-book) (hash->list output-book) (hash->list intermediate-book))))

; ; =====================
; ; construct symbol link
; (printf "# connecting symbols...\n")
; (define raw-sym (csv->list (file->string sym-path)))
; ; use 1st column
; ; (define sym2wid (make-hash (for/list ([p raw-sym]) (cons (car (reverse p)) (string->number (car p))))))
; ; use 2nd column
; (define sym2wid (make-hash (for/list ([p raw-sym]) (cons (car (reverse p)) (string->number (car (cdr p)))))))
; ; connect symbolic variables
; (for ([k (hash-keys sym2wid)])
;   (define w0 (hash-ref sym2wid k))
;   (cond
;     [(< w0 0) (printf "  # [intermediate, NOT in r1cs] key=~a, circom=~a\n" k (hash-ref io-book k))]
;     [else
;       (define var-left (list-ref xlist w0))
;       (define var-right (hash-ref io-book k))
;       ; (printf "  # var-left: ~a\n" var-left)
;       (cond
;         [(contains? input-list w0)
;           ; only bind inputs
;           (printf "  # [input, eq] key=~a, r1cs=~a, circom=~a\n" k var-left var-right)
;           ; binding constraint
;           (assert (bveq var-left var-right))
;         ]
;         [(contains? output-list w0)
;           ; outputs are not bound, but go with negation constaint
;           (printf "  # [output, neq] key=~a, r1cs=~a, circom=~a\n" k var-left var-right)
;           ; negation constraint
;           (assert (not (bveq var-left var-right)))
;         ]
;         [else
;           (if (hash-has-key? intermediate-book k)
;             ; intermediates are not bound, and we have no constraints on them
;             (printf "  # [intermediate, in r1cs] key=~a, r1cs=~a, circom=~a\n" k var-left var-right)
;             (printf "  # ---->[something is wrong] key=~a, r1cs=~a, circom=~a\n" k var-left var-right)
;           )
;         ]
;       )
;     ]
;   )
; )

; (printf "# solving equivalence...\n")
; (error-print-width 1000000)
; (define model (solve (assert (apply && sconstraints))))
; (if (sat? model)
;     (printf "  # found a counterexample:\n~a\n" model)
;     (printf "  # no counterexample: verified\n")
; )
