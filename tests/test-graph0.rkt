#lang racket
(require graph)
(require csv-reading)

; (define g (undirected-graph (list (list "a" "b") (list "c" "d") (list "a" "b"))))
(define g (undirected-graph (list )))
(define-edge-property g cid #:init null)

; (cid "a" "b")
; (cid-set! "a" "b" 102)
; (cid "a" "b")

; (csv->list (open-input-file "../benchmarks/circomlib-cff5ab6/BitElementMulAny@escalarmulany.sym"))

(add-vertex! g 0)
(add-vertex! g 1)
(add-vertex! g 2)
(add-edge! g 0 2)

(cid 0 1)