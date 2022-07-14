#lang rosette
(require "./picus/mhash.rkt")

(define m0 (make-mhash 10))
(mhash-has-key? m0 "apple")
(mhash-set! m0 "apple" 13)
(mhash-ref m0 "apple")
(mhash-has-key? m0 "apple")