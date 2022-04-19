#lang rosette
(require json)
(require "./picus/circom-parser.rkt")
(require "./picus/tokamak.rkt")

(define jj (string->jsexpr (file->string "./examples/test1.json")))
(define jnode (parse-circom-json jj))