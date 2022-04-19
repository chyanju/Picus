#lang rosette
(require json)
(require "./picus/circom-parser.rkt")
(require "./picus/tokamak.rkt")

(define jj (string->jsexpr (file->string "./examples/test1.json")))
(define sym0 (tokamak:symbolic* 'sb 'integer))
(define sym1 (tokamak:symbolic* 'sb 'integer))