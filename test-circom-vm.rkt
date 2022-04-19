#lang rosette
(require json)
(require "./picus/circom-vm.rkt")
(require "./picus/circom-parser.rkt")
(require "./picus/tokamak.rkt")

(define test1-json (string->jsexpr (file->string "./examples/test1.json")))
(define test1-node (parse-circom-json test1-json))
(define test1-vm (new circom-vm%))
(send test1-vm deploy test1-node)
; (get-field variable-book test1-vm)
(send test1-vm interpret test1-node)
(vc)