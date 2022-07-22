#lang rosette
; this file provides extended utilities from rosette
; to use this file, you should do a (prefix-in ... ...) or renaming to resolve confusions
(require rackunit)
(require/expose rosette/base/core/term (constant expression))
(require/expose rosette/base/core/term (term term-val term-type term-ord))
(require/expose rosette/base/form/define (index!))
(provide (rename-out 
	[constant constant] ; this is the original constant struct in rosette
	[expression expression] ; this is the original expression struct in rosette
	[term term] ; this is the original term struct in rosette
	[term-val term-val]
	[term-type term-type]
	[term-ord term-ord]
	[index! index!] ; necessary for dynamic creation of symbolic variables
))