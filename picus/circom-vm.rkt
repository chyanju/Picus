; (fixme) this file is outdated
#lang rosette
(require rosette/lib/destruct) ; match syntax in rosette
(require "./tokamak.rkt")
(require "./mhash.rkt")
(require "./utils.rkt")
(require "./config.rkt")
(require "./circom-grammar.rkt")
(provide (all-defined-out))

(define circom-vm%
    (class object%
        (super-new)
        (field
            [variable-book null] ; variable book is the top-level scope
            [template-book null] ; stores all templates and functions
            [circom-root null] ; the top-level node, if you want to start, go with the list of components
            [builtin-operators null] ; stores all builtin operators

            ; stateful members
            [input-book null] ; hash mapping from string to symbolic variable
            [output-book null] ; hash mapping from string to symbolic variable
            [intermediate-book null] ; hash mapping from string to symbolic variable

            ; constants
            [bv-zero (bv 0 config:bvtyp)]
            [bv-one (bv 1 config:bvtyp)]
            [bv-two (bv 2 config:bvtyp)]
        )

        ; also do initializations
        ; (concrete:top) arg-node
        (define/public (deploy arg-node arg-init)
            (when arg-init
                (set! variable-book (make-mhash config:cap))
                (set! template-book (make-hash))
                (init-builtin-operators); initialize all builtin operators
            )
            (do-deploy arg-node)
        )

        ; store all the templates into template book
        ; (concrete:top) arg-node
        (define (do-deploy arg-node)
            (destruct arg-node
                [(circom:circom m-meta m-ver m-incs m-defs m-main)
                    ; set root node
                    (set! circom-root arg-node)
                    ; continue to find out all template definitions
                    (for ([node0 m-defs])
                        (do-deploy node0)
                    )
                ]

                ; pass on
                [(circom:definition v) 
                    (for/all ([v0 v #:exhaustive])
                        (tokamak:typed v0 circom:template? circom:function?)
                        (do-deploy v)
                    )
                ]

                [(circom:template m-meta m-name m-args m-argloc m-body m-parallel)
                    ; add template definition
                    (hash-set! template-book m-name arg-node)
                ]

                [(circom:function m-meta m-name m-args m-argloc m-body)
                    ; add function definition
                    (hash-set! template-book m-name arg-node)
                ]

                [_ (tokamak:exit "[do-deploy] unsupported node, got: ~a." arg-node)]
            )
        )

        ; (concrete:top) arg-node
        (define/public (interpret arg-node arg-init)
            ; first clear all stateful vars
            (when arg-init
                (set! input-book (make-hash))
                (set! output-book (make-hash))
                (set! intermediate-book (make-hash))
            )
            (do-interpret arg-node (list variable-book) "" "")
        )

        ; (concrete:top) arg-node
        ; (symbolic:top) arg-scopes: a stacked list of scopes
        ; (symbolic:top) arg-prefix: the prefix attached to every variable interacted (esp. when applied to template)
        ; (symbolic:top) arg-cprx: (call prefix) for fetching the argument in the correct scope
        ;                          when assignment to a component, a call need to append a scope, but when fetching arguments
        ;                          it should still use the old prefix
        ;                          e.g., component lt = LessThan(n), "lt" should be appended, but "n" the argument come without "lt"
        ;                                main.lt.??, but main.n should be fetched before entering LessThan
        ;                          (note) only declstmt with 'comp and call related operation need to modify this field
        ;                                 otherwise, just inherit and ignore
        (define (do-interpret arg-node arg-scopes arg-prefix arg-cprx)
            (tokamak:typed arg-node circom:lang?)

            ; still use destruct to not lose track of vc
            (destruct arg-node

                [(circom:setype v)
                    (for/all ([v0 v #:exhaustive])
                        (tokamak:typed v0 symbol?)
                        (tokamak:typed v0 circom:setype:terminal?)

                        v0
                    )
                ]

                [(circom:stype v)
                    (for/all ([v0 v #:exhaustive])
                        (tokamak:typed v0 symbol?)
                        (tokamak:typed v0 circom:stype:terminal?)

                        v0
                    )
                ]

                [(circom:signal first second)
                    (for*/all ([first0 first #:exhaustive] [second0 second #:exhaustive])
                        (tokamak:typed first0 circom:stype?)
                        (tokamak:typed second0 circom:setype?)

                        (define tmp-first (do-interpret first0 arg-scopes arg-prefix arg-cprx))
                        (define tmp-second (do-interpret second0 arg-scopes arg-prefix arg-cprx))
                        (for*/all ([first1 tmp-first #:exhaustive] [second1 tmp-second #:exhaustive])
                            (tokamak:typed first1 symbol?)
                            (tokamak:typed second1 symbol?)

                            ; return
                            (cons first1 second1)
                        )
                    )
                ]

                [(circom:vtype v)
                    (for/all ([v0 v #:exhaustive])
                        (tokamak:typed v0 symbol? circom:signal?)

                        (cond
                            [(symbol? v0) v0]
                            [(circom:signal? v0) (do-interpret v0 arg-scopes arg-prefix arg-cprx)]
                            [else (tokamak:exit "[do-interpret] you can't reach here.")]
                        )
                    )
                ]

                [(circom:access v)
                    (for/all ([v0 v #:exhaustive])
                        (tokamak:typed v0 string? circom:expression?)
                        ; cond and return
                        (cond
                            [(string? v0) v0] ; direct return
                            [(circom:expression? v0)
                                ; get the value
                                (do-interpret v0 arg-scopes arg-prefix arg-cprx)
                            ]
                        )
                    )
                ]

                [(circom:assignop v)
                    (for/all ([v0 v #:exhaustive])
                        (tokamak:typed v0 symbol?)
                        (tokamak:typed v0 circom:assignop:terminal?)

                        v0
                    )
                ]

                [(circom:infixop v)
                    (for/all ([v0 v #:exhaustive])
                        (tokamak:typed v0 symbol?)
                        (tokamak:typed v0 circom:infixop:terminal?)

                        v0
                    )
                ]

                [(circom:prefixop v)
                    (for/all ([v0 v #:exhaustive])
                        (tokamak:typed v0 symbol?)
                        (tokamak:typed v0 circom:prefixop:terminal?)

                        v0
                    )
                ]

                [(circom:circom m-meta m-ver m-incs m-defs m-main)
                    (for/all ([main0 m-main #:exhaustive])
                        (tokamak:typed main0 circom:component? null?)

                        (cond
                            [(null? main0) (void)] ; do nothing
                            [else (do-interpret main0 arg-scopes arg-prefix arg-cprx)]
                        )
                    )
                ]

                [(circom:component m-public m-call)
                    ; just execute the expression in m-call
                    (for*/all ([call0 m-call #:exhaustive] [prefix0 arg-prefix #:exhaustive])
                        (tokamak:typed call0 circom:expression?)
                        (tokamak:typed prefix0 string?)

                        ; (fixme) the prefix seems to only be "main.", otherwise circom complains
                        (do-interpret call0 arg-scopes prefix0 (string-append prefix0 "main")) ; top level doesn't need a dot
                    )
                ]

                [(circom:template m-meta m-name m-args m-argloc m-body m-parallel)
                    (tokamak:exit "[do-interpret] [template.0] a template node should not be directly interpreted.")
                ]

                ; pass on
                [(circom:statement v)
                    (for/all ([v0 v #:exhaustive])
                        (tokamak:typed v0 circom:itestmt? circom:whilestmt? circom:retstmt? circom:declstmt? circom:substmt?
                                          circom:ceqstmt? circom:logcallstmt? circom:assertstmt? circom:initblock? circom:block?)

                        (do-interpret v0 arg-scopes arg-prefix arg-cprx)
                    )
                ]

                [(circom:itestmt m-meta m-cond m-if m-else)
                    (for*/all ([cond0 m-cond #:exhaustive] [if0 m-if #:exhaustive] [else0 m-else #:exhaustive])
                        (tokamak:typed cond0 circom:expression?)
                        (tokamak:typed if0 circom:statement?)
                        (tokamak:typed else0 circom:statement? null?)

                        (define tmp-cond (do-interpret cond0 arg-scopes arg-prefix arg-cprx))
                        (for/all ([cond1 tmp-cond #:exhaustive])
                            ; (note) for if, this can be symbolic
                            (tokamak:typed cond1 boolean?)

                            (cond
                                [cond1
                                    ; cond is true, go to if branch
                                    (do-interpret if0 arg-scopes arg-prefix arg-cprx)
                                ]
                                [else
                                    ; cond is false, go to else branch
                                    (cond
                                        [(null? else0) (void)] ; else branch is empty
                                        [else (do-interpret else0 arg-scopes arg-prefix arg-cprx)]
                                    )
                                ]
                            )
                        )
                    )
                ]

                ; (note) it seems that the while construct here doesn't open up new scope
                [(circom:whilestmt m-meta m-cond m-stmt)
                    (for*/all ([cond0 m-cond #:exhaustive] [stmt0 m-stmt #:exhaustive])
                        (tokamak:typed cond0 circom:expression?)
                        (tokamak:typed stmt0 circom:statement?)

                        ; define a recursive loop
                        (define (do-while lscopes lprefix lcprx)
                            (define tmp-cond (do-interpret cond0 lscopes lprefix lcprx))
                            (for/all ([cond1 tmp-cond #:exhaustive])
                                ; (note) this has to be both concrete and boolean
                                (tokamak:typed cond1 concrete?)
                                (tokamak:typed cond1 boolean?)

                                (cond
                                    [cond1 
                                        ; cond is true, go to statement
                                        (do-interpret stmt0 lscopes lprefix lcprx)
                                        (do-while lscopes lprefix lcprx)
                                    ]
                                    ; cond is false, do nothing and exit the loop
                                    [else (void)]
                                )
                            )
                        )

                        ; initiate the loop
                        (do-while arg-scopes arg-prefix arg-cprx)
                        
                    )
                ]

                [(circom:retstmt m-meta m-val)
                    (for*/all ([val0 m-val #:exhaustive])
                        (tokamak:typed val0 circom:expression?)
                        ; return
                        (do-interpret val0 arg-scopes arg-prefix arg-cprx)
                    )
                ]

                ; this creates new symbolic variables
                ; (fixme) you need to properly deal with dims
                [(circom:declstmt m-meta m-xtype m-name m-dims m-constant)
                    (for*/all ([xtype0 m-xtype #:exhaustive] [name0 m-name #:exhaustive] [dims0 m-dims #:exhaustive] 
                               [scopes0 arg-scopes #:exhaustive] [prefix0 arg-prefix #:exhaustive] [cprx0 arg-cprx #:exhaustive])
                        (tokamak:typed xtype0 circom:vtype?)
                        (tokamak:typed name0 string?)
                        (tokamak:typed dims0 list?)
                        (tokamak:typed scopes0 list?)
                        (tokamak:typed prefix0 string?)
                        (tokamak:typed cprx0 string?)

                        ; (note) if the original name0 is an inline array's identifier, register its type as 'arr
                        ;        as a special type to help the next substitution, and register its value as its dims in list
                        ;        e.g., (list 3 4) is arr[3][4]
                        (when (not (null? dims0))
                            (make-var scopes0 (string-append prefix0 "." name0) (get-dims scopes0 prefix0 cprx0 dims0))
                            (make-var scopes0 (string-append prefix0 "." name0 "@") 'arr)
                        )

                        ; dynamically create symbolic variable
                        (define dimstrs (assemble-dims scopes0 prefix0 cprx0 dims0)) ; (fixme) currently it's concrete, but it could be symbolic
                        (define vnames (for/list ([ds dimstrs])
                            (string-append prefix0 "." name0 ds)
                        ))

                        (define syms (for/list ([vv vnames])
                            (tokamak:symbolic* (string->symbol vv) config:bvsym)
                        ))
                        
                        ; register in the scope
                        (for ([vname vnames] [sym syms])
                            (make-var scopes0 vname sym)
                        )

                        ; update states
                        (define v (do-interpret xtype0 scopes0 prefix0 cprx0))
                        (for/all ([v0 v #:exhaustive])
                            (tokamak:typed v0 symbol? pair?)

                            (cond
                                [(pair? v0)
                                    (let ([first (car v0)] [second (cdr v0)])
                                        (for*/all ([first0 first #:exhaustive] [second0 second #:exhaustive])
                                            (tokamak:typed first0 symbol?)
                                            (tokamak:typed second0 symbol?) ; (fixme) need to consider 2nd pos here

                                            (cond
                                                [(equal? 'output first0) 
                                                    (for ([vname vnames] [sym syms])
                                                        (hash-set! output-book vname sym)
                                                    )
                                                    ; var is made before, register as 'output type
                                                    (for ([vname vnames])
                                                        (make-var scopes0 (string-append vname "@") 'output)
                                                    )
                                                ]
                                                [(equal? 'input first0) 
                                                    (for ([vname vnames] [sym syms])
                                                        (hash-set! input-book vname sym)
                                                    )
                                                    ; var is made before, register as 'input type
                                                    (for ([vname vnames])
                                                        (make-var scopes0 (string-append vname "@") 'input)
                                                    )
                                                ]
                                                [(equal? 'intermediate first0) 
                                                    (for ([vname vnames] [sym syms])
                                                        (hash-set! intermediate-book vname sym)
                                                    )
                                                    ; var is made before; var is made before, register as 'intermediate type
                                                    (for ([vname vnames])
                                                        (make-var scopes0 (string-append vname "@") 'intermediate)
                                                    )
                                                ]
                                                [else (tokamak:exit "[do-interpret] [declstmt.0] unsupported first0, got: ~a." first0)]
                                            )
                                        )
                                    )
                                ]
                                [(symbol? v0)
                                    (cond
                                        [(equal? 'var v0)
                                            ; var is made before, register as 'var type
                                            (for ([vname vnames])
                                                (make-var scopes0 (string-append vname "@") 'var)
                                            )
                                        ]
                                        [(equal? 'comp v0)
                                            ; component is made before, register as 'comp type
                                            (for ([vname vnames])
                                                (make-var scopes0 (string-append vname "@") 'comp)
                                            )
                                        ]
                                        [else (tokamak:exit "[do-interpret] [declstmt.1] unsupported v0, got: ~a." v0)]
                                    )
                                ]
                                [else (tokamak:exit "[do-interpret] [declstmt.2] you can't reach here.")]
                            )
                        )
                    )
                ]

                ; this creates assertions
                ; (fixme) you need to properly deal with access
                [(circom:substmt m-meta m-var m-access m-op m-rhe)
                    (for*/all ([var0 m-var #:exhaustive] [access0 m-access #:exhaustive] [op0 m-op #:exhaustive]
                               [rhe0 m-rhe #:exhaustive] [scopes0 arg-scopes #:exhaustive] [prefix0 arg-prefix #:exhaustive]
                               [cprx0 arg-cprx #:exhaustive])
                        (tokamak:typed var0 string?)
                        (tokamak:typed access0 list?)
                        (tokamak:typed op0 circom:assignop?)
                        (tokamak:typed rhe0 circom:expression?)
                        (tokamak:typed scopes0 list?)
                        (tokamak:typed prefix0 string?)
                        (tokamak:typed cprx0 string?)

                        (define tmp-accstr (assemble-access scopes0 prefix0 cprx0 access0))
                        (define tmp-var (string-append prefix0 "." var0 tmp-accstr)) ; don't forget the prefix
                        (define tmp-op (do-interpret op0 scopes0 prefix0 cprx0))

                        ; (fixme) maybe there's better way
                        ;         if tmp-var is a component, then rhe needs to append a prefix when interpreting
                        (define tmp-vtype (read-var scopes0 (string-append tmp-var "@")))
                        (tokamak:typed tmp-vtype symbol?)
                        (define tmp-rhe (cond 
                            ; (note) if rhe0 is a call, it will need a new prefix tmp-var
                            ; (fixme) this overrides/ignores the existing cprx0, is this right?
                            [(equal? 'comp tmp-vtype) (do-interpret rhe0 scopes0 prefix0 tmp-var)]

                            [(equal? 'var tmp-vtype) (do-interpret rhe0 scopes0 prefix0 cprx0)]
                            [(equal? 'input tmp-vtype) (do-interpret rhe0 scopes0 prefix0 cprx0)]
                            [(equal? 'output tmp-vtype) (do-interpret rhe0 scopes0 prefix0 cprx0)]
                            [(equal? 'intermediate tmp-vtype) (do-interpret rhe0 scopes0 prefix0 cprx0)]

                            ; special type from picus, array identifier for inline array
                            [(equal? 'arr tmp-vtype) (do-interpret rhe0 scopes0 prefix0 cprx0)]

                            [else (tokamak:exit "[do-interpret] [substmt.0] unsupported tmp-vtype, got: ~a." tmp-vtype)]
                        ))

                        (for/all ([op1 tmp-op #:exhaustive])
                            (tokamak:typed op1 symbol?)
                            ; (note) no need to decompose tmp-rhe, sicne union assertion is also acceptable
                            (cond
                                [(equal? 'arr tmp-vtype)
                                    ; inline array assignment
                                    (for/all ([rhe1 tmp-rhe #:exhaustive])
                                        (tokamak:typed rhe1 list?) ; inline array must return a list
                                        (cond
                                            [(equal? 'var op1)
                                                ; only support `=` symbol for now
                                                ; (fixme) we should properly check lengths match between var dims and rhe1 dims
                                                ;         the current impl is not considering symbolic elem in rhe1
                                                (define ld (get-list-dims0 rhe1))
                                                (define vd (read-var scopes0 tmp-var))
                                                (when (not (equal? ld vd))
                                                    (tokamak:exit "[do-interpret] [substmt.1] dims mismatch, declared: ~a, returned: ~a." vd ld))
                                                (define inds (apply cartesian-product (for/list ([z ld]) (range z))))
                                                (for ([ind inds])
                                                    (define retv (nested-list-ref rhe1 ind))
                                                    ; no need to add prefix since tmp-var already has prefix settled
                                                    (define srcv (string-append 
                                                        tmp-var
                                                        (apply string-append (for/list ([nn ind])
                                                            (string-append "[" (number->string nn) "]")
                                                        ))
                                                    ))
                                                    (write-var scopes0 srcv retv)
                                                )
                                            ]
                                            [else (tokamak:exit "[do-interpret] [substmt.2] unsupported op1 for inline array, got: ~a." op1)]
                                        )
                                    )
                                ]
                                [else
                                    ; other substitution
                                    (define tmp-val (read-var scopes0 tmp-var))
                                    (cond
                                        [(equal? 'csig op1) 
                                            ; `<==` symbol: assert and then update
                                            (assert (equal? tmp-val tmp-rhe))
                                            (write-var scopes0 tmp-var tmp-rhe)
                                        ]
                                        [(equal? 'var op1)
                                            ; `=` symbol: only update
                                            (write-var scopes0 tmp-var tmp-rhe)
                                        ]
                                        [(equal? 'sig op1)
                                            ; `<--` symbol: only assert
                                            (assert (equal? tmp-val tmp-rhe))
                                        ]
                                        [else (tokamak:exit "[do-interpret] [substmt.3] unsupported op1 in substmt, got: ~a." op1)]
                                    )
                                ]
                            )
                        )
                    )
                ]

                [(circom:ceqstmt m-meta m-lhe m-rhe)
                    (for*/all ([lhe0 m-lhe #:exhaustive] [rhe0 m-rhe #:exhaustive])
                        (tokamak:typed lhe0 circom:expression?)
                        (tokamak:typed rhe0 circom:expression?)

                        (define tmp-lhe (do-interpret lhe0 arg-scopes arg-prefix arg-cprx))
                        (define tmp-rhe (do-interpret rhe0 arg-scopes arg-prefix arg-cprx))
                        ; ceqstmt has default operator: ===, we will do assertion only here
                        ; (note) no need to decompose tmp-lhe or tmp-rhe, sicne union assertion is also acceptable
                        (assert (equal? tmp-lhe tmp-rhe))
                    )
                ]

                [(circom:assertstmt m-meta m-arg)
                    (for/all ([arg0 m-arg #:exhaustive])
                        (tokamak:typed arg0 circom:expression?)

                        (define tmp-arg (do-interpret arg0 arg-scopes arg-prefix arg-cprx))
                        ; (fixme) directly make assertion here, is it right?
                        ;         no need to lift tmp-arg
                        ;         but this assert is supposed to be triggered at circom compile time, no?
                        (assert tmp-arg)
                    )
                ]

                [(circom:block m-meta m-stmts)
                    (for/all ([stmts0 m-stmts #:exhaustive])
                        (tokamak:typed stmts0 list?)

                        ; (fixme) beware for/last may not be supported by rosette
                        (for/last ([s stmts0])
                            (for/all ([s0 s #:exhaustive])
                                (tokamak:typed s0 circom:statement?)

                                (do-interpret s0 arg-scopes arg-prefix arg-cprx)
                            )
                        )
                    )
                ]

                [(circom:initblock m-meta m-xtype m-inits)
                    (for/all ([inits0 m-inits #:exhaustive])
                        (tokamak:typed inits0 list?)

                        ; (fixme) beware for/last may not be supported by rosette
                        (for/last ([i inits0])
                            (for/all ([i0 i #:exhaustive])
                                (tokamak:typed i0 circom:statement?)

                                (do-interpret i0 arg-scopes arg-prefix arg-cprx)
                            )
                        )
                    )
                ]

                ; pass on
                [(circom:expression v)
                    (for/all ([v0 v #:exhaustive])
                        (tokamak:typed v0 circom:infix? circom:prefix? circom:inlineswitch? 
                                          circom:variable? circom:call? circom:arrayinline? circom:number?)

                        (do-interpret v0 arg-scopes arg-prefix arg-cprx)
                    )
                ]

                [(circom:call m-meta m-id m-args)
                    (for*/all ([id0 m-id #:exhaustive] [args0 m-args #:exhaustive])
                        (tokamak:typed id0 string?)
                        (tokamak:typed args0 list?)

                        ; grab args
                        (define tmp-args (for/list ([arg args0])
                            (for/all ([arg0 arg #:exhaustive])
                                (tokamak:typed arg0 circom:expression?)

                                (do-interpret arg0 arg-scopes arg-prefix arg-cprx)
                            )
                        ))

                        ; call and return
                        (for*/all ([args1 tmp-args #:exhaustive] [scopes0 arg-scopes #:exhaustive] [cprx0 arg-cprx #:exhaustive])
                            (tokamak:typed args1 list?)
                            (tokamak:typed scopes0 list?)
                            (tokamak:typed cprx0 string?)

                            ; (note) this should switch to call prefix, don't use the original prefix
                            (call-template scopes0 cprx0 id0 args1)
                        )
                    )
                ]

                [(circom:infix m-meta m-lhe m-op m-rhe)
                    (for*/all ([lhe0 m-lhe #:exhaustive] [op0 m-op #:exhaustive] [rhe0 m-rhe #:exhaustive])
                        (tokamak:typed lhe0 circom:expression?)
                        (tokamak:typed op0 circom:infixop?)
                        (tokamak:typed rhe0 circom:expression?)

                        (define tmp-lhe (do-interpret lhe0 arg-scopes arg-prefix arg-cprx))
                        (define tmp-rhe (do-interpret rhe0 arg-scopes arg-prefix arg-cprx))
                        (define tmp-op (do-interpret op0 arg-scopes arg-prefix arg-cprx))
                        ; (note) `apply` is not listed as rosette's lifted form (but can be found in rosette/safe)
                        ;        for safety we still manually lift it here
                        (define tmp-result (for*/all ([lhe1 tmp-lhe #:exhaustive] [op1 tmp-op #:exhaustive] [rhe1 tmp-rhe #:exhaustive])
                            ; (fixme) lhe1 is indecomposable, for all ops here, it's good to go (no type checking required)
                            ; (fixme) rhe1 is indecomposable, for all ops here, it's good to go (no type checking required)
                            (tokamak:typed op1 symbol?)

                            (apply (hash-ref builtin-operators op1) (list lhe1 rhe1))
                        ))
                        ; return
                        tmp-result
                    )
                ]

                [(circom:prefix m-meta m-op m-rhe)
                    (for*/all ([op0 m-op #:exhaustive] [rhe0 m-rhe #:exhaustive])
                        (tokamak:typed op0 circom:prefixop?)
                        (tokamak:typed rhe0 circom:expression?)

                        (define tmp-rhe (do-interpret rhe0 arg-scopes arg-prefix arg-cprx))
                        (define tmp-op (do-interpret op0 arg-scopes arg-prefix arg-cprx))
                        ; (note) `apply` is not listed as rosette's lifted form (but can be found in rosette/safe)
                        ;        for safety we still manually lift it here
                        (define tmp-result (for*/all ([rhe1 tmp-rhe #:exhaustive] [op1 tmp-op #:exhaustive])
                            ; (fixme) rhe1 is indecomposable, for all ops here, it's good to go (no type checking required)
                            (tokamak:typed op1 symbol?)

                            (apply (hash-ref builtin-operators op1) (list rhe1))
                        ))
                        ; return
                        tmp-result
                    )
                ]

                [(circom:inlineswitch m-meta m-cond m-true m-false)
                    (for*/all ([cond0 m-cond #:exhaustive] [true0 m-true #:exhaustive] [false0 m-false #:exhaustive])
                        (tokamak:typed cond0 circom:expression?)
                        (tokamak:typed true0 circom:expression?)
                        (tokamak:typed false0 circom:expression?)

                        (define tmp-cond (do-interpret cond0 arg-scopes arg-prefix arg-cprx))
                        (for/all ([cond1 tmp-cond #:exhaustive])
                            (tokamak:typed cond1 boolean?)

                            (cond
                                [cond1
                                    ; cond is true, go to true branch
                                    (do-interpret true0 arg-scopes arg-prefix arg-cprx)
                                ]
                                [else
                                    ; cond is false, go to false branch
                                    ; unlike ifthenelse, this must have a false branch
                                    (do-interpret false0 arg-scopes arg-prefix arg-cprx)
                                ]
                            )
                        )
                    )
                ]

                [(circom:number m-meta v)
                    (for/all ([v0 v #:exhaustive])
                        (tokamak:typed v0 integer?)

                        (bv v0 config:bvtyp) ; wrap into bitvector
                    )
                ]

                ; (fixme) you need to properly deal with access
                [(circom:variable m-meta m-name m-access)
                    (for*/all ([name0 m-name #:exhaustive] [access0 m-access #:exhaustive] [scopes0 arg-scopes #:exhaustive] 
                               [prefix0 arg-prefix #:exhaustive] [cprx0 arg-cprx #:exhaustive])
                        (tokamak:typed name0 string?)
                        (tokamak:typed access0 list?)
                        (tokamak:typed scopes0 list?)
                        (tokamak:typed prefix0 string?)
                        (tokamak:typed cprx0 string?)

                        (define tmp-accstr (assemble-access scopes0 prefix0 cprx0 access0))
                        (read-var scopes0 (string-append prefix0 "." name0 tmp-accstr))
                    )
                ]

                [(circom:arrayinline m-meta m-vals)
                    (for/all ([vals0 m-vals #:exhaustive])
                        (tokamak:typed vals0 list?)

                        (for/list ([val vals0])
                            (do-interpret val arg-scopes arg-prefix arg-cprx)
                        )
                    )
                ]

                [_ (tokamak:exit "[do-interpret] unsupported node, got: ~a." arg-node)]
            )
        )

        ; (concrete:top) arg-scopes
        ; (concrete:top) arg-prefix
        ; (concrete:top) arg-name
        ; (concrete:top) arg-args
        (define/public (call-template arg-scopes arg-prefix arg-name arg-args)
            (tokamak:typed arg-scopes list?)
            (tokamak:typed arg-prefix string?)
            (tokamak:typed arg-name string?)
            (tokamak:typed arg-args list?)

            (define tmp-template (hash-ref template-book arg-name)) ; fetch the template node
            ; you could've stored a symbolic template, couldn't you?
            (for/all ([template0 tmp-template #:exhaustive])
                (tokamak:typed template0 circom:template? circom:function?)
                (cond
                    [(circom:template? template0)
                        (define tmp-args (circom:template-args template0)) ; fetch the template args
                        (define tmp-body (circom:template-body template0)) ; fetch the template body

                        (for*/all ([args0 tmp-args #:exhaustive] [body0 tmp-body #:exhaustive])
                            (tokamak:typed args0 list?)
                            (tokamak:typed body0 circom:statement?)

                            ; check arity
                            (when (not (equal? (length args0) (length arg-args)))
                                (tokamak:exit "[call-template] argument arities mismatch, template requires ~a, but ~a is provided."
                                    (length args0) (length arg-args)))

                            (for ([local-id args0] [local-val arg-args])
                                ; (fixme) ideally local variables from arguments should not have additional prefix
                                ;         but we don't want to spend more efforts separating them, so let's add the prefix
                                ;         for now so it fits the current call model
                                ; ....... and maybe this is right
                                (make-var arg-scopes (string-append arg-prefix "." local-id) local-val)
                                ; (fixme) argument assignment, let's not register any type info
                            )
                            ; interpret template body
                            (do-interpret body0 arg-scopes arg-prefix arg-prefix)
                        )
                    ]
                    [(circom:function? template0)
                        ; (fixme) you probably need to create a local scope here
                        ;         we will see

                        (define tmp-args (circom:function-args template0)) ; fetch the function args
                        (define tmp-body (circom:function-body template0)) ; fetch the function body

                        (for*/all ([args0 tmp-args #:exhaustive] [body0 tmp-body #:exhaustive])
                            (tokamak:typed args0 list?)
                            (tokamak:typed body0 circom:statement?)

                            ; check arity
                            (when (not (equal? (length args0) (length arg-args)))
                                (tokamak:exit "[call-function] argument arities mismatch, function requires ~a, but ~a is provided."
                                    (length args0) (length arg-args)))

                            (for ([local-id args0] [local-val arg-args])
                                ; (fixme) ideally local variables from arguments should not have additional prefix
                                ;         but we don't want to spend more efforts separating them, so let's add the prefix
                                ;         for now so it fits the current call model
                                ; ....... and maybe this is right
                                (make-var arg-scopes (string-append arg-prefix "." local-id) local-val)
                                ; (fixme) argument assignment, let's not register any type info
                            )
                            ; interpret function body
                            (do-interpret body0 arg-scopes arg-prefix arg-prefix)
                        )
                    ]
                    [else (tokamak:exit "[call-template] you can't reach here.")]
                )
            )  
        )

        ; (concrete:top) arg-scopes
        ; (concrete:top) arg-prefix
        ; (concrete:top) arg-dims
        ; this returns a list of dims, e.g., (list 3 4) is for arr[3][4]
        ; (fixme) you need to properly deal with symbolic case
        (define (get-dims arg-scopes arg-prefix arg-cprx arg-dims)
            (tokamak:typed arg-scopes list?)
            (tokamak:typed arg-prefix string?)
            (tokamak:typed arg-dims list?)

            ; generate concrete dims
            (define tmp-dims (for/list ([dim arg-dims])
                (tokamak:typed dim circom:expression?)

                (define tmp-dim (do-interpret dim arg-scopes arg-prefix arg-cprx))
                ; (note) dim must be concrete, and you need to convert it to integer
                (tokamak:typed tmp-dim concrete?)
                (tokamak:typed tmp-dim bv?)

                (bitvector->integer tmp-dim)
            ))

            ; return
            tmp-dims
        )

        ; (concrete:top) arg-scopes
        ; (concrete:top) arg-prefix
        ; (concrete:top) arg-dims
        ; (note) this method returns a list of all dims strings
        ; (fixme) you need to properly deal with symbolic case
        (define (assemble-dims arg-scopes arg-prefix arg-cprx arg-dims)
            (tokamak:typed arg-scopes list?)
            (tokamak:typed arg-prefix string?)
            (tokamak:typed arg-dims list?)

            (cond
                [(null? arg-dims) (list "")] ; no dims
                [else
                    ; generate concrete dims
                    (define tmp-dims (get-dims arg-scopes arg-prefix arg-cprx arg-dims))
                    (define tmp-lls (for/list ([d tmp-dims])
                        ; create a range
                        (for/list ([i (range d)])
                            (string-append "[" (number->string i) "]")
                        )
                    ))
                    ; then do a cartesian product
                    (define tmp-strs (apply cartesian-product tmp-lls))
                    ; (printf "tmp-strs: ~a\n" tmp-strs)

                    ; assemble and return
                    (for/list ([s tmp-strs])
                        (apply string-append s)
                    )
                ]
            )
        )

        ; (concrete:top) arg-scopes
        ; (concrete:top) arg-prefix
        ; (concrete:top) arg-access
        ; (fixme) you need to properly deal with symbolic case
        (define (assemble-access arg-scopes arg-prefix arg-cprx arg-access)
            (tokamak:typed arg-scopes list?)
            (tokamak:typed arg-prefix string?)
            (tokamak:typed arg-access list?)

            (cond
                [(null? arg-access) ""] ; no access
                [else
                    ; generate concrete access, like dims
                    (define tmp-access (for/list ([acc arg-access])
                        (tokamak:typed acc circom:access?)

                        (define tmp-acc (do-interpret acc arg-scopes arg-prefix arg-cprx))
                        (tokamak:typed tmp-acc concrete?)
                        (tokamak:typed tmp-acc bv? string?)
                        ; convert to formatted string
                        (cond
                            ; [(string? tmp-acc) (string-append "[" tmp-acc "]")]
                            [(string? tmp-acc) (string-append "." tmp-acc )] ; (fixme) this is usually component access, right?
                            [(bv? tmp-acc) (string-append "[" (number->string (bitvector->integer tmp-acc)) "]")]
                        )
                    ))

                    ; assemble and return
                    (apply string-append tmp-access)
                ]
            )
        )

        ; create a variable in the nearest scope
        ; (symbolic:top) arg-stack
        ; (concrete:top) arg-id
        ; (symbolic:top) arg-val
        (define (make-var arg-stack arg-id arg-val)
            (tokamak:typed arg-id string?)
            (for/all ([stack0 arg-stack #:exhaustive])
                (tokamak:typed stack0 list?)

                (when (null? stack0) (tokamak:exit "[make-var] stack0 is empty."))
                (let ([scope (car stack0)])
                    (for/all ([scope0 scope #:exhaustive])
                        (tokamak:typed scope0 mhash?)

                        (mhash-set! scope arg-id arg-val)
                    )
                )
            )
        )

        ; read a variable from the stack of scopes, from nearest to farthest (top)
        ; (symbolic:top) arg-stack
        ; (concrete:top) arg-id
        (define (read-var arg-stack arg-id)
            (tokamak:typed arg-id string?)
            (for/all ([stack0 arg-stack #:exhaustive])
                (tokamak:typed stack0 list?)

                (let ([scope (car stack0)] [stack-res (cdr stack0)])
                    (for/all ([scope0 scope #:exhaustive])
                        (tokamak:typed scope0 mhash?)

                        (cond 
                            [(mhash-has-key? scope0 arg-id)
                                (mhash-ref scope0 arg-id)
                            ]
                            [(null? stack-res)
                                (tokamak:exit "[read-var] cannot find variable in all scopes, got: ~a." arg-id)
                            ]
                            [else
                                (read-var stack-res arg-id)
                            ]
                        )
                    ) 
                )
            )
        )

        ; write a variable to the stack of scopes, nearest first
        ; this requires the variable to exist before writing
        ; (symbolic:top) arg-stack
        ; (concrete:top) arg-id
        ; (symbolic:top) arg-val
        (define (write-var arg-stack arg-id arg-val)
            (tokamak:typed arg-id string?)
            (for/all ([stack0 arg-stack #:exhaustive])
                (tokamak:typed stack0 list?)

                (let ([scope (car stack0)] [stack-res (cdr stack0)])
                    (for/all ([scope0 scope #:exhaustive])
                        (tokamak:typed scope0 mhash?)

                        (cond
                            [(mhash-has-key? scope0 arg-id)
                                (mhash-set! scope0 arg-id arg-val)
                            ]
                            [(null? stack-res)
                                (tokamak:exit "[write-var] cannot find variable in all scopes, got: ~a." arg-id)
                            ]
                            [else
                                (write-var stack-res arg-id arg-val)
                            ]
                        )
                    )
                )
            )
        )

        (define (init-builtin-operators)
            ; (note) (fixme) all arguments should be concrete, you are not checking them all
            (set! builtin-operators (make-hash))

            ; ; borrowed from ecne for speed up
            ; (define (circom-mod x k)
            ;     (if (bvugt x k)
            ;         (bvsub x k)
            ;         x
            ;     )
            ; )
            (define (circom-mod x k) x)

            ; helper functions
            (define (circom-pow x k)
                ; (tokamak:exit "[debug] circom-pow x=~a k=~a" x k)
                (tokamak:typed x bv?)
                ; (note) k needs to be both concrete and bv
                (tokamak:typed k bv?)
                (tokamak:typed k concrete?)

                (if (bvzero? k)
                    bv-one
                    (config:mul x (circom-pow x (bvsub k bv-one)))
                )
            )

            ; ref: https://docs.circom.io/circom-language/basic-operators/#bitwise-operators
            (define (circom-shr x k)
                (tokamak:typed x bv?)
                ; (note) k needs to be both concrete and bv
                (tokamak:typed k bv?)
                (tokamak:typed k concrete?)

                (cond
                    ; 0=< k <= p/2
                    [(&&
                        (bvsle bv-zero k)
                        (bvsle k (bvsdiv config:bvp bv-two))
                     )
                        ; equals to: x/(2**k)
                        (bvsdiv x (circom-pow bv-two k))
                    ]
                    ; p/2 +1<= k < p
                    [(&&
                        (bvsle (bvadd bv-one (bvsdiv config:bvp bv-two)) k)
                        (bvslt k config:bvp)
                     )
                        ; equals to: x << (p-k)
                        (circom-shl x (bvsub config:bvp k))
                    ]
                    [else (tokamak:exit "[circom-shr] you can't reach here.")]
                )
            )

            ; ref: https://docs.circom.io/circom-language/basic-operators/#bitwise-operators
            (define (circom-shl x k)
                (tokamak:typed x bv?)
                ; (note) k needs to be both concrete and bv
                (tokamak:typed k bv?)
                (tokamak:typed k concrete?)

                (cond
                    ; 0=< k <= p/2
                    [(&&
                        (bvsle bv-zero k)
                        (bvsle k (bvsdiv config:bvp bv-two))
                     )
                        ; (fixme) you probably need to remove circom-mod temporarily
                        ; equals to: (x*(2{**}k)~ & ~mask) % p
                        (circom-mod
                            (bvand
                                (config:mul x (circom-pow bv-two k))
                                (bvnot config:bvmask)
                            )
                            config:bvp
                        )
                    ]
                    ; p/2 +1<= k < p
                    [(&&
                        (bvsle (bvadd bv-one (bvsdiv config:bvp bv-two)) k)
                        (bvslt k config:bvp)
                     )
                        ; equals to: x >> (p-k)
                        (circom-shr x (bvsub config:bvp k))
                    ]
                    [else (tokamak:exit "[circom-shl] you can't reach here.")]
                )
            )

            ; arithmethc operators (input: bitvector, output: boolean)
            (hash-set! builtin-operators 'mul (lambda (x y) (config:mul x y)))
            (hash-set! builtin-operators 'add (lambda (x y) (bvadd x y)))
            (hash-set! builtin-operators 'div (lambda (x y) (bvsdiv x y))) ; (fixme) this should be raw division, but bvsdiv is quotient, see doc
            (hash-set! builtin-operators 'intdiv (lambda (x y) (bvsdiv x y))) ; quotient
            (hash-set! builtin-operators 'mod (lambda (x y) (bvsrem x y))); remainder
            (hash-set! builtin-operators 'sub (lambda (x y) (bvsub x y) ))
            (hash-set! builtin-operators 'pow (lambda (x y) (circom-pow x y)))

            (hash-set! builtin-operators 'neg (lambda (x) (bvneg x)))
            
            ; relational operators (input: bitvector, output: boolean)
            (hash-set! builtin-operators 'lt (lambda (x y) (bvslt x y)))
            (hash-set! builtin-operators 'leq (lambda (x y) (bvsle x y)))
            (hash-set! builtin-operators 'gt (lambda (x y) (bvsgt x y)))
            (hash-set! builtin-operators 'geq (lambda (x y) (bvsge x y)))
            (hash-set! builtin-operators 'eq (lambda (x y) (bveq x y)))
            (hash-set! builtin-operators 'neq (lambda (x y) (not (bveq x y))))

            ; boolean operators (input: boolean, output: boolean)
            (hash-set! builtin-operators 'and (lambda (x y) (&& x y)))
            (hash-set! builtin-operators 'or (lambda (x y) (|| x y)))
            (hash-set! builtin-operators 'not (lambda (x) (not x)))

            ; bitwise operators
            ; ref: https://docs.circom.io/circom-language/basic-operators/#bitwise-operators
            (hash-set! builtin-operators 'band (lambda (x y) (bvand x y)))
            (hash-set! builtin-operators 'bor (lambda (x y) (bvor x y)))
            (hash-set! builtin-operators 'comp (lambda (x) (bvnot x))) ; (fixme) is this right?
            (hash-set! builtin-operators 'bxor' (lambda (x y) (bvxor x y)))
            (hash-set! builtin-operators 'shr (lambda (x k) (circom-shr x k)))
            (hash-set! builtin-operators 'shl (lambda (x k) (circom-shl x k)))

        )

    )
)