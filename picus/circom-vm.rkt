#lang rosette
(require rosette/lib/destruct) ; match syntax in rosette
(require "./tokamak.rkt")
(require "./mhash.rkt")
(require "./config.rkt")
(require "./circom-grammar.rkt")
(provide (all-defined-out))

(define circom-vm%
    (class object%
        (super-new)
        (field
            [variable-book null] ; variable book is the top-level scope
            [template-book null] ; stores all templates
            [circom-root null] ; the top-level node, if you want to start, go with the list of components
            [builtin-operators null] ; stores all builtin operators

            ; stateful members
            [input-book null] ; hash mapping from string to symbolic variable
            [output-book null] ; hash mapping from string to symbolic variable
            [intermediate-book null] ; hash mapping from string to symbolic variable

            ; constants
            [bv-zero (bv 0 config:bv)]
            [bv-one (bv 1 config:bv)]
            [bv-two (bv 2 config:bv)]
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
            (do-interpret arg-node (list variable-book) "")
        )

        ; (concrete:top) arg-node
        ; (symbolic:top) arg-scopes: a stacked list of scopes
        ; (symbolic:top) arg-prefix: the prefix attached to every variable interacted (esp. when applied to template)
        (define (do-interpret arg-node arg-scopes arg-prefix)
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

                        (define tmp-first (do-interpret first0 arg-scopes arg-prefix))
                        (define tmp-second (do-interpret second0 arg-scopes arg-prefix))
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
                            [(circom:signal? v0) (do-interpret v0 arg-scopes arg-prefix)]
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
                                (do-interpret v0 arg-scopes arg-prefix)
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
                            [else (do-interpret main0 arg-scopes arg-prefix)]
                        )
                    )
                ]

                [(circom:component m-public m-call)
                    ; just execute the expression in m-call
                    (for*/all ([call0 m-call #:exhaustive] [prefix0 arg-prefix #:exhaustive])
                        (tokamak:typed call0 circom:expression?)
                        (tokamak:typed prefix0 string?)

                        ; (fixme) the prefix seems to only be "main.", otherwise circom complains
                        (do-interpret call0 arg-scopes (string-append "main." prefix0))
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

                        (do-interpret v0 arg-scopes arg-prefix)
                    )
                ]

                ; (note) it seems that the while construct here doesn't open up new scope
                [(circom:whilestmt m-meta m-cond m-stmt)
                    (for*/all ([cond0 m-cond #:exhaustive] [stmt0 m-stmt #:exhaustive])
                        (tokamak:typed cond0 circom:expression?)
                        (tokamak:typed stmt0 circom:statement?)

                        ; define a recursive loop
                        (define (do-while lscopes lprefix)
                            (define tmp-cond (do-interpret cond0 lscopes lprefix))
                            (for/all ([cond1 tmp-cond #:exhaustive])
                                ; (note) this has to be both concrete and boolean
                                (tokamak:typed cond1 concrete?)
                                (tokamak:typed cond1 boolean?)

                                (cond
                                    [cond1 
                                        ; cond is true, go to statement
                                        (do-interpret stmt0 lscopes lprefix)
                                        (do-while lscopes lprefix)
                                    ]
                                    ; cond is false, do nothing and exit the loop
                                    [else (void)]
                                )
                            )
                        )

                        ; initiate the loop
                        (do-while arg-scopes arg-prefix)
                        
                    )
                ]

                ; this creates new symbolic variables
                ; (fixme) you need to properly deal with dims
                [(circom:declstmt m-meta m-xtype m-name m-dims m-constant)
                    (for*/all ([xtype0 m-xtype #:exhaustive] [name0 m-name #:exhaustive] 
                               [dims0 m-dims #:exhaustive] [scopes0 arg-scopes #:exhaustive] [prefix0 arg-prefix #:exhaustive])
                        (tokamak:typed xtype0 circom:vtype?)
                        (tokamak:typed name0 string?)
                        (tokamak:typed dims0 list?)
                        (tokamak:typed scopes0 list?)
                        (tokamak:typed prefix0 string?)

                        ; dynamically create symbolic variable
                        (define dimstrs (assemble-dims scopes0 prefix0 dims0)) ; (fixme) currently it's concrete, but it could be symbolic
                        (define vnames (for/list ([ds dimstrs])
                            (string-append prefix0 name0 ds)
                        ))

                        (define syms (for/list ([vv vnames])
                            (tokamak:symbolic* (string->symbol vv) config:bvsym)
                        ))
                        
                        ; register in the scope
                        (for ([vname vnames] [sym syms])
                            (make-var scopes0 vname sym)
                        )

                        ; update states
                        (define v (do-interpret xtype0 scopes0 prefix0))
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
                                                        (hash-set! input-book vname sym)
                                                    )
                                                    ; var is made before
                                                ]
                                                [(equal? 'input first0) 
                                                    (for ([vname vnames] [sym syms])
                                                        (hash-set! output-book vname sym)
                                                    )
                                                    ; var is made before
                                                ]
                                                [(equal? 'intermediate first0) 
                                                    (for ([vname vnames] [sym syms])
                                                        (hash-set! intermediate-book vname sym)
                                                    )
                                                    ; var is made before
                                                ]
                                                [else (tokamak:exit "[do-interpret] [declstmt.0] unsupported first0, got: ~a." first0)]
                                            )
                                        )
                                    )
                                ]
                                [(symbol? v0)
                                    (cond
                                        [(equal? 'var v0) (void)] ; var is made before
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
                               [rhe0 m-rhe #:exhaustive] [scopes0 arg-scopes #:exhaustive] [prefix0 arg-prefix #:exhaustive])
                        (tokamak:typed var0 string?)
                        (tokamak:typed access0 list?)
                        (tokamak:typed op0 circom:assignop?)
                        (tokamak:typed rhe0 circom:expression?)
                        (tokamak:typed scopes0 list?)
                        (tokamak:typed prefix0 string?)

                        (define tmp-rhe (do-interpret rhe0 scopes0 prefix0))
                        (define tmp-accstr (assemble-access scopes0 prefix0 access0))
                        (define tmp-var (string-append prefix0 var0 tmp-accstr)) ; don't forget the prefix
                        (define tmp-val (read-var scopes0 tmp-var))
                        (define tmp-op (do-interpret op0 scopes0 prefix0))
                        (for/all ([op1 tmp-op #:exhaustive])
                            (tokamak:typed op1 symbol?)
                            ; (note) no need to decompose tmp-rhe, sicne union assertion is also acceptable

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
                                [else (tokamak:exit "[do-interpret] [substmt.0] unsupported op1 in substmt, got: ~a." op1)]
                            )
                        )
                    )
                ]

                [(circom:ceqstmt m-meta m-lhe m-rhe)
                    (for*/all ([lhe0 m-lhe #:exhaustive] [rhe0 m-rhe #:exhaustive])
                        (tokamak:typed lhe0 circom:expression?)
                        (tokamak:typed rhe0 circom:expression?)

                        (define tmp-lhe (do-interpret lhe0 arg-scopes arg-prefix))
                        (define tmp-rhe (do-interpret rhe0 arg-scopes arg-prefix))
                        ; ceqstmt has default operator: ===, we will do assertion only here
                        ; (note) no need to decompose tmp-lhe or tmp-rhe, sicne union assertion is also acceptable
                        (assert (equal? tmp-lhe tmp-rhe))
                    )
                ]

                [(circom:block m-meta m-stmts)
                    (for/all ([stmts0 m-stmts #:exhaustive])
                        (tokamak:typed stmts0 list?)

                        (for ([s stmts0])
                            (for/all ([s0 s #:exhaustive])
                                (tokamak:typed s0 circom:statement?)

                                (do-interpret s0 arg-scopes arg-prefix)
                            )
                        )
                    )
                ]

                [(circom:initblock m-meta m-xtype m-inits)
                    (for/all ([inits0 m-inits #:exhaustive])
                        (tokamak:typed inits0 list?)

                        (for ([i inits0])
                            (for/all ([i0 i #:exhaustive])
                                (tokamak:typed i0 circom:statement?)

                                (do-interpret i0 arg-scopes arg-prefix)
                            )
                        )
                    )
                ]

                ; pass on
                [(circom:expression v)
                    (for/all ([v0 v #:exhaustive])
                        (tokamak:typed v0 circom:infix? circom:prefix? circom:inlineswitch? 
                                          circom:variable? circom:call? circom:arrayinline? circom:number?)

                        (do-interpret v0 arg-scopes arg-prefix)
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

                                (do-interpret arg0 arg-scopes arg-prefix)
                            )
                        ))

                        ; call and return
                        (for*/all ([args1 tmp-args #:exhaustive] [scopes0 arg-scopes #:exhaustive] [prefix0 arg-prefix #:exhaustive])
                            (tokamak:typed args1 list?)
                            (tokamak:typed scopes0 list?)
                            (tokamak:typed prefix0 string?)

                            (call-template scopes0 prefix0 id0 args1)
                        )
                    )
                ]

                [(circom:infix m-meta m-lhe m-op m-rhe)
                    (for*/all ([lhe0 m-lhe #:exhaustive] [op0 m-op #:exhaustive] [rhe0 m-rhe #:exhaustive])
                        (tokamak:typed lhe0 circom:expression?)
                        (tokamak:typed op0 circom:infixop?)
                        (tokamak:typed rhe0 circom:expression?)

                        (define tmp-lhe (do-interpret lhe0 arg-scopes arg-prefix))
                        (define tmp-rhe (do-interpret rhe0 arg-scopes arg-prefix))
                        (define tmp-op (do-interpret op0 arg-scopes arg-prefix))
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

                        (define tmp-rhe (do-interpret rhe0 arg-scopes arg-prefix))
                        (define tmp-op (do-interpret op0 arg-scopes arg-prefix))
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

                [(circom:number m-meta v)
                    (for/all ([v0 v #:exhaustive])
                        (tokamak:typed v0 integer?)

                        (bv v0 config:bv) ; wrap into bitvector
                    )
                ]

                ; (fixme) you need to properly deal with access
                [(circom:variable m-meta m-name m-access)
                    (for*/all ([name0 m-name #:exhaustive] [access0 m-access #:exhaustive]
                               [scopes0 arg-scopes #:exhaustive] [prefix0 arg-prefix #:exhaustive])
                        (tokamak:typed name0 string?)
                        (tokamak:typed access0 list?)
                        (tokamak:typed scopes0 list?)
                        (tokamak:typed prefix0 string?)

                        (define tmp-accstr (assemble-access scopes0 prefix0 access0))
                        (read-var scopes0 (string-append prefix0 name0 tmp-accstr))
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
                (tokamak:typed template0 circom:template?)

                (define tmp-args (circom:template-args template0)) ; fetch the template args
                (define tmp-body (circom:template-body template0)) ; fetch the template body

                (for*/all ([args0 tmp-args #:exhaustive] [body0 tmp-body #:exhaustive])
                    (tokamak:typed args0 list?)
                    (tokamak:typed body0 circom:statement?)

                    ; check arity
                    (when (not (equal? (length args0) (length arg-args)))
                        (tokamak:exit "[call-template] argument arities mismatch, template requires ~a, but ~a is provided."
                            (length args0) (length arg-args)))

                    ; create a local scope
                    (define local-scope (make-mhash config:cap))
                    ; initialize local scope with argument values
                    (for ([local-id args0] [local-val arg-args])
                        ; (make-var (cons local-scope scopes0) local-id local-val)
                        ; (fixme) ideally local variables from arguments should not have additional prefix
                        ;         but we don't want to spend more efforts separating them, so let's add the prefix
                        ;         for now so it fits the current call model
                        (make-var (cons local-scope arg-scopes) (string-append arg-prefix local-id) local-val)
                    )

                    ; interpret template body
                    (do-interpret body0 (cons local-scope arg-scopes) arg-prefix)
                )
            )  
        )

        ; (concrete:top) arg-scopes
        ; (concrete:top) arg-prefix
        ; (concrete:top) arg-dims
        ; (note) this method returns a list of all dims strings
        ; (fixme) you need to properly deal with symbolic case
        (define (assemble-dims arg-scopes arg-prefix arg-dims)
            (tokamak:typed arg-scopes list?)
            (tokamak:typed arg-prefix string?)
            (tokamak:typed arg-dims list?)

            (cond
                [(null? arg-dims) (list "")] ; no dims
                [else
                    ; generate concrete dims
                    (define tmp-dims (for/list ([dim arg-dims])
                        (tokamak:typed dim circom:expression?)

                        (define tmp-dim (do-interpret dim arg-scopes arg-prefix))
                        ; (note) dim must be concrete, and you need to convert it to integer
                        (tokamak:typed tmp-dim concrete?)
                        (tokamak:typed tmp-dim bv?)

                        (bitvector->integer tmp-dim)
                    ))
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
        (define (assemble-access arg-scopes arg-prefix arg-access)
            (tokamak:typed arg-scopes list?)
            (tokamak:typed arg-prefix string?)
            (tokamak:typed arg-access list?)

            (cond
                [(null? arg-access) ""] ; no access
                [else
                    ; generate concrete access, like dims
                    (define tmp-access (for/list ([acc arg-access])
                        (tokamak:typed acc circom:access?)

                        (define tmp-acc (do-interpret acc arg-scopes arg-prefix))
                        (tokamak:typed tmp-acc concrete?)
                        (tokamak:typed tmp-acc bv? string?)
                        ; convert to formatted string
                        (cond
                            [(string? tmp-acc) (string-append "[" tmp-acc "]")]
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
                    [(and
                        (bvsle bv-zero k)
                        (bvsle k (bvsdiv config:p bv-two))
                     )
                        ; equals to: x/(2**k)
                        (bvsdiv x (circom-pow bv-two k))
                    ]
                    ; p/2 +1<= k < p
                    [(and
                        (bvsle (bvadd bv-one (bvsdiv config:p bv-two)) k)
                        (bvslt k config:p)
                     )
                        ; equals to: x << (p-k)
                        (circom-shl x (bvsub config:p k))
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
                    [(and
                        (bvsle bv-zero k)
                        (bvsle k (bvsdiv config:p bv-two))
                     )
                        ; (fixme) you probably need to remove circom-mod temporarily
                        ; equals to: (x*(2{**}k)~ & ~mask) % p
                        (circom-mod
                            (bvand
                                (config:mul x (circom-pow bv-two k))
                                (bvnot config:mask)
                            )
                            config:p
                        )
                    ]
                    ; p/2 +1<= k < p
                    [(and
                        (bvsle (bvadd bv-one (bvsdiv config:p bv-two)) k)
                        (bvslt k config:p)
                     )
                        ; equals to: x >> (p-k)
                        (circom-shr x (bvsub config:p k))
                    ]
                    [else (tokamak:exit "[circom-shl] you can't reach here.")]
                )
            )

            ; arithmethc operators (returns bitvector)
            ; (hash-set! builtin-operators 'mul (lambda (x y) (bvmul x y)))
            (hash-set! builtin-operators 'mul (lambda (x y) (config:mul x y)))
            (hash-set! builtin-operators 'add (lambda (x y) (bvadd x y)))
            (hash-set! builtin-operators 'div (lambda (x y) (bvsdiv x y)))
            (hash-set! builtin-operators 'sub (lambda (x y) (bvsub x y) ))
            (hash-set! builtin-operators 'pow (lambda (x y) (circom-pow x y)))
            (hash-set! builtin-operators 'neg (lambda (x) (bvneg x)))

            ; boolean operators (returns boolean)
            (hash-set! builtin-operators 'lt (lambda (x y) (bvslt x y)))

            ; bitwise operators
            ; ref: https://docs.circom.io/circom-language/basic-operators/#bitwise-operators
            (hash-set! builtin-operators 'band (lambda (x y) (bvand x y)))
            (hash-set! builtin-operators 'shr (lambda (x k) (circom-shr x k)))
            (hash-set! builtin-operators 'shl (lambda (x k) (circom-shl x k)))

        )

    )
)