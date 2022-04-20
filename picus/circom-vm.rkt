#lang rosette
(require rosette/lib/destruct) ; match syntax in rosette
(require "./tokamak.rkt")
(require "./mhash.rkt")
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

            ; default setting
            [scope-cap 100]
        )

        ; concrete
        ; also do initializations
        (define/public (deploy arg-node)
            (set! variable-book (make-mhash scope-cap))
            (set! template-book (make-hash))
            (init-builtin-operators); initialize all builtin operators
            (do-deploy arg-node)
        )

        ; concrete
        ; store all the templates into template book
        (define (do-deploy arg-node)
            (destruct arg-node
                [(circom:circom m-meta m-version m-includes m-definitions m-components)
                    ; set root node
                    (set! circom-root arg-node)
                    ; continue to find out all template definitions
                    (for ([node0 m-definitions])
                        (do-deploy node0)
                    )
                ]

                [(circom:template m-meta m-name m-args m-argloc m-body)
                    ; add template definition
                    (hash-set! template-book m-name arg-node)
                ]

                [_ (tokamak:exit "[do-deploy] unsupported node, got: ~a." arg-node)]
            )
        )

        ; symbolic
        (define/public (interpret arg-node)
            ; first clear all stateful vars
            (set! input-book (make-hash))
            (set! output-book (make-hash))
            (do-interpret arg-node (list variable-book) "")
        )

        ; symbolic
        ; (note) this procedure assumes all input nodes are well typed; see grammar for typing
        ; arg-scopes: a stacked list of scopes
        ; arg-prefix: the prefix attached to every variable interacted (esp. when applied to template)
        (define (do-interpret arg-node arg-scopes arg-prefix)
            (for*/all ([scopes0 arg-scopes #:exhaustive] [prefix0 arg-prefix #:exhaustive])
                (tokamak:typed scopes0 list?)
                (tokamak:typed prefix0 string?)
                (destruct arg-node

                    [(circom:circom m-meta m-version m-includes m-definitions m-components)
                        ; (fixme) definitions should be processed and stored using the deploy procedure
                        ;         is this true?
                        (for/all ([components0 m-components #:exhaustive])
                            (tokamak:typed components0 list?)
                            (for ([c components0])
                                (for/all ([c0 c #:exhaustive])
                                    ; (fixme) this can only be "main" here
                                    (do-interpret c0 scopes0 (string-append "main." prefix0))
                                )
                            )
                        )
                    ]

                    [(circom:template m-meta m-name m-args m-argloc m-body)
                        (tokamak:exit "[do-interpret] a template node should not be directly interpreted.")
                    ]

                    ; this creates new symbolic variables
                    [(circom:declaration m-meta m-name m-constant m-xtype m-dimensions)
                        (for*/all ([name0 m-name #:exhaustive] [xtype0 m-xtype #:exhaustive])
                            (tokamak:typed name0 string?)
                            (tokamak:typed xtype0 circom:signal?)
                            ; (fixme) you may want to interpret the specific xtype info to determine the type
                            ; dynamically create symbolic variable
                            (define vname (string-append prefix0 name0))
                            (define sym (tokamak:symbolic* (string->symbol vname) 'integer))
                            ; register in the scope
                            (make-var scopes0 vname sym)
                            ; update states
                            (define signal-type (circom:signal-s xtype0))
                            (cond
                                [(equal? 'output signal-type) (hash-set! input-book vname sym)]
                                [(equal? 'input signal-type) (hash-set! output-book vname sym)]
                                [else (tokamak:exit "[do-interpret] unknown signal type, got: ~a." signal-type)]
                            )
                            ; this returns the newly created symbolic variables, sicne caller may want to do type conversion
                            sym
                        )
                    ]

                    ; this creates assertions
                    [(circom:substitution m-meta m-var m-op m-access m-rhe)
                        (for*/all ([rhe0 m-rhe #:exhaustive] [var0 m-var #:exhaustive] [op0 m-op #:exhaustive])
                            (tokamak:typed var0 string?)
                            (tokamak:typed op0 symbol?)
                            (define tmp-rhe (do-interpret rhe0 scopes0 prefix0))
                            (define tmp-var (read-var scopes0 (string-append prefix0 var0))) ; don't forget the prefix
                            (cond
                                [(equal? 'AssignConstraintSignal op0)
                                    (assert (equal? tmp-var tmp-rhe))
                                ]
                                [else (tokamak:exit "[do-interpret] unsupported operator in substitution, got: ~a." op0)]
                            )
                        )
                    ]

                    [(circom:block m-meta m-stmts)
                        (for/all ([stmts0 m-stmts #:exhaustive])
                            (tokamak:typed stmts0 list?)
                            (for ([s stmts0])
                                (for/all ([s0 s #:exhaustive])
                                    (do-interpret s0 scopes0 prefix0)
                                )
                            )
                        )
                    ]

                    [(circom:initblock m-meta m-xtype m-inits)
                        ; (fixme) you may want to interpret the specific xtype info to determine the type
                        (for/all ([inits0 m-inits #:exhaustive])
                            (tokamak:typed inits0 list?)
                            (for ([i inits0])
                                (for/all ([i0 i #:exhaustive])
                                    (do-interpret i0 scopes0 prefix0)
                                )
                            )
                        )
                    ]

                    [(circom:call m-meta m-id m-args)
                        (for*/all ([id0 m-id #:exhaustive] [args0 m-args #:exhaustive])
                            (tokamak:typed id0 string?)
                            (tokamak:typed args0 list?)
                            ; grab args
                            (define tmp-args (for/list ([arg args0])
                                (for/all ([arg0 arg #:exhaustive])
                                    (do-interpret arg0 scopes0 prefix0)
                                )
                            ))
                            ; call and return
                            (call-template scopes0 prefix0 id0 tmp-args)
                        )
                    ]

                    [(circom:infix m-meta m-op m-lhe m-rhe)
                        (for*/all ([lhe0 m-lhe #:exhaustive] [rhe0 m-rhe #:exhaustive] [op0 m-op #:exhaustive])
                            (tokamak:typed op0 symbol?)
                            (define tmp-lhe (do-interpret lhe0 scopes0 prefix0))
                            (define tmp-rhe (do-interpret rhe0 scopes0 prefix0))
                            (define tmp-result (apply (hash-ref builtin-operators op0) (list tmp-lhe tmp-rhe)))
                            tmp-result
                        )
                    ]

                    [(circom:number v)
                        (for/all ([v0 v #:exhaustive])
                            (tokamak:typed v0 number?)
                            ; return
                            v
                        )
                    ]

                    [(circom:signal s e)
                        (tokamak:exit "[do-interpret] a signal node should not be directly interpreted.")
                    ]

                    [(circom:variable m-meta m-name m-access)
                        (for/all ([name0 m-name #:exhaustive])
                            (read-var scopes0 (string-append prefix0 name0))
                        )
                    ]

                    [_ (tokamak:exit "[do-interpret] unsupported node, got: ~a." arg-node)]
                )
            )
        )

        ; symbolic
        (define/public (call-template arg-scopes arg-prefix arg-name arg-args)
            (for*/all ([scopes0 arg-scopes #:exhaustive] [prefix0 arg-prefix #:exhaustive] 
                      [name0 arg-name #:exhaustive] [args0 arg-args #:exhaustive])
                (tokamak:typed scopes0 list?)
                (tokamak:typed prefix0 string?)
                (tokamak:typed name0 string?)
                (tokamak:typed args0 list?)
                (define tmp-template (hash-ref template-book name0)) ; fetch the template node
                (define tmp-args (circom:template-args tmp-template)) ; fetch the template args
                (define tmp-body (circom:template-body tmp-template)) ; fetch the template body
                ; check arity
                (when (not (equal? (length tmp-args) (length args0)))
                    (tokamak:exit "[call-template] argument arities mismatch, template requires ~a, but ~a is provided."
                        (length tmp-args) (length args0)))
                ; create a local scope
                (define local-scope (make-mhash scope-cap))
                ; initialize local scope with argument values
                (for ([local-id tmp-args] [local-val args0])
                    ; (make-var (cons local-scope scopes0) local-id local-val)
                    ; (fixme) ideally local variables from arguments should not have additional prefix
                    ;         but we don't want to spend more efforts separating them, so let's add the prefix
                    ;         for now so it fits the current call model
                    (make-var (cons local-scope scopes0) (string-append prefix0 local-id) local-val)
                )
                ; interpret template body
                (do-interpret tmp-body (cons local-scope scopes0) prefix0)
            )
        )

        ; partly symbolic
        ; create a variable in the nearest scope
        (define (make-var arg-stack arg-id arg-val)
            (tokamak:typed arg-stack list?)
            (tokamak:typed arg-id string?)
            ; arg-val can be symbolic
            (when (null? arg-stack) (tokamak:exit "[make-var] arg-stack is empty."))
            (let ([scope (car arg-stack)])
                (tokamak:typed scope mhash?)
                (mhash-set! scope arg-id arg-val)
            )
        )

        ; concrete
        ; read a variable from the stack of scopes, from nearest to farthest (top)
        (define (read-var arg-stack arg-id)
            (tokamak:typed arg-stack list?)
            (tokamak:typed arg-id string?)
            (let ([scope (car arg-stack)] [stack0 (cdr arg-stack)])
                (tokamak:typed scope mhash?)
                (cond 
                    [(mhash-has-key? scope arg-id)
                        (mhash-ref scope arg-id)
                    ]
                    [(null? stack0)
                        (tokamak:exit "[read-var] cannot find variable in all scopes, got: ~a." arg-id)
                    ]
                    [else
                        (read-var stack0 arg-id)
                    ]
                )
            )
        )

        ; partly symbolic
        ; write a variable to the stack of scopes, nearest first
        ; this requires the variable to exist before writing
        (define (write-var arg-stack arg-id arg-val)
            (tokamak:typed arg-stack list?)
            (tokamak:typed arg-id string?)
            ; arg-val can be symbolic
            (let ([scope (car arg-stack)] [stack0 (cdr arg-stack)])
                (tokamak:typed scope mhash?)
                (cond
                    [(mhash-has-key? scope arg-id)
                        (mhash-set! scope arg-id arg-val)
                    ]
                    [(null? stack0)
                        (tokamak:exit "[write-var] cannot find variable in all scopes, got: ~a." arg-id)
                    ]
                    [else
                        (write-var stack0 arg-id arg-val)
                    ]
                )
            )
        )

        ; concrete
        (define (init-builtin-operators)
            (set! builtin-operators (make-hash))

            (hash-set! builtin-operators 'mul (lambda (x y) (* x y)))
            (hash-set! builtin-operators 'add (lambda (x y) (+ x y)))
        )

    )
)