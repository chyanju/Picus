#lang rosette
(require
    (prefix-in tokamak: "./tokamak.rkt")
    (prefix-in utils: "./utils.rkt")
    (prefix-in config: "./config.rkt")
    (prefix-in circom: "./circom-grammar.rkt")
)
(provide (all-defined-out))

(define vm%
    (class object%
        (super-new)
        (field
            [variable-book null] ; variable book is the top-level scope
            [template-book null] ; stores all templates and functions
            [circom-root null] ; the top-level node, if you want to start, go with the list of components
            [builtin-operators null] ; stores all builtin operators
        )

        (define/public (initialize)
            (set! variable-book (make-hash))
            (set! template-book (make-hash))
            (init-builtin-operators); initialize all builtin operators
        )

        ; (concrete:top) arg-node
        (define/public (deploy arg-node)
            (do-deploy arg-node)
        )

        ; store all the templates into template book
        ; (concrete:top) arg-node
        (define (do-deploy arg-node)
            (match arg-node
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
        (define/public (interpret arg-node)
            (do-interpret arg-node "")
        )

        (define (do-interpret arg-node arg-prefix)
            (tokamak:typed arg-node circom:lang?)

            (match arg-node

                [(circom:setype v)
                    (tokamak:log "circom:setype")
                ]

                [(circom:stype v)
                    (tokamak:log "circom:stype")
                ]

                [(circom:signal first second)
                    (tokamak:log "circom:signal")
                ]

                [(circom:vtype v)
                    (tokamak:log "circom:vtype")
                ]

                [(circom:access v)
                    (tokamak:log "circom:access")
                ]

                [(circom:assignop v)
                    (tokamak:log "circom:assignop")
                ]

                [(circom:infixop v)
                    (tokamak:log "circom:infixop")
                ]

                [(circom:prefixop v)
                    (tokamak:log "circom:prefixop")
                ]

                [(circom:circom m-meta m-ver m-incs m-defs m-main)
                    (tokamak:log "circom:circom")
                    (when (! (null? m-main))
                        (do-interpret m-main arg-prefix)
                    )
                ]

                [(circom:component m-public m-call)
                    (tokamak:log "circom:component")
                    (do-interpret m-call (string-append arg-prefix "main"))
                ]

                [(circom:template m-meta m-name m-args m-argloc m-body m-parallel)
                    (tokamak:exit "[do-interpret] [template.0] a template node should not be directly interpreted.")
                ]

                ; pass on
                [(circom:statement v)
                    (tokamak:log "circom:statement")
                    (do-interpret v arg-prefix)
                ]

                [(circom:itestmt m-meta m-cond m-if m-else)
                    (tokamak:log "circom:itestmt")
                ]

                ; (note) it seems that the while construct here doesn't open up new scope
                [(circom:whilestmt m-meta m-cond m-stmt)
                    (tokamak:log "circom:whilestmt")
                ]

                [(circom:retstmt m-meta m-val)
                    (tokamak:log "circom:retstmt")
                ]

                ; this creates new symbolic variables
                ; (fixme) you need to properly deal with dims
                [(circom:declstmt m-meta m-xtype m-name m-dims m-constant)
                    (tokamak:log "circom:declstmt")
                ]

                ; this creates assertions
                ; (fixme) you need to properly deal with access
                [(circom:substmt m-meta m-var m-access m-op m-rhe)
                    (tokamak:log "circom:substmt")
                ]

                [(circom:ceqstmt m-meta m-lhe m-rhe)
                    (tokamak:log "circom:ceqstmt")
                ]

                [(circom:assertstmt m-meta m-arg)
                    (tokamak:log "circom:assertstmt")
                ]

                [(circom:block m-meta m-stmts)
                    (tokamak:log "circom:block")
                    (for/last ([s m-stmts])
                        (do-interpret s arg-prefix)
                    )
                ]

                [(circom:initblock m-meta m-xtype m-inits)
                    (tokamak:log "circom:initblock")
                    (for/last ([i m-inits])
                        (do-interpret i arg-prefix)
                    )
                ]

                ; pass on
                [(circom:expression v)
                    (tokamak:log "circom:expression")
                    (do-interpret v arg-prefix)
                ]

                [(circom:call m-meta m-id m-args)
                    (tokamak:log "circom:call")
                    ; grab args
                    (define tmp-args (for/list ([arg m-args])
                        (do-interpret arg arg-prefix)
                    ))
                    ; call and return
                    ; (note) this should switch to call prefix, don't use the original prefix
                    (call-template m-id tmp-args arg-prefix)
                ]

                [(circom:infix m-meta m-lhe m-op m-rhe)
                    (tokamak:log "circom:infix")
                ]

                [(circom:prefix m-meta m-op m-rhe)
                    (tokamak:log "circom:prefix")
                ]

                [(circom:inlineswitch m-meta m-cond m-true m-false)
                    (tokamak:log "circom:inlineswitch")
                ]

                [(circom:number m-meta v)
                    (tokamak:log "circom:number")
                ]

                ; (fixme) you need to properly deal with access
                [(circom:variable m-meta m-name m-access)
                    (tokamak:log "circom:variable")
                ]

                [(circom:arrayinline m-meta m-vals)
                    (tokamak:log "circom:arrayinline")
                ]

                [null (tokamak:log "circom:null")]

                [_ (tokamak:exit "[do-interpret] unsupported node, got: ~a." arg-node)]
            )
        )

        (define/public (call-template arg-name arg-args arg-prefix)
            (tokamak:log "call-template: ~a, prefix: ~a" arg-name arg-prefix)
            ; fetch template node
            (define tmp-template (hash-ref template-book arg-name))
            (cond
                [(circom:template? tmp-template)
                    (define tmp-args (circom:template-args tmp-template))
                    (define tmp-body (circom:template-body tmp-template))
                    ; check arity
                    (when (! (= (length tmp-args) (length arg-args)))
                        (tokamak:error "[call-template] argument arities mismatch."))
                    ; call
                    (do-interpret tmp-body arg-prefix)
                ]
                [(circom:function? tmp-template)
                    (tokamak:error "not implemented")
                ]
                [else (tokamak:error "[call-template] you can't reach here.")]
            )
        )

        (define (init-builtin-operators)
            ; (note) (fixme) all arguments should be concrete, you are not checking them all
            (set! builtin-operators (make-hash))
        )

    )
)