#lang racket
(require "./tokamak.rkt")
(require "./circom-grammar.rkt")
(provide (all-defined-out))
; (fixme) all fields commented with "null" and "??" need to be concretized later

; entry point
(define (parse-circom-json arg-node)
    ; start by parsing it as top-level circom
    (parse-circom-circom arg-node)
)

(define (parse-circom-circom arg-node)
    (define tmp-meta null)
    (define tmp-version (hash-ref arg-node 'compiler_version))
    (define tmp-includes null)
    (define tmp-definitions (for/list ([node0 (hash-ref arg-node 'definitions)] #:unless (null? node0))
        (when (< 1 (hash-count node0)) 
            (tokamak:exit "[parse-circom-circom] node for definitions has more than 1 keys, got: ~a" (hash-count node0)))
        (cond
            [(hash-has-key? node0 'Template) (parse-circom-template (hash-ref node0 'Template))]
            [else (tokamak:exit "[parse-circom-circom] unsupported node for definitions, got: ~a" node0)]
        )
    ))
    (define tmp-components (for/list ([node0 (hash-ref arg-node 'main_component)] #:unless (null? node0))
        (when (< 1 (hash-count node0)) 
            (tokamak:exit "[parse-circom-circom] node for components has more than 1 keys, got: ~a" (hash-count node0)))
        (cond
            [(hash-has-key? node0 'Call) (parse-circom-call (hash-ref node0 'Call))]
            [else (tokamak:exit "[parse-circom-circom] unsupported node for components, got: ~a" node0)]
        )
    ))
    ; return
    (circom:circom tmp-meta tmp-version tmp-includes tmp-definitions tmp-components)
)

(define (parse-circom-template arg-node)
    (define tmp-meta null)
    (define tmp-name (hash-ref arg-node 'name))
    (define tmp-args (hash-ref arg-node 'args)) ; this is a list of strings already, just refer to it
    (define tmp-argloc null)
    (define tmp-body (let ([node0 (hash-ref arg-node 'body)])
        (when (< 1 (hash-count node0))
            (tokamak:exit "[parse-circom-template] node for body has more than 1 keys, got: ~a" (hash-count node0)))
        (cond
            [(hash-has-key? node0 'Block) (parse-circom-block (hash-ref node0 'Block))]
            [else (tokamak:exit "[parse-circom-template] unsupported node for body, got: ~a" node0)]
        )
    ))
    ; return
    (circom:template tmp-meta tmp-name tmp-args tmp-argloc tmp-body)
)

(define (parse-circom-declaration arg-node)
    (define tmp-meta (hash-ref arg-node 'meta))
    (define tmp-name (hash-ref arg-node 'name))
    (define tmp-constant (hash-ref arg-node 'is_constant))
    (define tmp-xtype (let ([node0 (hash-ref arg-node 'xtype)])
        (when (< 1 (hash-count node0))
            (tokamak:exit "[parse-circom-declaration] node for xtype has more than 1 keys, got: ~a" (hash-count node0)))
        (cond
            [(hash-has-key? node0 'Signal) (parse-circom-signal (hash-ref node0 'Signal))]
            [else (tokamak:exit "[parse-circom-declaration] unsupported node for xtype, got: ~a" node0)]
        )
    ))
    (define tmp-dimensions null)
    ; return
    (circom:declaration tmp-meta tmp-name tmp-constant tmp-xtype tmp-dimensions)
)

(define (parse-circom-substitution arg-node)
    (define tmp-meta (hash-ref arg-node 'meta))
    (define tmp-var (hash-ref arg-node 'var))
    (define tmp-op (let ([node0 (hash-ref arg-node 'op)])
        (cond
            [(equal? "AssignConstraintSignal" node0) 'AssignConstraintSignal]
            [else (tokamak:exit "[parse-circom-substitution] unsupported node for op, got: ~a") node0]
        )
    ))
    (define tmp-access null)
    (define tmp-rhe (let ([node0 (hash-ref arg-node 'rhe)])
        (when (< 1 (hash-count node0))
            (tokamak:exit "[parse-circom-substitution] node for rhe has more than 1 keys, got: ~a" (hash-count node0)))
        (cond
            [(hash-has-key? node0 'InfixOp) (parse-circom-infix (hash-ref node0 'InfixOp))]
            [(hash-has-key? node0 'Variable) (parse-circom-variable (hash-ref node0 'Variable))]
            [else (tokamak:exit "[parse-circom-substitution] unsupported node for rhe, got: ~a" node0)]
        )
    ))
    ; return
    (circom:substitution tmp-meta tmp-var tmp-op tmp-access tmp-rhe)
)

(define (parse-circom-block arg-node)
    (define tmp-meta null)
    (define tmp-stmts (for/list ([node0 (hash-ref arg-node 'stmts)])
        (when (< 1 (hash-count node0)) 
            (tokamak:exit "[parse-circom-block] node for stmts has more than 1 keys, got: ~a" (hash-count node0)))
        (cond
            [(hash-has-key? node0 'InitializationBlock) (parse-circom-initblock (hash-ref node0 'InitializationBlock))]
            [(hash-has-key? node0 'Substitution) (parse-circom-substitution (hash-ref node0 'Substitution))]
            [else (tokamak:exit "[parse-circom-block] unsupported node for stmts, got: ~a" node0)]
        )
    ))
    ; return
    (circom:block tmp-meta tmp-stmts)
)

(define (parse-circom-initblock arg-node)
    (define tmp-meta (hash-ref arg-node 'meta))
    (define tmp-xtype (let ([node0 (hash-ref arg-node 'xtype)])
        (when (< 1 (hash-count node0))
            (tokamak:exit "[parse-circom-initblock] node for xtype has more than 1 keys, got: ~a" (hash-count node0)))
        (cond
            [(hash-has-key? node0 'Signal) (parse-circom-signal (hash-ref node0 'Signal))]
            [else (tokamak:exit "[parse-circom-initblock] unsupported node for xtype, got: ~a" node0)]
        )
    ))
    (define tmp-initializations (for/list ([node0 (hash-ref arg-node 'initializations)])
        (when (< 1 (hash-count node0)) 
            (tokamak:exit "[parse-circom-initblock] node for initializations has more than 1 keys, got: ~a" (hash-count node0)))
        (cond
            [(hash-has-key? node0 'Declaration) (parse-circom-declaration (hash-ref node0 'Declaration))]
            [else (tokamak:exit "[parse-circom-initblock] unsupported node for initializations, got: ~a" node0)]
        )
    ))
    ; return
    (circom:initblock tmp-meta tmp-xtype tmp-initializations)
)

(define (parse-circom-call arg-node)
    (define tmp-meta null)
    (define tmp-id (hash-ref arg-node 'id))
    (define tmp-args (for/list ([node0 (hash-ref arg-node 'args)])
        (when (< 1 (hash-count node0)) 
            (tokamak:exit "[parse-circom-call] node for args has more than 1 keys, got: ~a" (hash-count node0)))
        (cond
            [(hash-has-key? node0 'Number) (parse-circom-number (hash-ref node0 'Number))]
            [else (tokamak:exit "[parse-circom-call] unsupported node for args, got: ~a" node0)]
        )
    ))
    ; return
    (circom:call tmp-meta tmp-id tmp-args)
)

(define (parse-circom-infix arg-node)
    (define tmp-meta null)
    (define tmp-op (let ([node0 (hash-ref arg-node 'infix_op)])
        (cond
            [(equal? "Mul" node0) 'mul]
            [(equal? "Add" node0) 'add]
            [else (tokamak:exit "[parse-circom-infix] unsupported node for op, got: ~a" node0)]
        )
    ))
    (define tmp-lhe (let ([node0 (hash-ref arg-node 'lhe)])
        (when (< 1 (hash-count node0))
            (tokamak:exit "[parse-circom-infix] node for lhe has more than 1 keys, got: ~a" (hash-count node0)))
        (cond
            [(hash-has-key? node0 'InfixOp) (parse-circom-infix (hash-ref node0 'InfixOp))]
            [(hash-has-key? node0 'Variable) (parse-circom-variable (hash-ref node0 'Variable))]
            [else (tokamak:exit "[parse-circom-infix] unsupported node for lhe, got: ~a" node0)]
        )
    ))
    (define tmp-rhe (let ([node0 (hash-ref arg-node 'rhe)])
        (when (< 1 (hash-count node0))
            (tokamak:exit "[parse-circom-infix] node for rhe has more than 1 keys, got: ~a" (hash-count node0)))
        (cond
            [(hash-has-key? node0 'InfixOp) (parse-circom-infix (hash-ref node0 'InfixOp))]
            [(hash-has-key? node0 'Variable) (parse-circom-variable (hash-ref node0 'Variable))]
            [else (tokamak:exit "[parse-circom-infix] unsupported node for rhe, got: ~a" node0)]
        )
    ))
    ; return
    (circom:infix tmp-meta tmp-op tmp-lhe tmp-rhe)
)

; (fixme) not yet sure about the structure of a number node
(define (parse-circom-number arg-node)
    (define tmp-v (list-ref (list-ref (list-ref arg-node 1) 1) 0))
    ; return
    (circom:number tmp-v)
)

(define (parse-circom-signal arg-node)
    (define tmp-s (let ([node0 (list-ref arg-node 0)])
        (cond
            [(equal? "Input" node0) 'input]
            [(equal? "Output" node0) 'output]
            [else (tokamak:exit "[parse-circom-signal] unsupported node for signal type, got: ~a" node0)]
        )
    ))
    (define tmp-e (let ([node0 (list-ref arg-node 1)])
        (cond
            [(equal? "FieldElement" node0) 'field]
            [else (tokamak:exit "[parse-circom-signal] unsupported node for element type, got: ~a" node0)]
        )
    ))
    ; return
    (circom:signal tmp-s tmp-e)
)

(define (parse-circom-variable arg-node)
    (define tmp-meta null)
    (define tmp-name (hash-ref arg-node 'name))
    (define tmp-access null)
    ; return
    (circom:variable tmp-meta tmp-name tmp-access)
)