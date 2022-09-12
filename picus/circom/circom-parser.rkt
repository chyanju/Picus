#lang rosette
(require
    (prefix-in tokamak: "../tokamak.rkt")
    (prefix-in circom: "./circom-grammar.rkt")
)
(provide (all-defined-out))
; (note) all arguments should be concrete; this module doesn't accept any symbolic values

; natural
(define (nat? x) (and (integer? x) (>= x 0)))

; entry point
(define (parse-circom-json arg-node)
    ; start by parsing it as top-level circom
    (tokamak:typed arg-node hash?)
    (parse-circom arg-node)
)

(define (parse-setype arg-node)
    (tokamak:typed arg-node string?)
    (define tmp-v (cond
        [(equal? "Empty" arg-node) 'empty]
        [(equal? "Binary" arg-node) 'binary]
        [(equal? "FieldElement" arg-node) 'fieldelem]
        [else (tokamak:exit "[parse-setype] unsupported setype, got: ~a." arg-node)]
    ))
    ; return
    (circom:setype tmp-v)
)
(define (parse-stype arg-node)
    (tokamak:typed arg-node string?)
    (define tmp-v (cond
        [(equal? "Output" arg-node) 'output]
        [(equal? "Input" arg-node) 'input]
        [(equal? "Intermediate" arg-node) 'intermediate]
        [else (tokamak:exit "[parse-stype] unsupported stype, got: ~a." arg-node)]
    ))
    ; return
    (circom:stype tmp-v)
)

(define (parse-signal arg-node)
    (tokamak:typed arg-node list?)
    (when (not (equal? 2 (length arg-node)))
        (tokamak:exit "[parse-signal] signal node needs to have only 2 elements, got: ~a." arg-node))
    (define tmp-v0 (parse-stype (list-ref arg-node 0)))
    (define tmp-v1 (parse-setype (list-ref arg-node 1)))
    ; return
    (circom:signal tmp-v0 tmp-v1)
)

(define (parse-vtype arg-node)
    (define tmp-v (cond
        [(string? arg-node)
            (cond
                [(equal? "Var" arg-node) 'var]
                [(equal? "Component" arg-node) 'comp]
                [else (tokamak:exit "[parse-vtype] unsupported vtype, got: ~a." arg-node)]
            )
        ]
        [(hash? arg-node)
            (when (not (equal? 1 (hash-count arg-node)))
                (tokamak:exit "[parse-vtype] definition node needs to have only 1 key, got: ~a." (hash-count arg-node)))
            (cond
                [(hash-has-key? arg-node 'Signal) (parse-signal (hash-ref arg-node 'Signal))]
                [else (tokamak:exit "[parse-vtype] unsupported signal type, got: ~a." (hash-keys arg-node))]
            )
        ]
        [else (tokamak:exit "[parse-vtype] unsupported node type, got: ~a." arg-node)]
    ))
    ; return
    (circom:vtype tmp-v)
)

(define (parse-version arg-node)
    (tokamak:typed arg-node list?)
    (when (not (equal? 3 (length arg-node)))
        (tokamak:exit "[parse-version] version node needs to have only 3 elements, got: ~a." arg-node))
    (define tmp-v0 (let ([node0 (list-ref arg-node 0)])
        (tokamak:typed node0 nat?)
        node0
    ))
    (define tmp-v1 (let ([node0 (list-ref arg-node 1)])
        (tokamak:typed node0 nat?)
        node0
    ))
    (define tmp-v2 (let ([node0 (list-ref arg-node 2)])
        (tokamak:typed node0 nat?)
        node0
    ))
    ; return
    (circom:version tmp-v0 tmp-v1 tmp-v2)
)

; (fixme) haven't seen a string cases, only the expreesion case
(define (parse-access arg-node)
    (tokamak:typed arg-node hash?)
    (when (not (equal? 1 (hash-count arg-node)))
        (tokamak:exit "[parse-access] access node needs to have only 1 key, got: ~a." (hash-count arg-node)))
    (define tmp-v (cond
        [(hash-has-key? arg-node 'ArrayAccess) (parse-expression (hash-ref arg-node 'ArrayAccess))]
        [(hash-has-key? arg-node 'ComponentAccess) (let ([node0 (hash-ref arg-node 'ComponentAccess)])
            (tokamak:typed node0 string?)
            node0
        )]
        [else (tokamak:exit "[parse-access] unsupported access type, got: ~a." (hash-keys arg-node))]
    ))
    ; return
    (circom:access tmp-v)
)

(define (parse-assignop arg-node)
    (tokamak:typed arg-node string?)
    (define tmp-v (cond
        [(equal? "AssignVar" arg-node) 'var]
        [(equal? "AssignSignal" arg-node) 'sig]
        [(equal? "AssignConstraintSignal" arg-node) 'csig]
        [else (tokamak:exit "[parse-assignop] unsupported assignop, got: ~a." arg-node)]
    ))
    ; return
    (circom:assignop tmp-v)
)

(define (parse-infixop arg-node)
    (tokamak:typed arg-node string?)
    (define tmp-v (cond
        [(equal? "Mul" arg-node) 'mul]
        [(equal? "Div" arg-node) 'div]
        [(equal? "Add" arg-node) 'add]
        [(equal? "Sub" arg-node) 'sub]
        [(equal? "Pow" arg-node) 'pow]
        [(equal? "IntDiv" arg-node) 'intdiv]
        [(equal? "Mod" arg-node) 'mod]
        [(equal? "ShiftL" arg-node) 'shl]
        [(equal? "ShiftR" arg-node) 'shr]
        [(equal? "LesserEq" arg-node) 'leq]
        [(equal? "GreaterEq" arg-node) 'geq]
        [(equal? "Lesser" arg-node) 'lt]
        [(equal? "Greater" arg-node) 'gt]
        [(equal? "Eq" arg-node) 'eq]
        [(equal? "NotEq" arg-node) 'neq]
        [(equal? "BoolOr" arg-node) 'or]
        [(equal? "BoolAnd" arg-node) 'and]
        [(equal? "BitOr" arg-node) 'bor]
        [(equal? "BitAnd" arg-node) 'band]
        [(equal? "BitXor" arg-node) 'bxor]
        [else (tokamak:exit "[parse-infixop] unsupported infixop, got: ~a." arg-node)]
    ))
    ; return
    (circom:infixop tmp-v)
)

(define (parse-prefixop arg-node)
    (tokamak:typed arg-node string?)
    (define tmp-v (cond
        [(equal? "Sub" arg-node) 'neg] ; (note) to not confuse with subtraction in infix op, we use 'neg for negation here
        [(equal? "BoolNot" arg-node) 'not]
        [(equal? "Complement" arg-node) 'comp]
        [else (tokamak:exit "[parse-prefixop] unsupported prefixop, got: ~a." arg-node)]
    ))
    ; return
    (circom:prefixop tmp-v)
)

(define (parse-treduction arg-node)
    (tokamak:typed arg-node string?)
    (define tmp-v (cond
        [(equal? "Variable" arg-node) 'var]
        [(equal? "Component" arg-node) 'comp]
        [(equal? "Signal" arg-node) 'sig]
        [else (tokamak:exit "[parse-treduction] unsupported treduction, got: ~a." arg-node)]
    ))
    ; return
    (circom:treduction tmp-v)
)

(define (parse-fileloc arg-node)
    (tokamak:typed arg-node hash?)
    (define tmp-start (let ([node0 (hash-ref arg-node 'start)])
        (tokamak:typed node0 nat?)
        node0
    ))
    (define tmp-end (let ([node0 (hash-ref arg-node 'end)])
        (tokamak:typed node0 nat?)
        node0
    ))
    ; return
    (circom:fileloc tmp-start tmp-end)
)

(define (parse-number arg-node)
    (tokamak:typed arg-node list?)
    (when (not (equal? 2 (length arg-node)))
        (tokamak:exit "[parse-component] component node needs to have only 2 elements, got: ~a." arg-node))
    (define tmp-meta (parse-meta (list-ref arg-node 0)))
    ; (fixme) there are some unknown structures in the actual json, but I know where the value is
    ; (define tmp-v (let ([node0 (list-ref (list-ref (list-ref arg-node 1) 1) 0)])
    ;     (tokamak:typed node0 integer?)
    ;     node0
    ; ))
    (define tmp-v (let ([node0 (list-ref (list-ref arg-node 1) 1)] [nn0 (list-ref arg-node 1)])
        (tokamak:typed node0 list?)
        (tokamak:typed nn0 list?)
        (if (equal? 0 (length node0))
            (list-ref nn0 0)
            (list-ref node0 0)
        )
    ))
    ; return
    (circom:number tmp-meta tmp-v)
)

(define (parse-tknowledge arg-node) null) ; (fixme)
(define (parse-mknowledge arg-node) null) ; (fixme)

(define (parse-meta arg-node)
    (tokamak:typed arg-node hash?)
    (define tmp-elemid (let ([node0 (hash-ref arg-node 'elem_id)])
        (tokamak:typed node0 nat?)
        node0
    ))
    (define tmp-start (let ([node0 (hash-ref arg-node 'start)])
        (tokamak:typed node0 nat?)
        node0
    ))
    (define tmp-end (let ([node0 (hash-ref arg-node 'end)])
        (tokamak:typed node0 nat?)
        node0
    ))
    (define tmp-loc (parse-fileloc (hash-ref arg-node 'location)))
    (define tmp-fileid (let ([node0 (hash-ref arg-node 'file_id)])
        (cond
            ; [(null? node0) null]
            [(equal? 'null node0) null]
            [else
                (tokamak:typed node0 nat?)
                node0
            ]
        )
    ))
    (define tmp-compinf (let ([node0 (hash-ref arg-node 'component_inference)])
        (cond
            ; [(null? node0) null]
            [(equal? 'null node0) null]
            [else
                (tokamak:typed node0 string?)
                node0
            ]
        )
    ))
    (define tmp-tk (parse-tknowledge (hash-ref arg-node 'type_knowledge)))
    (define tmp-mk (parse-mknowledge (hash-ref arg-node 'memory_knowledge)))
    ; return
    (circom:meta tmp-elemid tmp-start tmp-end tmp-loc tmp-fileid tmp-compinf tmp-tk tmp-mk)
)

(define (parse-circom arg-node)
    (tokamak:typed arg-node hash?)
    (define tmp-meta (parse-meta (hash-ref arg-node 'meta)))
    (define tmp-ver (let ([node0 (hash-ref arg-node 'compiler_version)])
        (cond
            ; [(null? node0) null]
            [(equal? 'null node0) null]
            [else (parse-version node0)]
        )
    ))
    (define tmp-incs (for/list ([node0 (hash-ref arg-node 'includes)])
        (tokamak:typed node0 string?)
        node0
    ))
    (define tmp-defs (for/list ([node0 (hash-ref arg-node 'definitions)])
        (parse-definition node0)
    ))
    (define tmp-main (let ([node0 (hash-ref arg-node 'main_component)])
        (cond
            ; [(null? node0) null]
            [(equal? 'null node0) null]
            [else (parse-component node0)]
        )
    ))
    ; return
    (circom:circom tmp-meta tmp-ver tmp-incs tmp-defs tmp-main)
)

(define (parse-component arg-node)
    (tokamak:typed arg-node list?)
    (when (not (equal? 2 (length arg-node)))
        (tokamak:exit "[parse-component] component node needs to have only 2 elements, got: ~a." arg-node))
    (define tmp-public (for/list ([node0 (list-ref arg-node 0)])
        (tokamak:typed node0 string?)
        node0
    ))
    (define tmp-call (parse-expression (list-ref arg-node 1)))
    ; return
    (circom:component tmp-public tmp-call)
)

(define (parse-definition arg-node)
    (tokamak:typed arg-node hash?)
    (when (not (equal? 1 (hash-count arg-node)))
        (tokamak:exit "[parse-definition] definition node needs to have only 1 key, got: ~a." (hash-count arg-node)))
    (define tmp-v (cond
        [(hash-has-key? arg-node 'Template) (parse-template (hash-ref arg-node 'Template))]
        [(hash-has-key? arg-node 'Function) (parse-function (hash-ref arg-node 'Function))]
        [else (tokamak:exit "[parse-definition] unsupported definition type, got: ~a." (hash-keys arg-node))]
    ))
    ; return
    (circom:definition tmp-v)
)

(define (parse-template arg-node)
    (tokamak:typed arg-node hash?)
    (define tmp-meta (parse-meta (hash-ref arg-node 'meta)))
    (define tmp-name (let ([node0 (hash-ref arg-node 'name)])
        (tokamak:typed node0 string?)
        node0
    ))
    (define tmp-args (for/list ([node0 (hash-ref arg-node 'args)])
        (tokamak:typed node0 string?)
        node0
    ))
    (define tmp-argloc (parse-fileloc (hash-ref arg-node 'arg_location)))
    (define tmp-body (parse-statement (hash-ref arg-node 'body)))
    (define tmp-parallel (let ([node0 (hash-ref arg-node 'parallel)])
        (tokamak:typed node0 boolean?)
        node0
    ))
    ; return
    (circom:template tmp-meta tmp-name tmp-args tmp-argloc tmp-body tmp-parallel)
)

(define (parse-function arg-node)
    (tokamak:typed arg-node hash?)
    (define tmp-meta (parse-meta (hash-ref arg-node 'meta)))
    (define tmp-name (let ([node0 (hash-ref arg-node 'name)])
        (tokamak:typed node0 string?)
        node0
    ))
    (define tmp-args (for/list ([node0 (hash-ref arg-node 'args)])
        (tokamak:typed node0 string?)
        node0
    ))
    (define tmp-argloc (parse-fileloc (hash-ref arg-node 'arg_location)))
    (define tmp-body (parse-statement (hash-ref arg-node 'body)))
    ; return
    (circom:function tmp-meta tmp-name tmp-args tmp-argloc tmp-body)
)

(define (parse-statement arg-node)
    (tokamak:typed arg-node hash?)
    (when (not (equal? 1 (hash-count arg-node)))
        (tokamak:exit "[parse-statement] statement node needs to have only 1 key, got: ~a." (hash-count arg-node)))
    (define tmp-v (cond
        [(hash-has-key? arg-node 'Assert) (parse-assertstmt (hash-ref arg-node 'Assert))]
        [(hash-has-key? arg-node 'Return) (parse-retstmt (hash-ref arg-node 'Return))]
        [(hash-has-key? arg-node 'IfThenElse) (parse-itestmt (hash-ref arg-node 'IfThenElse))]
        [(hash-has-key? arg-node 'While) (parse-whilestmt (hash-ref arg-node 'While))]
        [(hash-has-key? arg-node 'ConstraintEquality) (parse-ceqstmt (hash-ref arg-node 'ConstraintEquality))]
        [(hash-has-key? arg-node 'Block) (parse-block (hash-ref arg-node 'Block))]
        [(hash-has-key? arg-node 'InitializationBlock) (parse-initblock (hash-ref arg-node 'InitializationBlock))]
        [(hash-has-key? arg-node 'Declaration) (parse-declstmt (hash-ref arg-node 'Declaration))]
        [(hash-has-key? arg-node 'Substitution) (parse-substmt (hash-ref arg-node 'Substitution))]
        [else (tokamak:exit "[parse-statement] unsupported statement type, got: ~a." (hash-keys arg-node))]
    ))
    ; return
    (circom:statement tmp-v)
)

(define (parse-itestmt arg-node)
    (tokamak:typed arg-node hash?)
    (define tmp-meta (parse-meta (hash-ref arg-node 'meta)))
    (define tmp-cond (parse-expression (hash-ref arg-node 'cond)))
    (define tmp-if (parse-statement (hash-ref arg-node 'if_case)))
    (define tmp-else (let ([node0 (hash-ref arg-node 'else_case)])
        (cond
            ; [(null? node0) null]
            [(equal? 'null node0) null]
            [else (parse-statement node0)]
        )
    ))
    ; return
    (circom:itestmt tmp-meta tmp-cond tmp-if tmp-else)
)

(define (parse-whilestmt arg-node)
    (tokamak:typed arg-node hash?)
    (define tmp-meta (parse-meta (hash-ref arg-node 'meta)))
    (define tmp-cond (parse-expression (hash-ref arg-node 'cond)))
    (define tmp-stmt (parse-statement (hash-ref arg-node 'stmt)))
    ; return
    (circom:whilestmt tmp-meta tmp-cond tmp-stmt)
)

(define (parse-retstmt arg-node)
    (tokamak:typed arg-node hash?)
    (define tmp-meta (parse-meta (hash-ref arg-node 'meta)))
    (define tmp-val (parse-expression (hash-ref arg-node 'value)))
    ; reuturn
    (circom:retstmt tmp-meta tmp-val)
)

(define (parse-declstmt arg-node)
    (tokamak:typed arg-node hash?)
    (define tmp-meta (parse-meta (hash-ref arg-node 'meta)))
    (define tmp-xtype (parse-vtype (hash-ref arg-node 'xtype)))
    (define tmp-name (let ([node0 (hash-ref arg-node 'name)])
        (tokamak:typed node0 string?)
        node0
    ))
    (define tmp-dims (for/list ([node0 (hash-ref arg-node 'dimensions)])
        (parse-expression node0)
    ))
    (define tmp-constant (let ([node0 (hash-ref arg-node 'is_constant)])
        (tokamak:typed node0 boolean?)
        node0
    ))
    ; return
    (circom:declstmt tmp-meta tmp-xtype tmp-name tmp-dims tmp-constant)
)

(define (parse-substmt arg-node)
    (tokamak:typed arg-node hash?)
    (define tmp-meta (parse-meta (hash-ref arg-node 'meta)))
    (define tmp-var (let ([node0 (hash-ref arg-node 'var)])
        (tokamak:typed node0 string?)
        node0
    ))
    (define tmp-access (for/list ([node0 (hash-ref arg-node 'access)])
        (parse-access node0)
    ))
    (define tmp-op (parse-assignop (hash-ref arg-node 'op)))
    (define tmp-rhe (parse-expression (hash-ref arg-node 'rhe)))
    ; return
    (circom:substmt tmp-meta tmp-var tmp-access tmp-op tmp-rhe)
)

(define (parse-ceqstmt arg-node)
    (tokamak:typed arg-node hash?)
    (define tmp-meta (parse-meta (hash-ref arg-node 'meta)))
    (define tmp-lhe (parse-expression (hash-ref arg-node 'lhe)))
    (define tmp-rhe (parse-expression (hash-ref arg-node 'rhe)))
    ; return
    (circom:ceqstmt tmp-meta tmp-lhe tmp-rhe)
)


(define (parse-logcallstmt arg-node) (tokamak:exit "[~a] not implemented." (current-namespace)))

(define (parse-assertstmt arg-node)
    (tokamak:typed arg-node hash?)
    (define tmp-meta (parse-meta (hash-ref arg-node 'meta)))
    (define tmp-arg (parse-expression (hash-ref arg-node 'arg)))
    ; return
    (circom:assertstmt tmp-meta tmp-arg)
)

(define (parse-initblock arg-node)
    (tokamak:typed arg-node hash?)
    (define tmp-meta (parse-meta (hash-ref arg-node 'meta)))
    (define tmp-xtype (parse-vtype (hash-ref arg-node 'xtype)))
    (define tmp-inits (for/list ([node0 (hash-ref arg-node 'initializations)])
        (parse-statement node0)
    ))
    ; return 
    (circom:initblock tmp-meta tmp-xtype tmp-inits)
)

(define (parse-block arg-node)
    (tokamak:typed arg-node hash?)
    (define tmp-meta (parse-meta (hash-ref arg-node 'meta)))
    (define tmp-stmts (for/list ([node0 (hash-ref arg-node 'stmts)])
        (parse-statement node0)
    ))
    ; return
    (circom:block tmp-meta tmp-stmts)
)

(define (parse-expression arg-node)
    (tokamak:typed arg-node hash?)
    (when (not (equal? 1 (hash-count arg-node)))
        (tokamak:exit "[parse-expression] expression node needs to have only 1 key, got: ~a." (hash-count arg-node)))
    (define tmp-v (cond
        [(hash-has-key? arg-node 'ArrayInLine) (parse-arrayinline (hash-ref arg-node 'ArrayInLine))]
        [(hash-has-key? arg-node 'InlineSwitchOp) (parse-inlineswitch (hash-ref arg-node 'InlineSwitchOp))]
        [(hash-has-key? arg-node 'InfixOp) (parse-infix (hash-ref arg-node 'InfixOp))]
        [(hash-has-key? arg-node 'PrefixOp) (parse-prefix (hash-ref arg-node 'PrefixOp))]
        [(hash-has-key? arg-node 'Variable) (parse-variable (hash-ref arg-node 'Variable))]
        [(hash-has-key? arg-node 'Call) (parse-call (hash-ref arg-node 'Call))]
        [(hash-has-key? arg-node 'Number) (parse-number (hash-ref arg-node 'Number))]
        [else (tokamak:exit "[parse-expression] unsupported expression type, got: ~a." (hash-keys arg-node))]
    ))
    ; return
    (circom:expression tmp-v)
)

(define (parse-infix arg-node)
    (tokamak:typed arg-node hash?)
    (define tmp-meta (parse-meta (hash-ref arg-node 'meta)))
    (define tmp-lhe (parse-expression (hash-ref arg-node 'lhe)))
    (define tmp-op (parse-infixop (hash-ref arg-node 'infix_op)))
    (define tmp-rhe (parse-expression (hash-ref arg-node 'rhe)))
    ; return
    (circom:infix tmp-meta tmp-lhe tmp-op tmp-rhe)
)

(define (parse-prefix arg-node)
    (tokamak:typed arg-node hash?)
    (define tmp-meta (parse-meta (hash-ref arg-node 'meta)))
    (define tmp-op (parse-prefixop (hash-ref arg-node 'prefix_op)))
    (define tmp-rhe (parse-expression (hash-ref arg-node 'rhe)))
    ; return
    (circom:prefix tmp-meta tmp-op tmp-rhe)
)

(define (parse-inlineswitch arg-node)
    (tokamak:typed arg-node hash?)
    (define tmp-meta (parse-meta (hash-ref arg-node 'meta)))
    (define tmp-cond (parse-expression (hash-ref arg-node 'cond)))
    (define tmp-true (parse-expression (hash-ref arg-node 'if_true)))
    (define tmp-false (parse-expression (hash-ref arg-node 'if_false)))
    ; return
    (circom:inlineswitch tmp-meta tmp-cond tmp-true tmp-false)
)

(define (parse-variable arg-node)
    (tokamak:typed arg-node hash?)
    (define tmp-meta (parse-meta (hash-ref arg-node 'meta)))
    (define tmp-name (let ([node0 (hash-ref arg-node 'name)])
        (tokamak:typed node0 string?)
        node0
    ))
    (define tmp-access (for/list ([node0 (hash-ref arg-node 'access)])
        (parse-access node0)
    ))
    ; return
    (circom:variable tmp-meta tmp-name tmp-access)
)

(define (parse-call arg-node)
    (tokamak:typed arg-node hash?)
    (define tmp-meta (parse-meta (hash-ref arg-node 'meta)))
    (define tmp-id (let ([node0 (hash-ref arg-node 'id)])
        (tokamak:typed node0 string?)
        node0
    ))
    (define tmp-args (for/list ([node0 (hash-ref arg-node 'args)])
        (parse-expression node0)
    ))
    ; return
    (circom:call tmp-meta tmp-id tmp-args)
)
(define (parse-arrayinline arg-node)
    (tokamak:typed arg-node hash?)
    (define tmp-meta (parse-meta (hash-ref arg-node 'meta)))
    (define tmp-vals (for/list ([node0 (hash-ref arg-node 'values)])
        (parse-expression node0)
    ))
    ; return
    (circom:arrayinline tmp-meta tmp-vals)
)
