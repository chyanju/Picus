#lang rosette
(provide (all-defined-out))
; (note) see NOTES.md for transcribed CFG

(struct setype (v) #:mutable #:transparent #:reflection-name 'circom:setype)
(struct stype (v) #:mutable #:transparent #:reflection-name 'circom:stype)
(struct signal (v0 v1) #:mutable #:transparent #:reflection-name 'circom:signal)
(struct vtype (v) #:mutable #:transparent #:reflection-name 'circom:vtype)
(struct version (v0 v1 v2) #:mutable #:transparent #:reflection-name 'circom:version)
(struct access (v) #:mutable #:transparent #:reflection-name 'circom:access)
(struct assignop (v) #:mutable #:transparent #:reflection-name 'circom:assignop)
(struct infixop (v) #:mutable #:transparent #:reflection-name 'circom:infixop)
(struct prefixop (v) #:mutable #:transparent #:reflection-name 'circom:prefixop)
(struct treduction (v) #:mutable #:transparent #:reflection-name 'circom:treduction)
(struct fileloc (start end) #:mutable #:transparent #:reflection-name 'circom:fileloc)

(struct number (meta v) #:mutable #:transparent #:reflection-name 'circom:number)
(struct tknowledge (rto) #:mutable #:transparent #:reflection-name 'circom:tknowledge)
(struct mknowledge (cdims len absmaddr) #:mutable #:transparent #:reflection-name 'circom:mknowledge)
(struct meta (elemid start end loc fileid compinf tk mk) #:mutable #:transparent #:reflection-name 'circom:meta)
(struct circom (meta ver incs defs main) #:mutable #:transparent #:reflection-name 'circom:circom)
(struct component (public call) #:mutable #:transparent #:reflection-name 'circom:component)

(struct definition (v) #:mutable #:transparent #:reflection-name 'circom:definition)
(struct template (meta name args argloc body parallel) #:mutable #:transparent #:reflection-name 'circom:template)
(struct function (meta name args argloc body) #:mutable #:transparent #:reflection-name 'circom:function)

(struct statement (v) #:mutable #:transparent #:reflection-name 'circom:statement)
(struct itestmt (meta cond if else) #:mutable #:transparent #:reflection-name 'circom:itestmt)
(struct whilestmt (meta cond stmt) #:mutable #:transparent #:reflection-name 'circom:whilestmt)
(struct retstmt (meta val) #:mutable #:transparent #:reflection-name 'circom:retstmt)
(struct declstmt (meta xtype name dims constant) #:mutable #:transparent #:reflection-name 'circom:declstmt)
(struct substmt (meta var access op rhe) #:mutable #:transparent #:reflection-name 'circom:declstmt)
(struct ceqstmt (meta lhe rhe) #:mutable #:transparent #:reflection-name 'circom:ceqstmt)
(struct logcallstmt (meta arg) #:mutable #:transparent #:reflection-name 'circom:logcallstmt)
(struct assertstmt (meta arg) #:mutable #:transparent #:reflection-name 'circom:assertstmt)
(struct initblock (meta xtype inits) #:mutable #:transparent #:reflection-name 'circom:initblock)
(struct block (meta stmts) #:mutable #:transparent #:reflection-name 'circom:block)

(struct expression (v) #:mutable #:transparent #:reflection-name 'circom:expression)
(struct infix (meta lhe op rhe) #:mutable #:transparent #:reflection-name 'circom:infix)
(struct prefix (meta op rhe) #:mutable #:transparent #:reflection-name 'circom:prefix)
(struct inlineswitch (meta cond true false) #:mutable #:transparent #:reflection-name 'circom:inlineswitch)
(struct variable (meta name access) #:mutable #:transparent #:reflection-name 'circom:variable)
(struct call (meta id args) #:mutable #:transparent #:reflection-name 'circom:call)
(struct arrayinline (meta vals) #:mutable #:transparent #:reflection-name 'circom:arrayinline)

; tells whether x falls into one of the circom grammar structs
(define (lang? x)
    (or 
        (setype? x) (stype? x) (signal? x) (vtype? x) (version? x) (access? x) (assignop? x)
        (infixop? x) (prefixop? x) (treduction? x) (fileloc? x)
        (number? x) (tknowledge? x) (mknowledge? x) (meta? x) (circom? x) (component? x)
        (definition? x) (template? x) (function? x)
        (statement? x) (itestmt? x) (whilestmt? x) (retstmt? x) (declstmt? x) (substmt? x)
        (ceqstmt? x) (logcallstmt? x) (assertstmt? x) (initblock? x) (block? x)
        (expression? x) (infix? x) (prefix? x) (inlineswitch? x) (variable? x) (call? x) (arrayinline? x)
    )
)

(define (setype:terminal? x) (or
    (equal? 'empty x) (equal? 'binary x) (equal? 'fieldelem x)
))

(define (stype:terminal? x) (or
    (equal? 'output x) (equal? 'input x) (equal? 'intermediate x)
))

(define (vtype:terminal? x) (or
    (equal? 'var x) (equal? 'comp x) (signal? x)
))

(define (assignop:terminal? x) (or
    (equal? 'var x) (equal? 'sig x) (equal? 'csig x)
))

(define (infixop:terminal? x) (or
    (equal? 'mul x) (equal? 'div x) (equal? 'add x) (equal? 'sub x) (equal? 'pow x) (equal? 'intdiv x)
    (equal? 'mod x) (equal? 'shl x) (equal? 'shr x) (equal? 'leq x) (equal? 'geq x) (equal? 'lt x)
    (equal? 'gt x) (equal? 'eq x) (equal? 'neq x) (equal? 'or x) (equal? 'and x) (equal? 'bor x)
    (equal? 'band x) (equal? 'bxor x)
))

(define (prefixop:terminal? x) (or
    (equal? 'neg x) (equal? 'not x) (equal? 'comp x)
))

(define (treduction:terminal x) (or
    (equal? 'var x) (equal? 'comp x) (equal? 'sig x)
))