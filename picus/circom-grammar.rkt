#lang racket
(provide (prefix-out circom: (all-defined-out)))
; (fixme) all fields commented with "null" and "??" need to be concretized later

(struct circom (
    meta ; null
    version ; string
    includes ; null
    definitions ; list of: template | ??
    components ; list of: call | ??
) #:mutable #:transparent #:reflection-name 'circom:circom)

(struct template (
    meta ; null
    name ; (template name) string
    args ; list of: string | ??
    argloc ; null
    body ; block
) #:mutable #:transparent #:reflection-name 'circom:template)

(struct declaration (
    meta ; null
    name ; string
    constant ; bool
    xtype ; signal | ??
    dimensions ; null
) #:mutable #:transparent #:reflection-name 'circom:declaration)

(struct substitution (
    meta ; null
    var ; string
    op ; symbol: 'AssignConstraintSignal | ??
    access ; null
    rhe ; infix | ??
) #:mutable #:transparent #:reflection-name 'circom:substitution)

(struct block (
    meta ; null
    stmts ; list of: initblock | substitution
) #:mutable #:transparent #:reflection-name 'circom:block)

(struct initblock (
    meta ; null
    xtype ; signal | ??
    inits ; list of: declaration | ??
) #:mutable #:transparent #:reflection-name 'circom:initblock)

(struct call (
    meta ; null
    id ; string
    args ; list of: number | ??
) #:mutable #:transparent #:reflection-name 'circom:call)

(struct infix (
    meta ; null
    op ; symbol: 'mul | 'add | ??
    lhe ; infix | ??
    rhe ; infex | ??
) #:mutable #:transparent #:reflection-name 'circom:infix)

(struct number (
    v ; number
) #:mutable #:transparent #:reflection-name 'circom:number)

(struct signal (
    s ; (signal type) symbol: 'input | 'output
    e ; (element type) symbol: 'field | 'binary
) #:mutable #:transparent #:reflection-name 'circom:signal)

(struct variable (
    meta ; null
    name ; string
    access ; null
) #:mutable #:transparent #:reflection-name 'circom:variable)