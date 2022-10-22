#lang rosette
(require json
    (prefix-in tokamak: "./tokamak.rkt")
    (prefix-in r1cs: "./r1cs/r1cs-grammar.rkt")
)
(provide (rename-out
    [read-precondition read-precondition]
))

; parse the json precondition into program in r1cs grammar
; (note) you should provide each piece of precondition, not the entire json
(define (parse-precondition arg-json)
    (match arg-json
        ; language component
        [(list "rassert" v) (r1cs:rassert (parse-precondition v))]
        [(list "rneq" lhs rhs) (r1cs:rneq (parse-precondition lhs) (parse-precondition rhs))]
        [(list "req" lhs rhs) (r1cs:req (parse-precondition lhs) (parse-precondition rhs))]
        [(list "rmul" vs) (r1cs:rmul (for/list ([v vs]) (parse-precondition v)))]
        [(list "rmod" lhs rhs) (r1cs:rmod (parse-precondition lhs) (parse-precondition rhs))]
        [(list "rvar" v) (r1cs:rvar v)] ; make sure v is a string
        [(list "rint" v) (r1cs:rint v)] ; make sure v is a number/integer

        ; (note) each precondition is only one rassert command, don't include rcmds
        [_ (tokamak:error "unsupported precondition form, got: ~a." arg-json)]
    )
)

; returns:
;   - (values unique-set pres), where
;     - unique-set: a set of assumed unique signals
;     - pres: list of (tag r1cs command)
;             where r1cs command is a single command with not rcmds wrapper
(define (read-precondition arg-path)
    (define pre-json (string->jsexpr (file->string arg-path)))

    (define unique-json (filter (lambda (x) (equal? "unique" (car x))) pre-json))
    (define cmd-json (filter (lambda (x) (! (equal? "unique" (car x)))) pre-json))

    ; process the unique set
    (define unique-set (list->set (filter (lambda (x) (! (equal? "unique" x))) (flatten unique-json))))

    ; process precondition
    (define pres (for/list ([v cmd-json])
        (when (! (= 2 (length v)))
            (tokamak:error "precondition entry should contain exactly 2 elements, got: ~a." v))
        (cons (list-ref v 0) (parse-precondition (list-ref v 1)))
    ))

    (values unique-set pres)
)