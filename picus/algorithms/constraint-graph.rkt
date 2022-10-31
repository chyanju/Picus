#lang racket
(require graph csv-reading
    (prefix-in tokamak: "../tokamak.rkt")
    (prefix-in r1cs: "../r1cs/r1cs-grammar.rkt")
)
(provide (all-defined-out))

; constraint graph
;   - g: graph object
;   - e2c: hash, edge to constraint id, key is a set of signals, val is a set of constraint ids
;   - s2o: vector, signal to order
;   - s2s: vector, signal to scope
;   - o2s: vector, order to scope
(struct cgraph (g e2c s2o s2s o2s) #:mutable #:transparent #:reflection-name 'cgraph) ; constraint graph

(define (extract-signal-id x) (string->number (substring x 1)))

; scope is a set e.g.  (set "adder" "main")
(define (read-sym path-sym)
    (define rd (csv->list (open-input-file path-sym)))
    ; sym file doesn't have x0, so you need to manually add it
    (define n-signals (+ 1 (length rd)))

    ; 3rd column, could be topological order?
    ; module order vector
    (define order-vec (make-vector n-signals null))
    ; scope vector
    (define scope-vec (make-vector n-signals null))

    ; parse module order and scope
    ; no x0 is included in sym, so minus 1
    (define ospairs (list ))
    (for ([i (range (- n-signals 1))])
        (define sid (+ 1 i)) ; shift, start from signal 1
        (define entry (list-ref rd i))
        ; parse order
        (define order (string->number (list-ref entry 2)))
        (vector-set! order-vec sid order)
        ; parse scope, drop the last element since that's not a scope
        (define scope (list->set (cdr (reverse (string-split (list-ref entry 3) ".")))))
        (vector-set! scope-vec sid scope)
        ; track os pairs
        (set! ospairs (cons (cons order scope) ospairs))
    )
    (set! ospairs (set->list (list->set ospairs))) ; remove duplicates

    ; set order and scope of x0
    ; just copy from signal 1
    (vector-set! order-vec 0 (vector-ref order-vec 1))
    (vector-set! scope-vec 0 (vector-ref scope-vec 1))

    ; (todo) verify order-scope mapping is unique
    (define nos (length ospairs))
    (define os-hash (make-hash ospairs))
    (when (not (equal? nos (hash-count os-hash)))
        (tokamak:exit "something is wrong with the sym file, ospairs: ~a" ospairs))
    (define os-vec (build-vector nos (lambda (x) (hash-ref os-hash x))))

    ; return
    ;   - order-vec: signal to order mapping, s2o
    ;   - scope-vec: signal to scope mapping, s2s
    ;   - os-vec: order to signal mapping, o2s
    (values order-vec scope-vec os-vec)
)

; requires p1cnsts, no constraint id change after that
(define (compute-constraint-graph r0 arg-r1cs path-sym)
    (define input-list (r1cs:r1cs-inputs r0))
    (define output-list (r1cs:r1cs-outputs r0))

    ; read sym file
    (define-values (order-vec scope-vec os-vec) (read-sym path-sym))

    ; constraint graph
    (define g (undirected-graph (list )))

    (define vs (r1cs:rcmds-vs arg-r1cs))
    (define n-edges (length vs))
    (define n-nodes (r1cs:get-nwires r0))
    ; first add all signals as vertices
    (for ([i (range n-nodes)]) (add-vertex! g i))

    ; then define e2c-map
    (define e2c-map (make-hash))

    ; then add edges
    (for ([i (range n-edges)])
        (define cnst (list-ref vs i))
        (define asvs (r1cs:get-assert-variables cnst #t)) ; get all involving signals
        ; add edges
        (for ([b (combinations (set->list asvs) 2)])
            (define node0 (list-ref b 0))
            (define node1 (list-ref b 1))
            (add-edge! g node0 node1) ; good enough, will automatically convert to bi-direct.
            ; set label to constraint id, need to set for both directions
            (define ek (set node0 node1)) ; key
            (when (not (hash-has-key? e2c-map ek))
                (hash-set! e2c-map ek (set )))
            (hash-set! e2c-map ek (set-add (hash-ref e2c-map ek) i))
        )
    )

    ; construct and return cgraph
    (cgraph g e2c-map order-vec scope-vec os-vec)
)

; arguments:
;   - arg-connections: a set of extra signals that *could* be included
;                      this set is usually global inputs/outputs, connecting nodes, etc
;                      (note) only those connected to the target scope will be there, others removed
;                      this just makes some suggestions
; returns:
;   - a new copy of subgraph (still wrapped in cgraph)
;   - (fixme) only changes the graph, but other components remain the same
(define (get-scoped-subgraph arg-graph arg-scope arg-connections)
    (define g (graph-copy (cgraph-g arg-graph))) ; make a copy
    (define scope-vec (cgraph-s2s arg-graph))
    ; get candidate signal ids
    (define scope-sids (list->set (filter
        (lambda (x) (equal? arg-scope (vector-ref scope-vec x)))
        (range (vector-length scope-vec))
    )))
    (define all-sids (set-union scope-sids arg-connections))
    ; then delete the nodes that are out of given scope
    (for ([node (get-vertices g)])
        (when (not (set-member? all-sids node))
            (remove-vertex! g node))
    )
    ; then, remove those nodes without any neighbors
    (for ([node (get-vertices g)])
        (when (empty? (get-neighbors g node))
            (remove-vertex! g node))
    )
    ; return
    (cgraph
        g
        (cgraph-e2c arg-graph)
        (cgraph-s2o arg-graph)
        (cgraph-s2s arg-graph)
        (cgraph-o2s arg-graph)
    )
)