(set-logic QF_NIA)
(declare-const p Int)
(assert (= p 21888242871839275222246405745257275088548364400416034343698204186575808495617))

(declare-const x10 Int)
(assert (and (<= 0 x10) (< x10 p)))

; we want to prove ( 1 + (p-b) * x10 ) != 0
; so we need to find a counter-example
(assert (= 0 (mod (+ 1 (* (- p 168696) x10)) p)))

; block
(assert (not (= x10 5950707087489713327630097374536055433359970814342252235411810230289552242107)))

(check-sat)
(get-model)