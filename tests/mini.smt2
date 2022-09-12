(set-logic QF_NIA)
(declare-const p Int)
(assert (= p 21888242871839275222246405745257275088548364400416034343698204186575808495617))
(declare-const x0 Int)
(declare-const x1 Int)
(declare-const n Int)
(assert (<= 0 x0))
(assert (<= 0 x1))
(assert (<= 0 n))
(assert (<= x0 p))
(assert (<= x1 p))

(assert (! (= x0 1)))
(assert (! (= x1 1)))

(assert (= (* x0 x1) (+ 11 (* n p))))

(check-sat)
(get-model)
