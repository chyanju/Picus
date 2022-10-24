(set-logic QF_NIA)
(declare-const p Int)
(assert (= p 21888242871839275222246405745257275088548364400416034343698204186575808495617))

(declare-const x10 Int)
(assert (and (<= 0 x10) (< x10 p)))

; we want to prove ( 1 + b * x10 ) != 0
; so we need to find a counter-example
(assert (= 0 (mod (+ 1 (* 168696 x10)) p)))

; block
(assert (not (= x10 15937535784349561894616308370721219655188393586073782108286393956286256253510)))

(check-sat)
(get-model)