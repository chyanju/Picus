(set-logic QF_NIA)
(declare-const p Int)
(assert (= p 21888242871839275222246405745257275088548364400416034343698204186575808495617))
(declare-const ps1 Int)
(assert (= ps1 21888242871839275222246405745257275088548364400416034343698204186575808495616))
(declare-const ps2 Int)
(assert (= ps2 21888242871839275222246405745257275088548364400416034343698204186575808495615))
(declare-const ps3 Int)
(assert (= ps3 21888242871839275222246405745257275088548364400416034343698204186575808495614))
(declare-const ps4 Int)
(assert (= ps4 21888242871839275222246405745257275088548364400416034343698204186575808495613))
(declare-const ps5 Int)
(assert (= ps5 21888242871839275222246405745257275088548364400416034343698204186575808495612))


(declare-const x10 Int)
(declare-const k Int)
(assert (and (<= 0 x10) (< x10 p)))
(assert (and (<= 0 k) (< k p)))

; we want to prove ( 1 + b * x10 ) != 0
; so we need to find a counter-example
; (assert (= (* 168696 x10) (- (* k p) 1)))
(assert (= 0 (mod (+ 1 (* 168696 x10)) p)))

; block
(assert (and
    (not (= x10 15937535784349561894616308370721219655188393586073782108286393956286256253510))
    (not (= k 122833))
))

(check-sat)
(get-model)