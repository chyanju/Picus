(set-logic QF_FF)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(define-sort F () (_ FiniteField 21888242871839275222246405745257275088548364400416034343698204186575808495617))
; ================================
; ======== original block ========
; ================================
; ======== declaration constraints ========
(declare-const x1 F)
(declare-const x3 F)
(declare-const x4 F)
(declare-const x5 F)
(declare-const x6 F)
(declare-const x7 F)
(declare-const x8 F)
(declare-const x9 F)
(declare-const x10 F)
; ======== p definitions ========
(declare-const p F)
(assert (= p #f21888242871839275222246405745257275088548364400416034343698204186575808495617m21888242871839275222246405745257275088548364400416034343698204186575808495617))
(declare-const ps1 F)
(assert (= ps1 #f21888242871839275222246405745257275088548364400416034343698204186575808495616m21888242871839275222246405745257275088548364400416034343698204186575808495617))
(declare-const ps2 F)
(assert (= ps2 #f21888242871839275222246405745257275088548364400416034343698204186575808495615m21888242871839275222246405745257275088548364400416034343698204186575808495617))
(declare-const ps3 F)
(assert (= ps3 #f21888242871839275222246405745257275088548364400416034343698204186575808495614m21888242871839275222246405745257275088548364400416034343698204186575808495617))
(declare-const ps4 F)
(assert (= ps4 #f21888242871839275222246405745257275088548364400416034343698204186575808495613m21888242871839275222246405745257275088548364400416034343698204186575808495617))
(declare-const ps5 F)
(assert (= ps5 #f21888242871839275222246405745257275088548364400416034343698204186575808495612m21888242871839275222246405745257275088548364400416034343698204186575808495617))
(declare-const zero F)
(assert (= zero #f0m21888242871839275222246405745257275088548364400416034343698204186575808495617))
(declare-const one F)
(assert (= one #f1m21888242871839275222246405745257275088548364400416034343698204186575808495617))

(declare-const a F)
(assert (= a #f168700m21888242871839275222246405745257275088548364400416034343698204186575808495617))
(declare-const d F)
(assert (= d #f168696m21888242871839275222246405745257275088548364400416034343698204186575808495617))
(declare-const pd F)
(assert (= pd #f21888242871839275222246405745257275088548364400416034343698204186575808326921m21888242871839275222246405745257275088548364400416034343698204186575808495617))

(assert (=
    (ff.mul x3 x6)
    x7
))

(assert (=
    (ff.mul x4 x5)
    x8
))

(assert (=
    (ff.mul ps1 x9)
    (ff.mul
        (ff.add x5 x6)
        (ff.add
            (ff.mul a x3)
            (ff.mul ps1 x4)
        )
    )
))

(assert (=
    x10
    (ff.mul x7 x8)
))

(assert (=
    zero
    (ff.add
        one
        (ff.mul pd x10)
    )
))

(assert (=
    zero
    (ff.add
        x9
        (ff.add
            (ff.mul a x7)
            (ff.mul ps1 x8)
        )
    )
))

; this hangs, need simplification
; even with x10 plugged in, it still hangs
(assert (= x10 #f5950707087489713327630097374536055433359970814342252235411810230289552242107m21888242871839275222246405745257275088548364400416034343698204186575808495617))

; =============================
; ======== query block ========
; =============================
(check-sat)
(get-model)