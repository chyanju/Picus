(set-logic QF_FF)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(define-sort F () (_ FiniteField 21888242871839275222246405745257275088548364400416034343698204186575808495617))
; ================================
; ======== original block ========
; ================================
; ======== declaration constraints ========
(declare-const x1 F)
; (declare-const x3 F)
; (declare-const x4 F)
; (declare-const x5 F)
; (declare-const x6 F)
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
(declare-const b F)
(assert (= b #f168696m21888242871839275222246405745257275088548364400416034343698204186575808495617))

; first add this constraint, and it returns sat
; then we should add more
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

; then we choose to add this constraint
(assert (=
    (ff.add x7 x8)
    (ff.mul
        x1
        (ff.add
            one
            (ff.mul b x10)
        )
    )
))

; then we add this constraint, still sat
; then we should add more
(assert (=
    (ff.mul ps1 x10)
    (ff.mul ps1 (ff.mul x7 x8))
))

; (assert (=
;     (ff.mul x3 x6)
;     x7
; ))
; (assert (=
;     (ff.mul x4 x5)
;     x8
; ))
; (assert (=
;     x9
;     (ff.mul
;         (ff.add x5 x6)
;         (ff.add
;             (ff.mul a x3)
;             (ff.mul ps1 x4)
;         )
;     )
; ))

; case
(assert (= x10 #f5950707087489713327630097374536055433359970814342252235411810230289552242107m21888242871839275222246405745257275088548364400416034343698204186575808495617))


; block
(assert (and
    (not (= x1 zero))
    (not (= x7 zero))
    (not (= x8 zero))
    (not (= x9 zero))
))

; =============================
; ======== query block ========
; =============================
(check-sat)
(get-model)