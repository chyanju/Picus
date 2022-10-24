(set-logic QF_FF)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(define-sort F () (_ FiniteField 21888242871839275222246405745257275088548364400416034343698204186575808495617))
; ================================
; ======== original block ========
; ================================
; ======== declaration constraints ========
(declare-const x1 F)
(declare-const x35 F)
(declare-const x36 F)
(declare-const x45 F)
(declare-const x46 F)
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


; case assumption
(assert (=
    zero
    (ff.add
        one
        (ff.mul pd x10)
    )
))

; case assumption
(assert (=
    zero
    (ff.add
        x9
        (ff.add
            (ff.mul a x36)
            (ff.mul ps1 x45)
        )
    )
))

; this is not enough, we need to include more constraints
(assert (=
    (ff.mul ps1 x9)
    (ff.add
        (ff.mul a x35)
        (ff.add
            (ff.mul ps1 x45)
            (ff.add
                (ff.mul a x36)
                (ff.mul ps1 x46)
            )
        )
    )
))

(assert (=
    x10
    (ff.mul x36 x45)
))

; (important) super extra constraint introduced by rewriting
(assert (=
    (ff.mul x36 x45)
    (ff.mul x35 x46)
))

; still not enough
; add all remaining constraints back assuming we don't know what to choose
(assert (=
    (ff.add x35 x45)
    (ff.mul
        x1
        (ff.add
            one
            (ff.mul d x10)
        )
    )
))

; =============================
; ======== query block ========
; =============================
(check-sat)
(get-model)