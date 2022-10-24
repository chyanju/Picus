(set-logic QF_FF)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(define-sort F () (_ FiniteField 21888242871839275222246405745257275088548364400416034343698204186575808495617))
; ================================
; ======== original block ========
; ================================
; ======== declaration constraints ========
(declare-const x1 F)
(declare-const x2 F)
(declare-const x35 F)
(declare-const x36 F)
(declare-const x45 F)
(declare-const x46 F)
(declare-const x10 F)
; ======== p definitions ========
(declare-const p F)
(assert (= p #f21888242871839275222246405745257275088548364400416034343698204186575808495617m21888242871839275222246405745257275088548364400416034343698204186575808495617))
(declare-const p1 F)
(assert (= p1 #f21888242871839275222246405745257275088548364400416034343698204186575808495616m21888242871839275222246405745257275088548364400416034343698204186575808495617))
(declare-const p2 F)
(assert (= p2 #f21888242871839275222246405745257275088548364400416034343698204186575808495615m21888242871839275222246405745257275088548364400416034343698204186575808495617))
(declare-const p3 F)
(assert (= p3 #f21888242871839275222246405745257275088548364400416034343698204186575808495614m21888242871839275222246405745257275088548364400416034343698204186575808495617))
(declare-const p4 F)
(assert (= p4 #f21888242871839275222246405745257275088548364400416034343698204186575808495613m21888242871839275222246405745257275088548364400416034343698204186575808495617))
(declare-const p5 F)
(assert (= p5 #f21888242871839275222246405745257275088548364400416034343698204186575808495612m21888242871839275222246405745257275088548364400416034343698204186575808495617))
(declare-const zero F)
(assert (= zero #f0m21888242871839275222246405745257275088548364400416034343698204186575808495617))
(declare-const one F)
(assert (= one #f0m21888242871839275222246405745257275088548364400416034343698204186575808495617))

(declare-const a F)
(assert (= a #f168700m21888242871839275222246405745257275088548364400416034343698204186575808495617))
(declare-const b F)
(assert (= b #f168696m21888242871839275222246405745257275088548364400416034343698204186575808495617))
(declare-const pb F)
(assert (= pb #f21888242871839275222246405745257275088548364400416034343698204186575808326921m21888242871839275222246405745257275088548364400416034343698204186575808495617))
; ======== main constraints ========
(assert (=
    zero
    (ff.add
        (ff.mul
            x2
            (ff.add
                one
                (ff.mul pb x10)
            )
        )
        (ff.add
            (ff.mul a x35)
            (ff.mul p1 x46)
        )
    )
))
(assert (=
    (ff.mul
        x1
        (ff.add
            one
            (ff.mul b x10)
        )
    )
    (ff.add
        x36
        x45
    )
))
(assert (=
    x10
    (ff.mul x36 x45)
))
; ===================================
; ======== alternative block ========
; ===================================
; ======== declaration constraints ========
; (declare-const y1 F)
; (declare-const y2 F)
; x3: already defined
; x4: already defined
; x5: already defined
; x6: already defined
; (declare-const y10 F)
; ======== p definitions: alt skip ========
; ======== main constraints ========
; (assert (=
;     zero
;     (ff.add
;         (ff.mul
;             y2
;             (ff.add
;                 one
;                 (ff.mul pb y10)
;             )
;         )
;         (ff.add
;             (ff.mul a (ff.mul x3 x5))
;             (ff.mul p1 (ff.mul x4 x6))
;         )
;     )
; ))
; (assert (=
;     (ff.mul
;         y1
;         (ff.add
;             one
;             (ff.mul b y10)
;         )
;     )
;     (ff.add
;         (ff.mul x3 x6)
;         (ff.mul x4 x5)
;     )
; ))
; (assert (=
;     y10
;     (ff.mul x3 (ff.mul x4 (ff.mul x5 x6)))
; ))


(assert (and
    (not (= x1 zero))
    (not (= x2 zero))
    (= x35 zero)
    (= x36 zero)
    (= x45 zero)
    (= x46 zero)
    (= x10 zero)
))

(check-sat)
(get-model)