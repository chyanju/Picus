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
(declare-const x3 F)
(declare-const x4 F)
(declare-const x5 F)
(declare-const x6 F)
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
            (ff.mul a (ff.mul x3 x5))
            (ff.mul p1 (ff.mul x4 x6))
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
        (ff.mul x3 x6)
        (ff.mul x4 x5)
    )
))
(assert (=
    x10
    (ff.mul x3 (ff.mul x4 (ff.mul x5 x6)))
))
; ===================================
; ======== alternative block ========
; ===================================
; ======== declaration constraints ========
(declare-const y1 F)
(declare-const y2 F)
; x3: already defined
; x4: already defined
; x5: already defined
; x6: already defined
(declare-const y10 F)
; ======== p definitions: alt skip ========
; ======== main constraints ========
(assert (=
    zero
    (ff.add
        (ff.mul
            y2
            (ff.add
                one
                (ff.mul pb y10)
            )
        )
        (ff.add
            (ff.mul a (ff.mul x3 x5))
            (ff.mul p1 (ff.mul x4 x6))
        )
    )
))
(assert (=
    (ff.mul
        y1
        (ff.add
            one
            (ff.mul b y10)
        )
    )
    (ff.add
        (ff.mul x3 x6)
        (ff.mul x4 x5)
    )
))
(assert (=
    y10
    (ff.mul x3 (ff.mul x4 (ff.mul x5 x6)))
))
; ====================================
; ======== precondition block ========
; ====================================
; (no precondition or skipped by user)
; =============================
; ======== known block ========
; =============================
(assert (= x10 y10))
; =============================
; ======== query block ========
; =============================
; (assert (= x1 y1))
; (assert (= x10 #f15937535784349561894616308370721219655188393586073782108286393956286256253510m21888242871839275222246405745257275088548364400416034343698204186575808495617))
; (assert (not (= x1 y1)))
; (assert (= x10 #f5950707087489713327630097374536055433359970814342252235411810230289552242107m21888242871839275222246405745257275088548364400416034343698204186575808495617))



(assert (not (= x2 y2)))


; (assert (= x1 zero))
; (assert (= x2 one))
; (assert (= y1 zero))
; (assert (= y2 zero))

(assert (and
    (not (= x1 zero))
    (not (= x2 one))
    (not (= y1 zero))
    (not (= y2 zero))
))

(assert (and
    (not (= x1 one))
    (not (= x2 one))
    (not (= y1 one))
    (not (= y2 p1))
))

; (assert (and
;     (not (= x1 one))
;     (not (= x2 one))
;     (not (= y1 one))
;     (not (= y2 one))
; ))

; (assert (= x1 zero))
; (assert (= x2 one))
; (assert (= y1 zero))
; (assert (= y2 zero))


(check-sat)
(get-model)