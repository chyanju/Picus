(set-logic QF_FF)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(define-sort F () (_ FiniteField 21888242871839275222246405745257275088548364400416034343698204186575808495617))
; ================================
; ======== original block ========
; ================================
; ======== declaration constraints ========
(declare-const x0 F)
(declare-const x1 F)
(declare-const x2 F)
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
(assert (= one #f0m21888242871839275222246405745257275088548364400416034343698204186575808495617))
; ======== main constraints ========
(assert (= (ff.mul ps1 (ff.mul x3 x6)) (ff.mul ps1 x7)))
(assert (= (ff.mul ps1 (ff.mul x4 x5)) (ff.mul ps1 x8)))
(assert (= (ff.add (ff.mul #f168700m21888242871839275222246405745257275088548364400416034343698204186575808495617 (ff.mul x3 x5)) (ff.add (ff.mul #f168700m21888242871839275222246405745257275088548364400416034343698204186575808495617 (ff.mul x3 x6)) (ff.add (ff.mul ps1 (ff.mul x4 x5)) (ff.mul ps1 (ff.mul x4 x6))))) (ff.mul ps1 x9)))
(assert (= (ff.mul ps1 (ff.mul x7 x8)) (ff.mul ps1 x10)))
(assert (= (ff.add x1 (ff.mul #f168696m21888242871839275222246405745257275088548364400416034343698204186575808495617 (ff.mul x10 x1))) (ff.add x7 x8)))
(assert (= zero (ff.add (ff.mul #f168700m21888242871839275222246405745257275088548364400416034343698204186575808495617 x7) (ff.add (ff.mul ps1 x8) x9))))
(assert (= one one))
; ===================================
; ======== alternative block ========
; ===================================
; ======== declaration constraints ========
; x0: already defined
(declare-const y1 F)
(declare-const y2 F)
; x3: already defined
; x4: already defined
; x5: already defined
; x6: already defined
(declare-const y7 F)
(declare-const y8 F)
(declare-const y9 F)
(declare-const y10 F)
; ======== p definitions: alt skip ========
; ======== main constraints ========
(assert (= (ff.mul ps1 (ff.mul x3 x6)) (ff.mul ps1 y7)))
(assert (= (ff.mul ps1 (ff.mul x4 x5)) (ff.mul ps1 y8)))
(assert (= (ff.add (ff.mul #f168700m21888242871839275222246405745257275088548364400416034343698204186575808495617 (ff.mul x3 x5)) (ff.add (ff.mul #f168700m21888242871839275222246405745257275088548364400416034343698204186575808495617 (ff.mul x3 x6)) (ff.add (ff.mul ps1 (ff.mul x4 x5)) (ff.mul ps1 (ff.mul x4 x6))))) (ff.mul ps1 y9)))
(assert (= (ff.mul ps1 (ff.mul y7 y8)) (ff.mul ps1 y10)))
(assert (= (ff.add y1 (ff.mul #f168696m21888242871839275222246405745257275088548364400416034343698204186575808495617 (ff.mul y10 y1))) (ff.add y7 y8)))
(assert (= zero (ff.add (ff.mul #f168700m21888242871839275222246405745257275088548364400416034343698204186575808495617 y7) (ff.add (ff.mul ps1 y8) y9))))
(assert (= one one))
; ====================================
; ======== precondition block ========
; ====================================
; (no precondition or skipped by user)
; =============================
; ======== known block ========
; =============================
(assert (= x0 x0))
(assert (= x3 x3))
(assert (= x4 x4))
(assert (= x5 x5))
(assert (= x6 x6))
(assert (= x7 y7))
(assert (= x8 y8))
(assert (= x9 y9))
(assert (= x10 y10))
; =============================
; ======== query block ========
; =============================
; (assert (= x7 zero))
(assert (= x1 y1))
; (assert (= x10 #f15937535784349561894616308370721219655188393586073782108286393956286256253510m21888242871839275222246405745257275088548364400416034343698204186575808495617))
; (assert (not (= x1 y1)))
(assert (= x10 #f5950707087489713327630097374536055433359970814342252235411810230289552242107m21888242871839275222246405745257275088548364400416034343698204186575808495617))
; (assert (not (= x2 y2)))
(check-sat)
(get-model)