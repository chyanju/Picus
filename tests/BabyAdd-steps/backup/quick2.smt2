(set-logic QF_NIA)
; ================================
; ======== original block ========
; ================================
; ======== declaration constraints ========
(declare-const x0 Int)
(declare-const x1 Int)
(declare-const x2 Int)
(declare-const x3 Int)
(declare-const x4 Int)
(declare-const x5 Int)
(declare-const x6 Int)
(declare-const x7 Int)
(declare-const x8 Int)
(declare-const x9 Int)
(declare-const x10 Int)
; ======== range constraints ========
(assert (and (<= 0 x0) (< x0 21888242871839275222246405745257275088548364400416034343698204186575808495617)))
(assert (and (<= 0 x1) (< x1 21888242871839275222246405745257275088548364400416034343698204186575808495617)))
(assert (and (<= 0 x2) (< x2 21888242871839275222246405745257275088548364400416034343698204186575808495617)))
(assert (and (<= 0 x3) (< x3 21888242871839275222246405745257275088548364400416034343698204186575808495617)))
(assert (and (<= 0 x4) (< x4 21888242871839275222246405745257275088548364400416034343698204186575808495617)))
(assert (and (<= 0 x5) (< x5 21888242871839275222246405745257275088548364400416034343698204186575808495617)))
(assert (and (<= 0 x6) (< x6 21888242871839275222246405745257275088548364400416034343698204186575808495617)))
(assert (and (<= 0 x7) (< x7 21888242871839275222246405745257275088548364400416034343698204186575808495617)))
(assert (and (<= 0 x8) (< x8 21888242871839275222246405745257275088548364400416034343698204186575808495617)))
(assert (and (<= 0 x9) (< x9 21888242871839275222246405745257275088548364400416034343698204186575808495617)))
(assert (and (<= 0 x10) (< x10 21888242871839275222246405745257275088548364400416034343698204186575808495617)))
; ======== p definitions ========
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
; ======== main constraints ========

(assert
    (=
        0
        (mod
            (+
                (* 168700 x7)
                (+
                    (* ps1 x8)
                    x9
                )
            )
            p
        )
    )
)

(assert
    (=
        (mod
            (*
                x8
                x7
            )
            p
        )
        x10
    )
)

; =============================
; ======== query block ========
; =============================
(assert (= x10 5950707087489713327630097374536055433359970814342252235411810230289552242107))

; candidate 1
; (assert (= x8 1))
; (assert (= x7 15937535784349561894616308370721219655188393586073782108286393956286256253510))

(assert (= x8 5950707087489713327630097374536055433359970814342252235411810230289552242107))
(assert (= x7 1))


(check-sat)
(get-model)