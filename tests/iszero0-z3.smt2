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
; ================================
; ======== original block ========
; ================================
; ======== declaration constraints ========
(declare-const x0 Int)
(declare-const x1 Int)
(declare-const x2 Int)
(declare-const x3 Int)
; ======== range constraints ========
(assert (and (<= 0 1) (< 1 p)))
(assert (and (<= 0 x1) (< x1 p)))
(assert (and (<= 0 x2) (< x2 p)))
(assert (and (<= 0 x3) (< x3 p)))
(assert (= (mod (* x2 x3) p) (mod (+ 1 (* ps1 x1)) p)))
(assert (= (mod (* x2 x1) p) 0))
(assert (= 1 1))
; ===================================
; ======== alternative block ========
; ===================================
; ======== declaration constraints ========
; x0: already defined
(declare-const y1 Int)
; x2: already defined
(declare-const y3 Int)
; ======== range constraints ========
; x0: already defined
(assert (and (<= 0 y1) (< y1 p)))
; x2: already defined
(assert (and (<= 0 y3) (< y3 p)))
(assert (= (mod (* x2 y3) p) (mod (+ 1 (* ps1 y1)) p)))
(assert (= (mod (* x2 y1) p) 0))
(assert (= 1 1))
; =============================
; ======== known block ========
; =============================
(assert (= 1 1))
(assert (= x2 x2))
; ======== lemma derivations ========
(assert (or
    (= 0 x2)
    (= 0 x1)
))
(assert (or
    (= 0 x2)
    (= 0 y1)
))
; =============================
; ======== query block ========
; =============================
(assert (not (= x1 y1)))
(check-sat)
(get-model)