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
(declare-const x4 Int)
; ======== range constraints ========
(assert (and (<= 0 1) (< 1 p)))
(assert (and (<= 0 x1) (< x1 p)))
(assert (and (<= 0 x2) (< x2 p)))
(assert (and (<= 0 x3) (< x3 p)))
(assert (and (<= 0 x4) (< x4 p)))
(assert (= (mod (+ x1 (* ps1 (* x4 x1))) p) (mod (+ 1 x4) p)))
(assert (= (mod (* x2 x3) p) (mod x1 p)))
(assert (= 1 1))
; ===================================
; ======== alternative block ========
; ===================================
; ======== declaration constraints ========
; x0: already defined
(declare-const y1 Int)
(declare-const y2 Int)
; x3: already defined
; x4: already defined
; ======== range constraints ========
; x0: already defined
(assert (and (<= 0 y1) (< y1 p)))
(assert (and (<= 0 y2) (< y2 p)))
; x3: already defined
; x4: already defined
(assert (= (mod (+ y1 (* ps1 (* x4 y1))) p) (mod (+ 1 x4) p)))
(assert (= (mod (* y2 x3) p) (mod y1 p)))
(assert (= 1 1))
; =============================
; ======== known block ========
; =============================
(assert (= 1 1))
(assert (= x3 x3))
(assert (= x4 x4))
; ======== preconditions ========
; (assert (! (= x4 1)))
; =============================
; ======== query block ========
; =============================
(assert (not (= x2 y2)))
(check-sat)
(get-model)