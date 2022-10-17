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
; (assert (= (* x4 x1) 0))
; (assert (= (+ (* ps1 x2) (* x4 x2)) 0))
; (assert (= 0 (mod (+ x1 (+ x2 (* ps1 x3))) p)))
; (assert (= (+ (* ps1 x3) (* x3 x3)) 0))
(assert (= (mod (* x4 x1) p) 0))
(assert (= (mod (+ (* ps1 x2) (* x4 x2)) p) 0))
(assert (= 0 (mod (+ x1 (+ x2 (* ps1 x3))) p)))
(assert (= (mod (+ (* ps1 x3) (* x3 x3)) p) 0))
(assert (= 1 1))
; ===================================
; ======== alternative block ========
; ===================================
; ======== declaration constraints ========
; x0: already defined
(declare-const y1 Int)
(declare-const y2 Int)
(declare-const y3 Int)
; x4: already defined
; ======== range constraints ========
; x0: already defined
(assert (and (<= 0 y1) (< y1 p)))
(assert (and (<= 0 y2) (< y2 p)))
(assert (and (<= 0 y3) (< y3 p)))
; x4: already defined
; (assert (= (* x4 y1) 0))
; (assert (= (+ (* ps1 y2) (* x4 y2)) 0))
; (assert (= 0 (mod (+ y1 (+ y2 (* ps1 y3))) p)))
; (assert (= (+ (* ps1 y3) (* y3 y3)) 0))
(assert (= (mod (* x4 y1) p) 0))
(assert (= (mod (+ (* ps1 y2) (* x4 y2)) p) 0))
(assert (= 0 (mod (+ y1 (+ y2 (* ps1 y3))) p)))
(assert (= (mod (+ (* ps1 y3) (* y3 y3)) p) 0))
(assert (= 1 1))
; =============================
; ======== known block ========
; =============================
(assert (= 1 1))
(assert (= x4 x4))
; =============================
; ======== query block ========
; =============================
(assert (not (= x1 y1)))
(check-sat)
(get-model)