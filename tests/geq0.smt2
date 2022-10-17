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
(declare-const x5 Int)
(declare-const x6 Int)
(declare-const x7 Int)
(declare-const x8 Int)
(declare-const x9 Int)
(declare-const x10 Int)
; ======== range constraints ========
(assert (and (<= 0 1) (< 1 p)))
(assert (and (<= 0 x1) (< x1 p)))
(assert (and (<= 0 x2) (< x2 p)))
(assert (and (<= 0 x3) (< x3 p)))
(assert (and (<= 0 x4) (< x4 p)))
(assert (and (<= 0 x5) (< x5 p)))
(assert (and (<= 0 x6) (< x6 p)))
(assert (and (<= 0 x7) (< x7 p)))
(assert (and (<= 0 x8) (< x8 p)))
(assert (and (<= 0 x9) (< x9 p)))
(assert (and (<= 0 x10) (< x10 p)))
(assert (= 0 (mod (+ x3 (* ps1 x5)) p)))
(assert (= 0 (mod (+ 1 (+ x2 (* ps1 x6))) p)))
(assert (= 0 (mod (+ (* ps1 x1) x4) p)))
(assert (= 0 (mod (+ 4 (+ x5 (+ (* ps1 x6) (* ps1 x10)))) p)))
(assert (= 0 (mod (+ 1 (+ (* ps1 x4) (* ps1 x9))) p)))
(assert (= (mod (+ (* ps1 x7) (* x7 x7)) p) 0))
(assert (= (mod (+ (* ps1 x8) (* x8 x8)) p) 0))
(assert (= (mod (+ (* ps1 x9) (* x9 x9)) p) 0))
(assert (= 0 (mod (+ (* ps1 x7) (+ (* ps2 x8) (+ (* ps4 x9) x10))) p)))
(assert (= 1 1))
; ===================================
; ======== alternative block ========
; ===================================
; ======== declaration constraints ========
; x0: already defined
(declare-const y1 Int)
; x2: already defined
; x3: already defined
(declare-const y4 Int)
(declare-const y5 Int)
(declare-const y6 Int)
(declare-const y7 Int)
(declare-const y8 Int)
(declare-const y9 Int)
(declare-const y10 Int)
; ======== range constraints ========
; x0: already defined
(assert (and (<= 0 y1) (< y1 p)))
; x2: already defined
; x3: already defined
(assert (and (<= 0 y4) (< y4 p)))
(assert (and (<= 0 y5) (< y5 p)))
(assert (and (<= 0 y6) (< y6 p)))
(assert (and (<= 0 y7) (< y7 p)))
(assert (and (<= 0 y8) (< y8 p)))
(assert (and (<= 0 y9) (< y9 p)))
(assert (and (<= 0 y10) (< y10 p)))
(assert (= 0 (mod (+ x3 (* ps1 y5)) p)))
(assert (= 0 (mod (+ 1 (+ x2 (* ps1 y6))) p)))
(assert (= 0 (mod (+ (* ps1 y1) y4) p)))
(assert (= 0 (mod (+ 4 (+ y5 (+ (* ps1 y6) (* ps1 y10)))) p)))
(assert (= 0 (mod (+ 1 (+ (* ps1 y4) (* ps1 y9))) p)))
(assert (= (mod (+ (* ps1 y7) (* y7 y7)) p) 0))
(assert (= (mod (+ (* ps1 y8) (* y8 y8)) p) 0))
(assert (= (mod (+ (* ps1 y9) (* y9 y9)) p) 0))
(assert (= 0 (mod (+ (* ps1 y7) (+ (* ps2 y8) (+ (* ps4 y9) y10))) p)))
(assert (= 1 1))
; =============================
; ======== known block ========
; =============================
(assert (= 1 1))
(assert (= x2 x2))
(assert (= x3 x3))
(assert (= x5 y5))
(assert (= x6 y6))
(assert (= x10 y10))
; ======== lemma derivations ========
(assert (or
    (= 0 (+ ps1 x7))
    (= 0 x7)
))
(assert (or
    (= 0 (+ ps1 x8))
    (= 0 x8)
))
(assert (or
    (= 0 (+ ps1 x9))
    (= 0 x9)
))
(assert (or
    (= 0 (+ ps1 y7))
    (= 0 y7)
))
(assert (or
    (= 0 (+ ps1 y8))
    (= 0 y8)
))
(assert (or
    (= 0 (+ ps1 y9))
    (= 0 y9)
))
; =============================
; ======== query block ========
; =============================
(assert (not (= x9 y9)))
(check-sat)
(get-model)