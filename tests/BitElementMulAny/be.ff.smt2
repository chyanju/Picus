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
(declare-const x11 F)
(declare-const x12 F)
(declare-const x13 F)
(declare-const x14 F)
(declare-const x15 F)
(declare-const x16 F)
(declare-const x17 F)
(declare-const x18 F)
(declare-const x19 F)
(declare-const x20 F)
(declare-const x21 F)
(declare-const x22 F)
(declare-const x23 F)
(declare-const x24 F)
(declare-const x25 F)
(declare-const x26 F)
(declare-const x27 F)
(declare-const x28 F)
(declare-const x29 F)
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
; ======== main constraints ========

; doubler
(assert (= (ff.mul ps1 (ff.mul x19 x19)) (ff.mul ps1 x22)))
(assert (= (ff.mul #f2m21888242871839275222246405745257275088548364400416034343698204186575808495617 (ff.mul x20 x21)) (ff.add one (ff.add (ff.mul #f337396m21888242871839275222246405745257275088548364400416034343698204186575808495617 x19) (ff.mul #f3m21888242871839275222246405745257275088548364400416034343698204186575808495617 x22)))))
(assert (= (ff.mul ps1 (ff.mul x21 x21)) (ff.add #f21888242871839275222246405745257275088548364400416034343698204186575808326919m21888242871839275222246405745257275088548364400416034343698204186575808495617 (ff.add (ff.mul ps1 x17) (ff.mul ps2 x19)))))
(assert (= (ff.add (ff.mul x17 x21) (ff.mul ps1 (ff.mul x19 x21))) (ff.add (ff.mul ps1 x18) (ff.mul ps1 x20))))

; adder
(assert (= (ff.add (ff.mul ps1 (ff.mul x12 x16)) (ff.mul x14 x16)) (ff.add (ff.mul ps1 x13) x15)))
(assert (= (ff.mul ps1 (ff.mul x16 x16)) (ff.add #f21888242871839275222246405745257275088548364400416034343698204186575808326919m21888242871839275222246405745257275088548364400416034343698204186575808495617 (ff.add (ff.mul ps1 x10) (ff.add (ff.mul ps1 x12) (ff.mul ps1 x14))))))
(assert (= (ff.add (ff.mul x10 x16) (ff.mul ps1 (ff.mul x12 x16))) (ff.add (ff.mul ps1 x11) (ff.mul ps1 x13))))

; selector
(assert (= (ff.add (ff.mul x26 x25) (ff.mul ps1 (ff.mul x28 x25))) (ff.add (ff.mul ps1 x23) x26)))
(assert (= (ff.add (ff.mul x27 x25) (ff.mul ps1 (ff.mul x29 x25))) (ff.add (ff.mul ps1 x24) x27)))

; main -> doubler
(assert (= zero (ff.add x6 (ff.mul ps1 x19))))
(assert (= zero (ff.add x7 (ff.mul ps1 x20))))

; main -> adder
(assert (= zero (ff.add x8 (ff.mul ps1 x14))))
(assert (= zero (ff.add x9 (ff.mul ps1 x15))))

; main -> selector
(assert (= zero (ff.add x5 (ff.mul ps1 x25))))
(assert (= zero (ff.add x8 (ff.mul ps1 x26))))
(assert (= zero (ff.add x9 (ff.mul ps1 x27))))

; doubler -> main
(assert (= zero (ff.add (ff.mul ps1 x1) x17)))
(assert (= zero (ff.add (ff.mul ps1 x2) x18)))

; adder -> main

; selector -> main
(assert (= zero (ff.add (ff.mul ps1 x3) x23)))
(assert (= zero (ff.add (ff.mul ps1 x4) x24)))

; doubler -> adder
(assert (= zero (ff.add (ff.mul ps1 x12) x17)))
(assert (= zero (ff.add (ff.mul ps1 x13) x18)))

; adder -> selector
(assert (= zero (ff.add x10 (ff.mul ps1 x28))))
(assert (= zero (ff.add x11 (ff.mul ps1 x29))))

; ===================================
; ======== alternative block ========
; ===================================
; ======== declaration constraints ========
; x0: already defined
(declare-const y1 F)
(declare-const y2 F)
(declare-const y3 F)
(declare-const y4 F)
; x5: already defined
; x6: already defined
; x7: already defined
; x8: already defined
; x9: already defined
(declare-const y10 F)
(declare-const y11 F)
(declare-const y12 F)
(declare-const y13 F)
(declare-const y14 F)
(declare-const y15 F)
(declare-const y16 F)
(declare-const y17 F)
(declare-const y18 F)
(declare-const y19 F)
(declare-const y20 F)
(declare-const y21 F)
(declare-const y22 F)
(declare-const y23 F)
(declare-const y24 F)
(declare-const y25 F)
(declare-const y26 F)
(declare-const y27 F)
(declare-const y28 F)
(declare-const y29 F)
; ======== p definitions: alt skip ========
; ======== main constraints ========


; doubler
(assert (= (ff.mul ps1 (ff.mul y19 y19)) (ff.mul ps1 y22)))
(assert (= (ff.mul #f2m21888242871839275222246405745257275088548364400416034343698204186575808495617 (ff.mul y20 y21)) (ff.add one (ff.add (ff.mul #f337396m21888242871839275222246405745257275088548364400416034343698204186575808495617 y19) (ff.mul #f3m21888242871839275222246405745257275088548364400416034343698204186575808495617 y22)))))
(assert (= (ff.mul ps1 (ff.mul y21 y21)) (ff.add #f21888242871839275222246405745257275088548364400416034343698204186575808326919m21888242871839275222246405745257275088548364400416034343698204186575808495617 (ff.add (ff.mul ps1 y17) (ff.mul ps2 y19)))))
(assert (= (ff.add (ff.mul y17 y21) (ff.mul ps1 (ff.mul y19 y21))) (ff.add (ff.mul ps1 y18) (ff.mul ps1 y20))))

; adder
(assert (= (ff.add (ff.mul ps1 (ff.mul y12 y16)) (ff.mul y14 y16)) (ff.add (ff.mul ps1 y13) y15)))
(assert (= (ff.mul ps1 (ff.mul y16 y16)) (ff.add #f21888242871839275222246405745257275088548364400416034343698204186575808326919m21888242871839275222246405745257275088548364400416034343698204186575808495617 (ff.add (ff.mul ps1 y10) (ff.add (ff.mul ps1 y12) (ff.mul ps1 y14))))))
(assert (= (ff.add (ff.mul y10 y16) (ff.mul ps1 (ff.mul y12 y16))) (ff.add (ff.mul ps1 y11) (ff.mul ps1 y13))))

; selector
(assert (= (ff.add (ff.mul y26 y25) (ff.mul ps1 (ff.mul y28 y25))) (ff.add (ff.mul ps1 y23) y26)))
(assert (= (ff.add (ff.mul y27 y25) (ff.mul ps1 (ff.mul y29 y25))) (ff.add (ff.mul ps1 y24) y27)))

; main -> doubler
(assert (= zero (ff.add x6 (ff.mul ps1 y19))))
(assert (= zero (ff.add x7 (ff.mul ps1 y20))))

; main -> adder
(assert (= zero (ff.add x8 (ff.mul ps1 y14))))
(assert (= zero (ff.add x9 (ff.mul ps1 y15))))

; main -> selector
(assert (= zero (ff.add x5 (ff.mul ps1 y25))))
(assert (= zero (ff.add x8 (ff.mul ps1 y26))))
(assert (= zero (ff.add x9 (ff.mul ps1 y27))))

; doubler -> main
(assert (= zero (ff.add (ff.mul ps1 y1) y17)))
(assert (= zero (ff.add (ff.mul ps1 y2) y18)))

; adder -> main

; selector -> main
(assert (= zero (ff.add (ff.mul ps1 y3) y23)))
(assert (= zero (ff.add (ff.mul ps1 y4) y24)))

; doubler -> adder
(assert (= zero (ff.add (ff.mul ps1 y12) y17)))
(assert (= zero (ff.add (ff.mul ps1 y13) y18)))

; adder -> selector
(assert (= zero (ff.add y10 (ff.mul ps1 y28))))
(assert (= zero (ff.add y11 (ff.mul ps1 y29))))

; ====================================
; ======== precondition block ========
; ====================================
; (no precondition or skipped by user)
; =============================
; ======== known block ========
; =============================
(assert (= x0 x0))
(assert (= x19 y19))
(assert (= x20 y20))
(assert (= x5 x5))
(assert (= x7 x7))
(assert (= x8 x8))
(assert (= x26 y26))
(assert (= x27 y27))
(assert (= x14 y14))
(assert (= x15 y15))
(assert (= x6 x6))
(assert (= x22 y22))
(assert (= x9 x9))
(assert (= x25 y25))
; =============================
; ======== query block ========
; =============================

; hints
; doubler hints
(assert (= x17 #f5322068362127053380761936828261197253630416030257971508159916442316514342224m21888242871839275222246405745257275088548364400416034343698204186575808495617))
(assert (= x18 zero))
(assert (= y17 zero))
(assert (= y18 #f11395287471962378606215025428882238971762841540906324053591198862844560648166m21888242871839275222246405745257275088548364400416034343698204186575808495617))
; adder hints
(assert (= x10 zero))
(assert (= x11 zero))
(assert (= x14 #f16566174509712221841484468916996077834917948370158062835538287744259293984695m21888242871839275222246405745257275088548364400416034343698204186575808495617))
(assert (= x15 zero))
(assert (= y10 #f3991551271595290035571452621195897940222812022693478631119937331737385756668m21888242871839275222246405745257275088548364400416034343698204186575808495617))
(assert (= y11 #f4012429113723871465222073151607819404797376354456273132644964550131685945213m21888242871839275222246405745257275088548364400416034343698204186575808495617))
(assert (= y14 #f16566174509712221841484468916996077834917948370158062835538287744259293984695m21888242871839275222246405745257275088548364400416034343698204186575808495617))
(assert (= y15 zero))
; selector hints
(assert (= x23 zero))
(assert (= x24 zero))
(assert (= y23 #f3991551271595290035571452621195897940222812022693478631119937331737385756668m21888242871839275222246405745257275088548364400416034343698204186575808495617))
(assert (= y24 #f4012429113723871465222073151607819404797376354456273132644964550131685945213m21888242871839275222246405745257275088548364400416034343698204186575808495617))

(assert (not (= x1 y1)))
(check-sat)
(get-model)