(set-logic QF_NIA)
(declare-const p Int)
(assert (= p 21888242871839275222246405745257275088548364400416034343698204186575808495617))

(declare-const x1 Int)
(declare-const x2 Int)
(declare-const x35 Int)
(declare-const x36 Int)
(declare-const x45 Int)
(declare-const x46 Int)
(declare-const x10 Int)
(assert (and (<= 0 x1) (< x1 p)))
(assert (and (<= 0 x2) (< x2 p)))
(assert (and (<= 0 x35) (< x35 p)))
(assert (and (<= 0 x36) (< x36 p)))
(assert (and (<= 0 x45) (< x45 p)))
(assert (and (<= 0 x46) (< x46 p)))
(assert (and (<= 0 x10) (< x10 p)))

; (declare-const y1 Int)
; (declare-const y2 Int)
; (assert (and (<= 0 y1) (< y1 p)))
; (assert (and (<= 0 y2) (< y2 p)))


(declare-const a Int)
(declare-const b Int)
(assert (= a 168700))
(assert (= b 168696))

; main

(assert (=
    0
    (mod
        (+
            (*
                x2
                (+
                    1
                    (*
                        x10
                        (- p b)
                    )
                )
            )
            (+
                (* a x35)
                (* (- p 1) x46)
            )
        )
        p
    )
))

(assert (=
    (mod
        (*
            x1
            (+
                1
                (* b x10)
            )
        )
        p
    )
    (mod
        (+
            x36
            x45
        )
        p
    )
))

(assert (=
    x10
    (mod
        (* x36 x45)
        p
    )
))

; (assert (= x10 5950707087489713327630097374536055433359970814342252235411810230289552242107))

; alt



; (assert (and
;     (not (= x1 0))
;     (not (= x2 0))
;     (= x35 0)
;     (= x36 0)
;     (= x45 0)
;     (= x46 0)
;     (= x10 0)
; ))

(assert (and
    (not (= x1 0))
    (not (= x2 0))
    (not (= x35 0))
    (not (= x36 0))
    (not (= x45 0))
    (not (= x46 0))
    (not (= x10 0))
))


; (assert (not (= x2 y2)))

(check-sat)
(get-model)