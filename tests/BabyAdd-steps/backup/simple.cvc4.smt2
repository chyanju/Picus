(set-logic QF_NIA)
(declare-const p Int)
(assert (= p 21888242871839275222246405745257275088548364400416034343698204186575808495617))

(declare-const x1 Int)
(declare-const x2 Int)
(declare-const x3 Int)
(declare-const x4 Int)
(declare-const x5 Int)
(declare-const x6 Int)
(declare-const x10 Int)
(assert (and (<= 0 x1) (< x1 p)))
(assert (and (<= 0 x2) (< x2 p)))
(assert (and (<= 0 x3) (< x3 p)))
(assert (and (<= 0 x4) (< x4 p)))
(assert (and (<= 0 x5) (< x5 p)))
(assert (and (<= 0 x6) (< x6 p)))
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
                (* a (* x3 x5))
                (* (- p 1) (* x4 x6))
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
            (* x3 x6)
            (* x4 x5)
        )
        p
    )
))

(assert (=
    x10
    (mod
        (* x3 (* x4 (* x5 x6)))
        p
    )
))

(assert (= x10 5950707087489713327630097374536055433359970814342252235411810230289552242107))

; alt



; (assert (and
;     (not (= x1 0))
;     (not (= x2 0))
;     (= x3 0)
;     (= x4 0)
;     (= x5 0)
;     (= x6 0)
;     (= x10 0)
; ))

(assert (and
    (not (= x1 0))
    (not (= x2 0))
    (not (= x3 0))
    (not (= x4 0))
    (not (= x5 0))
    (not (= x6 0))
    (not (= x10 0))
))


; (assert (not (= x2 y2)))

(check-sat)
(get-model)