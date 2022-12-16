(set-logic QF_LRA)

(declare-fun x0 () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun y0 () Real)
(declare-fun y1 () Real)
(declare-fun y2 () Real)

(assert (and
    (<= x0 100000)
    (<= x1 100000)
    (<= x2 100000)
    (<= y0 100000)
    (<= y1 100000)
    (<= y2 100000)
    (= x0 0)
    (= y0 0)
    (or 
        (and (= x1 (+ x0 1)) (= y1 (+ y0 1)))
        (and (= x1 x0) (= y1 y0))
    )
))