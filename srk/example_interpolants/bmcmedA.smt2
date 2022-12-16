(set-logic QF_LRA)

(declare-fun x0 () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)

(declare-fun x11 () Real)
(declare-fun x12 () Real)
(declare-fun x13 () Real)
(declare-fun x14 () Real)


(declare-fun y0 () Real)
(declare-fun y1 () Real)
(declare-fun y2 () Real)
(declare-fun y3 () Real)
(declare-fun y4 () Real)

(declare-fun y11 () Real)
(declare-fun y12 () Real)
(declare-fun y13 () Real)
(declare-fun y14 () Real)


(assert (and
    (<= x0 100000)
    (<= x1 100000)
    (<= x2 100000)
    (<= x3 100000)
    (<= x4 100000)

    (<= x11 100000)
    (<= x12 100000)
    (<= x13 100000)
    (<= x14 100000)

    (<= y0 100000)
    (<= y1 100000)
    (<= y2 100000)
    (<= y3 100000)
    (<= y4 100000)

    (<= y11 100000)
    (<= y12 100000)
    (<= y13 100000)
    (<= y14 100000)


    (= x0 0)
    (= y0 0)
    (or 
        (and (= x1 (+ x0 1)) (= y1 (+ y0 1)))
        (and (= x1 x0) (= y1 y0))
    )
    (or 
        (and (= x2 (+ x1 1)) (= y2 (+ y1 1)))
        (and (= x2 x1) (= y2 y1))
    )
    (or 
        (and (= x3 (+ x2 1)) (= y3 (+ y2 1)))
        (and (= x3 x2) (= y3 y2))
    )
    (or 
        (and (= x4 (+ x3 1)) (= y4 (+ y3 1)))
        (and (= x4 x3) (= y4 y3))
    )
))