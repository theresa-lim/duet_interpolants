(set-logic QF_LRA)

(declare-fun x0 () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun y0 () Real)
(declare-fun y1 () Real)
(declare-fun y2 () Real)

(assert (and
    (>= x0 -100000)
    (>= x1 -100000)
    (>= x2 -100000)
    (>= y0 -100000)
    (>= y1 -100000)
    (>= y2 -100000)
    (or 
        (and (= x2 (- x1 1)) (= y2 (- y1 1)))
        (and (= x2 x1) (= y2 y1))
    )
    (= x2 0)
    (or (> y2 0) (< y2 0) )
))