(set-logic QF_LRA)

(declare-fun x () Real)
(declare-fun y () Real)

(assert (and 
    (or 
        (and (<= x 1) (<= y 3)) 
        (and (<= x 2) (<= y 2)) 
        (and (<= x 3) (<= y 1))
    )
    (or
        (and (< 1 x) (< 3 y))
        (and (< 2 x) (< 2 y))
        (and (< 3 x) (< 1 y))
    )
)
)

(check-sat)
(get-model)