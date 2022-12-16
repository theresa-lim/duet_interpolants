(set-logic QF_LRA)

(declare-fun x () Real)
(declare-fun y () Real)

(assert (or
  (and (<= 2 x) (<= 3 y))
  (and (<= 3 x) (<= 2 y) (<= y 3))
))