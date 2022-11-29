(set-logic QF_LRA)

(declare-fun x () Int)
(declare-fun y () Int)

(assert (or
  (and (<= 2 x) (<= 3 y))
  (and (<= 3 x) (<= 2 y) (<= y 3))
))