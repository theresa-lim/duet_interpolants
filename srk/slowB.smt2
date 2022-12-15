(set-logic QF_LRA)

(declare-fun x () Real)
(declare-fun y () Real)

(assert (or
  (and (< 1 x) (< 6 y))
  (and (< 2 x) (< 4 y))
  (and (< 3 x) (< 2 y))
))