(set-logic QF_LRA)

(declare-fun x () Real)
(declare-fun y () Real)

(assert (or 
  (and (<= x 1) (<= y 3)) 
  (and (<= x 2) (<= 1 x) (<= y 2)) 
  (and (<= 2 x) (<= x 3) (<= y 1))))