(set-logic QF_LRA)

(declare-fun x () Real)
(declare-fun y () Real)

(assert (or 
  (and (<= x 1) (<= y 9)) 
  (and (<= x 2) (<= y 6)) 
  (and (<= x 3) (<= y 3))))