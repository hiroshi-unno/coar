(set-logic OMT_QF_NRA)

(declare-fun x () Real)
(declare-fun y () Real)

(assert (and 
  (>= x 0)
  (>= y 0)
  (<= x 10)
  (<= y 10)
  (>= (- (* x x) y) 1)
))

(minimize (+ (* x x) (* y y)))

(check-sat)
(get-objectives)
(get-model)
