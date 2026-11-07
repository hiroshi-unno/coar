; A universally quantified Boolean c that the existential y answers, and an equality between two
; Boolean variables: satisfiable (with d equal to c, y above x when c holds and below it otherwise).
(set-logic LRA)
(declare-fun x () Real)
(assert (forall ((c Bool)) (exists ((d Bool) (y Real))
  (and (= d c) (=> d (> y x)) (=> (not d) (< y x))))))
(check-sat)
