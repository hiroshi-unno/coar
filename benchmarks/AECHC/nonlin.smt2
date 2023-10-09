(set-logic HORN)
(declare-fun X (Int) Bool)
(assert (forall ((x Int)) (exists ((y Int)) (X (* x y))) ))
(assert (=> (X 0) false))
