(set-logic HORN)
(assert (forall ((x Int) (y Int) (z Int))
  (=> (and (> x 0) (> y 0) (> z 0) (= (+ (* x x x) (* y y y)) (* z z z))) false)))
(check-sat)
