(set-logic SYGUS)

(declare-fun max (Int Int) Int)

(declare-var x Int)
(declare-var y Int)

(assert (>= (max x y) x))
(assert (>= (max x y) y))
(assert (or (= x (max x y)) (= y (max x y))))

(check-sat)

