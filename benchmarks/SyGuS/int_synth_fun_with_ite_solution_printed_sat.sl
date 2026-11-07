; An Int-valued synth-fun whose solution needs a conditional: the maximum.
(set-logic LIA)
(synth-fun max2 ((a Int) (b Int)) Int)
(declare-var x Int)
(declare-var y Int)
(constraint (>= (max2 x y) x))
(constraint (>= (max2 x y) y))
(constraint (or (= (max2 x y) x) (= (max2 x y) y)))
(check-synth)
