; A constructor qualification fixes its result datatype instance.
(set-logic ALL)
(declare-datatype E (par (T) ((a) (b))))
(declare-const x (E Bool)) (declare-const y (E Int))
(assert (= x (as a (E Bool)))) (assert (= y (as b (E Int))))
(assert (not (= x (as b (E Bool))))) (assert (not (= y (as a (E Int)))))
(check-sat)
