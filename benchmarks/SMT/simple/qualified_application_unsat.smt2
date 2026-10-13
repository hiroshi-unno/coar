; A constructor qualification fixes its result datatype instance.
(set-logic ALL)
(declare-datatype E (par (T) ((nil) (box (value T)))))
(declare-const x (E Bool))
(assert (= x ((as box (E Bool)) true))) (assert (not (value x)))
(check-sat)
