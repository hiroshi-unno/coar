(set-logic QF_LIA)
(set-option :produce-models true)
(declare-fun x () Int)


(assert (and (not (= x 1)) (or (<= x 0) (> x 2) (= x 1))))
(check-sat)
(exit)
