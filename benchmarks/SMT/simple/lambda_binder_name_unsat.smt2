(set-logic ALL)
(declare-const i1 Int)
(assert (= (lambda ((i Int)) i) (lambda ((j Int)) i1)))
(check-sat)
