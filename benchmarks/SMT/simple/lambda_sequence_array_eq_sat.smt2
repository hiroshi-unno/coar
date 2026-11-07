; C495 positive control: the arrays differ only before the overwritten cell.
(set-logic ALL)
(assert (= (seq.unit (store (lambda ((x Int)) x) 7 0))
           (seq.unit (store (lambda ((x Int)) (ite (= x 7) 1 x)) 7 0))))
(check-sat)
