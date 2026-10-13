(set-logic ALL)
(declare-const |#tvar2| Int)
(assert (= (lambda ((i Int)) i) (lambda ((j Int)) |#tvar2|)))
(check-sat)
