; The negation is satisfiable.  Translating operator names for cvc5 (ubv_to_int to bv2nat) must
; change neither a string literal nor a bound name, or cvc5 proves a false formula.
(set-logic ALL)
(declare-fun bv2nat_x () Int)
(assert (exists ((ubv_to_int_x Int)) (not (= ubv_to_int_x bv2nat_x))))


(check-sat)
