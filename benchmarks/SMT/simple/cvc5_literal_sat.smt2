; The negation is satisfiable.  Translating operator names for cvc5 (ubv_to_int to bv2nat) must
; change neither a string literal nor a bound name, or cvc5 proves a false formula.
(set-logic ALL)
(assert (not (= "ubv_to_int" "bv2nat")))


(check-sat)
