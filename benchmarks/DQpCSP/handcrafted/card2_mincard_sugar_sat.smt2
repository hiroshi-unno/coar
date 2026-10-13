; card2_constants_sat.smt2 written with the :min-card sugar: the front end expands
; (declare-forall-sort a :min-card 2) into two universal constants #card_a_0, #card_a_1 of
; sort a and a (distinct ...) premise in every following assertion.
; The generated names may be used in the clauses.  expected: sat
(set-logic DQHORN)
(declare-forall-sort a :min-card 2)
(declare-fun P (a a a) Bool)
(assert (forall ((x a)) (=> (= x #card_a_0) (P #card_a_0 #card_a_1 x))))
(assert (forall ((x a)) (=> (and (P #card_a_0 #card_a_1 x) (= x #card_a_1)) false)))
(check-sat)
