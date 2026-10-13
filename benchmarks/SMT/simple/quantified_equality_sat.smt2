; expected: sat
;
; A control: this quantified query was answered under either strategy, so it is
; here to say that the repair is not needed for every quantifier -- and that it
; must not break the ones that already worked.
(set-logic ALL)
(assert (forall ((x Int)) (exists ((y Int)) (= y x))))
(check-sat)
