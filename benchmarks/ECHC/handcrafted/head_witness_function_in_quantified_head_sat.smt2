; A head existential whose witness reaches a quantified subformula of another clause after resolution.
; Read with head existentials Skolemised into FUNCTIONS (not functional predicates), the witness y of
; clause 2 becomes f(x); resolving R away puts f(x) under the (pure) existential of clause 3's head, as
; part of a Boolean equality the eliminator expands, and the clausification of that resolvent met a
; quantifier with an unknown (the function f) under it.  The clause stays a disjunction with the
; quantified subformula as one disjunct.  Satisfiable: P := (x = 0), Q := R := (y = 0), y := 0.
; expected: sat
(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(declare-fun R (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int)) (=> (P x) (exists ((y Int)) (and (Q y) (R y))))))
(assert (forall ((z Int)) (=> (R z) (exists ((i Int)) (and (> i z) (< i (+ z 2)))))))
(assert (forall ((y Int)) (=> (Q y) (>= y 0))))
(check-sat)
