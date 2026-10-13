; The unsat direction of the string/regex path: "ab" is in ab c*, so P("ab") must hold and the
; query P(s) /\ s in "ab" => false cannot be satisfied.  Expected: unsat.
(set-logic HORN)
(declare-fun P (String) Bool)
(assert (forall ((s String)) (=> (str.in.re s (re.++ (str.to.re "ab") (re.* (str.to.re "c")))) (P s))))
(assert (forall ((s String)) (=> (and (P s) (str.in.re s (str.to.re "ab"))) false)))
(check-sat)
