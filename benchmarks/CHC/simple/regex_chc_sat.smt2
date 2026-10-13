; A CHC over strings with str.in.re atoms.  Until 2026-09-06 the
; LogicOld->Logic bridge matched str.in.re with one argument and every such atom failed with
; "[Logic.of_old_pred_sym] str_in_regex not supported"; P := s in ab c* is a solution.  Expected: sat.
(set-logic HORN)
(declare-fun P (String) Bool)
(assert (forall ((s String)) (=> (str.in.re s (re.++ (str.to.re "ab") (re.* (str.to.re "c")))) (P s))))
(assert (forall ((s String)) (=> (and (P s) (not (str.in.re s (re.++ (str.to.re "ab") re.all)))) false)))
(check-sat)
