; An existential head over Real whose only witnesses are not integers: the
; conclusion asks for some r strictly between 0 and 1 in Q, and the first
; clause keeps Q out of [0.8, 1), so a witness lies in (0, 0.8).  Q(r) :=
; r >= 0 /\ (r < 0.8 \/ r >= 1) satisfies all three clauses, with r = 1/2 a
; witness.  Neither the upper bound the first clause gives Q nor its one
; unfolding through the recursive clause is closed under r -> r + 1 (both
; hold at -1.1 and not at -0.1), so Q and the witness have to be synthesised
; together; a solver that offers a real witness only integer values never
; finds one.
; Expected: sat (z3: sat).
(set-logic HORN)
(declare-fun Q (Real) Bool)
(assert (forall ((r Real)) (=> (Q r) (or (< r 0.8) (>= r 1.0)))))
(assert (forall ((r Real)) (=> (and (Q r) (< r 10.0)) (Q (+ r 1.0)))))
(assert (forall ((x Int)) (=> (> x 0) (exists ((r Real)) (and (> r 0.0) (< r 1.0) (Q r))))))
(check-sat)
