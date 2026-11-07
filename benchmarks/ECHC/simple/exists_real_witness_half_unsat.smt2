; The negation of exists_real_witness_half_sat.smt2: the conclusion still asks
; for some r strictly between 0 and 1 in Q, and the first clause now forbids Q
; from holding anywhere in that interval, so no interpretation of Q satisfies
; all three clauses.
; Expected: unsat (z3: unsat).
(set-logic HORN)
(declare-fun Q (Real) Bool)
(assert (forall ((r Real)) (=> (Q r) (or (<= r 0.0) (>= r 1.0)))))
(assert (forall ((r Real)) (=> (and (Q r) (< r 10.0)) (Q (+ r 1.0)))))
(assert (forall ((x Int)) (=> (> x 0) (exists ((r Real)) (and (> r 0.0) (< r 1.0) (Q r))))))
(check-sat)
