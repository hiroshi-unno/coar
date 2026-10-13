; skolem_head_exists_universal_const_int_sat over a forall-sort.  Q := R is a solution (the
; witness of the head exists is the universal constant c).  Since the Skolem function for y
; receives neither c nor R, its range is the sort variable a and it has no argument of that sort
; to return, so the FN template generator stops with
;   Failure "[gen_fun] no argument of the universally quantified sort a to return: ..."
; (measured 2026-09-12: uncaught exception, exit 1, under pcsat_tbq_ar and pcsat_wopp_tbq_ar).
; The message is right that a witness exists; the reason none can be built is that the
; universals were left out of the Skolem function's arguments, not that the problem has no
; solution.  expected: sat
(set-logic DQHORN)
(declare-forall-sort a)
(declare-forall-fun R (a) Bool)
(declare-forall-fun c () a)
(declare-fun Q (a) Bool)
(assert (=> (R c) (exists ((y a)) (Q y))))
(assert (forall ((y a)) (=> (Q y) (R y))))
(check-sat)
