; A head existential whose witness must come from the universals.  Q depends on R (the default:
; R is the Bool forall-fun declared before it).  Q := R is a solution: (1) if R holds at the
; universal constant c then some y satisfies Q, namely y := c; (2) Q is contained in R.
;
; What the solver does with the head exists is Skolemise it into an FN unknown whose arguments
; are the clause's *first-order* universals only -- here none, since c and R are problem-level
; universals of the reduction (array-sorted and constant term variables) and never enter the
; Skolem function's argument list.  The Skolemised problem therefore asks for ONE integer f
; with Q(R, f) whenever R(c), for every R and c, and R := {c} with c != f refutes it: the problem
; actually solved is strictly stronger than this one and is unsatisfiable, so the solver cannot
; answer sat here (measured 2026-09-12: no answer in 30 s under pcsat_tbq_ar and
; pcsat_wopp_tbq_ar).  A refutation of the stronger problem would be a wrong unsat.
; The faithful Skolem function takes c (or R) as an argument: f(c) := c.  expected: sat
(set-logic DQHORN)
(declare-forall-fun R (Int) Bool)
(declare-forall-fun c () Int)
(declare-fun Q (Int) Bool)
(assert (=> (R c) (exists ((y Int)) (Q y))))
(assert (forall ((y Int)) (=> (Q y) (R y))))
(check-sat)
