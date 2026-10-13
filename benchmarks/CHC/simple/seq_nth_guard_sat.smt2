; expected: sat
;
; `P(x, k) := x != 0` satisfies all eight clauses in every model of the theory,
; so the problem is satisfiable. It answered `unsat,0` -- from preprocessing,
; without a single CEGIS round -- because `seq.nth` was missing from the list of
; symbols whose value the theory leaves open. A read outside a sequence is
; unspecified, so `(seq.nth (as seq.empty (Seq Int)) 0)` denotes a value that is
; fixed within a model and different across models. For a guard over such a term
; Z3's "invalid" means "false in SOME model", not "false"; reading it as "false"
; let the clause be strengthened by dropping the guard, and the eight
; strengthened clauses contradict each other.
;
; NOT CURRENTLY ANSWERED: the wrong `unsat` is gone and the CEGIS loop now runs,
; but it does not converge -- the two guards are contradictory, so no example
; ever becomes unguarded, and the qualifier the solution needs (`x != 0` over the
; atom's first argument) is not among those the guards generate. The file is
; kept as the reproducer for the classification and as the acceptance test for
; that second half.
;
; The four-clause and two-clause reductions of this answer `sat,0`, because
; preprocessing eliminates the predicate before the offending step is reached;
; only the eight-clause form exercises it.
(set-logic HORN)
(declare-fun P (Int Int) Bool)
(assert (=> (= (seq.nth (as seq.empty (Seq Int)) 0) 0) (not (P (seq.nth (as seq.empty (Seq Int)) 0) 0))))
(assert (=> (= (seq.nth (as seq.empty (Seq Int)) 0) 0) (not (P (seq.nth (as seq.empty (Seq Int)) 0) 1))))
(assert (=> (= (seq.nth (as seq.empty (Seq Int)) 0) 0) (not (P (seq.nth (as seq.empty (Seq Int)) 0) 2))))
(assert (=> (= (seq.nth (as seq.empty (Seq Int)) 0) 0) (not (P (seq.nth (as seq.empty (Seq Int)) 0) 3))))
(assert (=> (not (= (seq.nth (as seq.empty (Seq Int)) 0) 0)) (P (seq.nth (as seq.empty (Seq Int)) 0) 0)))
(assert (=> (not (= (seq.nth (as seq.empty (Seq Int)) 0) 0)) (P (seq.nth (as seq.empty (Seq Int)) 0) 1)))
(assert (=> (not (= (seq.nth (as seq.empty (Seq Int)) 0) 0)) (P (seq.nth (as seq.empty (Seq Int)) 0) 2)))
(assert (=> (not (= (seq.nth (as seq.empty (Seq Int)) 0) 0)) (P (seq.nth (as seq.empty (Seq Int)) 0) 3)))
(check-sat)
