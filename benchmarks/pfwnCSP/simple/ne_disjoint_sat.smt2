; Two non-empty predicates that must be disjoint.  P := (x = 0) and
; Q := (x = 1) is a solution, so the problem is satisfiable.  An example clause
; {not P(x), not Q(x)} over one shared parameter x must keep both atoms: the
; clause is (forall x. not P(x) \/ not Q(x)), and dropping an atom because its
; predicate is non-empty is sound only when the atom's variables occur nowhere
; else in the clause.  Dropping both yields the empty clause, a refutation of
; this satisfiable system.
(set-logic HORN)
(declare-nep P (Int) Bool)
(declare-nep Q (Int) Bool)
(assert (forall ((x Int)) (=> (and (P x) (Q x)) false)))
(check-sat)
