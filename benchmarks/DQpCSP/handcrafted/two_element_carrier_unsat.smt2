; The minimal witness for the labeler's [pex_instances]:
; a refutation that needs ONE parametric example at TWO different instances.
;
; The clause forces, for any two distinct elements x and y, both P(x) and not P(y).  On a
; one-element carrier the premise (distinct x y) never holds and P := true is a solution; on a
; carrier with two elements u and v it demands P(u) and not P(v) from the instance (x,y)=(u,v)
; and P(v) and not P(u) from (x,y)=(v,u), which is a contradiction.  A forall-sort is *every*
; non-empty type, so the problem is unsat.
;
; The refutation is out of reach of the default labeling: every parametric example is
; instantiated at the constants of its parameters' canonical names, so the positive P($1) and
; the negative P($2) land on different constants and never collide, and the propositional
; abstraction refutes only through collisions.  With pex_instances > 1 the example is also
; instantiated under the swap $1 <-> $2, the two atoms collide, and the guard $1 != $2 is
; satisfiable, so the conflict stands.  expected: unsat with
; config/solver/pcsat_wopp_tbq_ar_pex3.json; no answer with pcsat_wopp_tbq_ar.json
(set-logic QHORN)
(declare-forall-sort a)
(declare-fun P (a) Bool)
(assert (forall ((x a) (y a)) (=> (distinct x y) (P x))))
(assert (forall ((x a) (y a)) (=> (and (distinct x y) (P y)) false)))
(check-sat)
