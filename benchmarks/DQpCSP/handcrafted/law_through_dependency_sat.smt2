; A loop whose invariant must name a universal relation that the loop body never writes.
; `hist` is a reflexive, transitive relation containing every `step`; the loop advances `g`
; by `step` and the goal asks `hist(f0, g)` on exit.  The invariant `Inv(f0, g) := hist(f0, g)`
; is a solution under the stated problem ("for every lawful hist"), and `Inv` lists `hist` in its
; dependency set.  The clause entering the loop and the loop clause write `hist` nowhere, so a
; law inserted only where its function is mentioned leaves them demanded for every relation,
; reflexive or not; with the law also inserted where a dependent unknown is applied
; (PCSat's `law_reach_dependents`), the invariant above is a solution.  Expected `sat`.
(set-logic DQHORN)
(declare-forall-sort a)
(declare-forall-fun step (a a) Bool)
(declare-forall-fun hist (a a) Bool :law
  (and (forall ((x a)) (hist x x))
       (forall ((x a) (y a) (z a)) (=> (and (hist x y) (hist y z)) (hist x z)))
       (forall ((x a) (y a)) (=> (step x y) (hist x y)))))
(declare-dep-exists-fun Inv (hist step) (a a) Bool)
(declare-forall-fun stop (a) Bool)
(assert (forall ((f a)) (Inv f f)))
(assert (forall ((f0 a) (g a) (g2 a)) (=> (and (Inv f0 g) (step g g2)) (Inv f0 g2))))
(assert (forall ((f0 a) (g a)) (=> (and (Inv f0 g) (stop g)) (hist f0 g))))
(check-sat)
