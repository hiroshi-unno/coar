; A law on a universally quantified function reaches a clause that applies the function only
; inside a define-fun body -- the shape a front end produces when a trait method is routed
; through one definition per implementation.  `:law` inserts its premise into every following
; assertion that mentions the function directly or through the transitive bodies of the
; definitions it applies, so the first clause below gets the premise (it reaches `fresh`
; through `step`) and the second does not (`same` never reaches it).
;
; With the premise the problem is sat, Q(x, y) := (x != y).  Without it `fresh` may be the
; identity, the first clause then forces Q(x, x), the second forbids it, and the problem is
; unsat -- which is what the reader produced while only a literal mention of `fresh` counted.
;
; expected: sat
(set-logic DQHORN)
(declare-forall-sort a)
(declare-forall-fun fresh (a) a :law (distinct (fresh x) x))
(define-fun step ((x a) (y a)) Bool (= y (fresh x)))
(define-fun same ((x a) (y a)) Bool (= x y))
(declare-fun Q (a a) Bool)
(assert (forall ((x a) (y a)) (=> (step x y) (Q x y))))
(assert (forall ((x a) (y a)) (=> (and (Q x y) (same x y)) false)))
(check-sat)
