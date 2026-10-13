; Instantiation of a predicate-polymorphic library at an *inferred* predicate: the client's
; argument f has an unknown contract K (to be inferred: K := (>= 0) works), and the library's
; dependent postcondition P must be applied at K.  Since an unknown cannot be passed as an
; array argument, the client clause quantifies over the universal X and equates it with K by a
; universally quantified premise -- a forall in the body, i.e. a forall-exists clause.
; expected: sat
(set-logic DQHORN)
(declare-forall-fun X (Int) Bool)
(declare-dep-exists-fun P () ((Array Int Bool) Int Int) Bool)
(declare-fun K (Int) Bool)
(assert (forall ((x Int) (m Int) (r Int)) (=> (and (X x) (X m) (X r)) (P X x r))))
; f = (+1): its contract K must be preserved
(assert (forall ((a Int)) (=> (and (K a)) (K (+ a 1)))))
(assert (K 0))
; client: x = 0, result must be non-negative; P applied at X = K
(assert (forall ((r Int)) (=> (and (forall ((a Int)) (= (X a) (K a))) (P X 0 r) (< r 0)) false)))
(check-sat)
