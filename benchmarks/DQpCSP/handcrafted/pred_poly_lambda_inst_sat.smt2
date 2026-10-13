; Predicate polymorphism as DQCHC.  The library function
;   twice : forall X. (x:{a | X a}) -> (f : (a:{X}) -> {b | X b}) -> {r | P(X, x, r)}
; applies its argument twice; its postcondition P is an unknown that depends on the universally
; quantified contract X of the argument (the generalization side, verified once for every X).
; Two clients instantiate X at definable predicates by passing a lambda array (the
; instantiation side): X1 := (>= 0) with f = (+1), and X2 := (= 5) with f = id.  P is written
; with an explicit array argument, i.e. the dependency passed as an argument by hand, because the front
; end prepends declared dependencies itself and has no syntax for instantiating one.
; P(X, x, r) := X[x] /\ X[r] is a solution.  expected: sat
(set-logic DQHORN)
(declare-forall-fun X (Int) Bool)
(declare-dep-exists-fun P () ((Array Int Bool) Int Int) Bool)
; library body: m = f x, r = f m, each call uses f's contract X
(assert (forall ((x Int) (m Int) (r Int)) (=> (and (X x) (X m) (X r)) (P X x r))))
; client 1: x = 0, f = (+1) preserves (>= 0); the result must be non-negative
(assert (forall ((r Int)) (=> (and (P (lambda ((a Int)) (>= a 0)) 0 r) (< r 0)) false)))
; client 2: x = 5, f = id preserves (= 5); the result must be 5
(assert (forall ((r Int)) (=> (and (P (lambda ((a Int)) (= a 5)) 5 r) (not (= r 5))) false)))
(check-sat)
