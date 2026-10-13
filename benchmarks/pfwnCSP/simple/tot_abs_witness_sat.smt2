; Satisfiable.  A total predicate whose witness needs a guarded function of the universal
; position: P is declared total over its first argument (position 0) and occurs only negatively,
; so a solution is any total P whose every point satisfies the body.
;
; The problem is  forall x. exists y. y >= 0 /\ (y = x \/ y = -x),  whose only witness is |x|.
; Solution: P(x, y) := (x >= 0 /\ y = x) \/ (x < 0 /\ y = -x), the graph of |x|.  It is not the
; graph of any unguarded affine function y = c0 + c1*x (c1 = 1 fails at x = -1, c1 = -1 at x = 1,
; any other c1 at x = 0 or x = 1), so the per-position affine witness template cannot state it,
; while a guarded piecewise witness (the functional predicate's template) can, with two cases.
; Expected of a correct run: sat, or no answer; never unsat.
(set-logic HORN)
(declare-totp (0) P (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (P x y) (and (>= y 0) (or (= y x) (= y (- x)))))))
(check-sat)
