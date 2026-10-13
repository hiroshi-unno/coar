; A universal *function* whose value reaches an
; unknown through a NON-INJECTIVE map (absolute value).  P holds f(0), Q holds |f(0)|, and Q is
; forced to be a singleton.  Solution: P(f,x) := (x = f[0]), Q(f,z) := (z = |f[0]|).  The graph
; translation with a universal predicate instead of f is unsat (forall_fun_abs_graph_unsat.smt2),
; and no quantifier-free predicate-only problem simulates this one.
; expected: sat
(set-logic DQHORN)
(declare-forall-fun f (Int) Int)
(declare-dep-exists-fun P (f) (Int) Bool)
(declare-dep-exists-fun Q (f) (Int) Bool)
(assert (P (f 0)))
(assert (forall ((y Int)) (=> (and (P y) (>= y 0)) (Q y))))
(assert (forall ((y Int)) (=> (and (P y) (< y 0)) (Q (- y)))))
(assert (forall ((z Int) (z2 Int)) (=> (and (Q z) (Q z2) (distinct z z2)) false)))
(check-sat)
