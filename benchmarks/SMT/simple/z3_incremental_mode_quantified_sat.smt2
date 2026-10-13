; A satisfiable quantified goal that Z3 4.15.2 decides only in a fresh context.
; Asked in a solver that has been pushed, or in a context holding any recursive
; function definition (used or not), it comes back "unknown (incomplete
; quantifiers)": the solver is then in incremental mode and answers with the
; smt core alone, without the tactic preprocessing (elimination of
; unconstrained terms) that decides it.  test/z3_incremental_canary.ml reads
; this file and reports when a Z3 version stops behaving this way.
(declare-sort a3 0) (declare-sort a0 0) (declare-sort a1 0)
(declare-datatypes ((T 0)) (((tup (p0 (Array Int a3)) (p1 Int)))))
(declare-const A (Array a0 (Array T (Array a0 Bool))))
(declare-const B (Array a1 (Array a3 Bool)))
(declare-const C (Array a1 (Array a3 Bool)))
(declare-const D (Array a0 Bool))
(declare-const E a0) (declare-const F a1) (declare-const G a0) (declare-const H a3)
; the negated validity question of one constraint of a Rust-derived problem,
; after the one-point rule and the splitting of tuple-sorted binders
(assert (select D E)) (assert (select D G)) (assert (not (select (select B F) H)))
(assert (forall ((x a0) (f (Array Int a3))) (or (select (select C F) (select f 0)) (not (select (select (select A G) (tup f 1)) x)))))
(assert (forall ((f (Array Int a3))) (select (select (select A G) (tup f 0)) G)))
(assert (forall ((f (Array Int a3))) (or (select (select (select A G) (tup f 1)) E) (not (= H (select f 0))))))
(check-sat)
