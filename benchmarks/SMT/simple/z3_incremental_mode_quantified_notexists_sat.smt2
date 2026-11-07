; The goal of z3_incremental_mode_quantified_sat.smt2 with each universal
; assertion written as (not (exists ... (not ...))), the shape that Z3 4.15.2
; answered without its default preprocessing even in a fresh context.
; test/z3_incremental_canary.ml asks both and reports when they differ.
(declare-sort a3 0) (declare-sort a0 0) (declare-sort a1 0)
(declare-datatypes ((T 0)) (((tup (p0 (Array Int a3)) (p1 Int)))))
(declare-const A (Array a0 (Array T (Array a0 Bool))))
(declare-const B (Array a1 (Array a3 Bool)))
(declare-const C (Array a1 (Array a3 Bool)))
(declare-const D (Array a0 Bool))
(declare-const E a0) (declare-const F a1) (declare-const G a0) (declare-const H a3)
(assert (select D E)) (assert (select D G)) (assert (not (select (select B F) H)))
(assert (not (exists ((x a0) (f (Array Int a3))) (not (or (select (select C F) (select f 0)) (not (select (select (select A G) (tup f 1)) x)))))))
(assert (not (exists ((f (Array Int a3))) (not (select (select (select A G) (tup f 0)) G)))))
(assert (not (exists ((f (Array Int a3))) (not (or (select (select (select A G) (tup f 1)) E) (not (= H (select f 0))))))))
(check-sat)
