(set-logic HORN)
(set-info :source |
  Benchmark: ./benchmarks/ocaml/safety/tacas2015//enc-zip3.ml
  Generated by Refinement Caml
|)
(set-info :status unknown)
(declare-fun |$P0| (Int) Bool)
(declare-fun |$P1| (Int Int) Bool)
(declare-fun |$P2| (Int) Bool)
(declare-fun |$P3| (Int Int) Bool)
(declare-fun |$P4| (Int Int Int) Bool)
(assert (forall ((x0 Int)(x1 Int)) (=> (|$P0| x1) (|$P0| x0))))
(assert (forall ((x0 Int)(x2 Int)(x1 Int)) (=> (and (|$P0| x0) (|$P1| x1 x2)) (|$P1| x0 x2))))
(assert (forall ((x1 Int)(x2 Int)(x0 Int)) (=> (and (|$P2| x1) (and (|$P3| x1 x2) (and (= x0 0) (and (= x1 0) (= x2 0))))) (|$P4| x1 x2 x0))))
(assert (forall ((x0 Int)(x1 Int)) (=> (and (|$P2| 0) (and (|$P3| 0 x1) (or (< x1 0) (> x1 0)))) (|$P0| x0))))
(assert (forall ((x0 Int)(x1 Int)(x3 Int)(x2 Int)) (=> (and (|$P2| x0) (and (|$P3| x0 x1) (and (|$P1| x2 x3) (and (or (< x1 0) (> x1 0)) (= x0 0))))) (|$P4| x0 x1 x3))))
(assert (forall ((x0 Int)(x1 Int)) (=> (and (|$P2| x1) (and (|$P3| x1 0) (or (< x1 0) (> x1 0)))) (|$P0| x0))))
(assert (forall ((x0 Int)(x1 Int)(x3 Int)(x2 Int)) (=> (and (|$P2| x0) (and (|$P3| x0 x1) (and (|$P1| x2 x3) (and (or (< x0 0) (> x0 0)) (= x1 0))))) (|$P4| x0 x1 x3))))
(assert (forall ((x1 Int)(x2 Int)(x3 Int)(x0 Int)) (=> (and (|$P2| x2) (and (|$P3| x2 x3) (and (and (or (< x2 0) (> x2 0)) (or (< x3 0) (> x3 0))) (and (= x3 (+ 1 x0)) (= x2 (+ 1 x1)))))) (|$P2| x1))))
(assert (forall ((x0 Int)(x1 Int)(x2 Int)(x3 Int)) (=> (and (|$P2| x2) (and (|$P3| x2 x3) (and (and (or (< x2 0) (> x2 0)) (or (< x3 0) (> x3 0))) (and (= x2 (+ 1 x0)) (= x3 (+ 1 x1)))))) (|$P3| x0 x1))))
(assert (forall ((x1 Int)(x2 Int)(x0 Int)(x3 Int)(x4 Int)(x5 Int)) (=> (and (|$P2| x1) (and (|$P3| x1 x2) (and (|$P4| x3 x4 x5) (and (and (or (< x1 0) (> x1 0)) (or (< x2 0) (> x2 0))) (and (= x1 (+ 1 x3)) (and (= x2 (+ 1 x4)) (= x0 (+ 1 x5)))))))) (|$P4| x1 x2 x0))))
(assert (forall ((x0 Int)) (|$P2| x0)))
(assert (forall ((x1 Int)(x0 Int)) (=> (= x0 x1) (|$P3| x1 x0))))
(assert (not (exists ((x1 Int)(x0 Int)) (and (|$P4| x0 x0 x1) (or (< x1 x0) (> x1 x0))))))
(check-sat)
