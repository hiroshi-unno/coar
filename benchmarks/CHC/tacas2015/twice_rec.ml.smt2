(set-logic HORN)
(set-info :source |
  Benchmark: ./benchmarks/ocaml/safety/tacas2015//twice_rec.ml
  Generated by Refinement Caml
|)
(set-info :status unknown)
(declare-fun |$P4| (Int Int) Bool)
(declare-fun |$P3| (Int Int) Bool)
(declare-fun |$P0| (Int) Bool)
(declare-fun |$P1| (Int) Bool)
(declare-fun |$P2| (Int Int) Bool)
(declare-fun |$P5| (Int Int Int) Bool)
(assert (forall ((x1 Int)(x0 Int)) (=> (|$P4| x0 x1) (|$P1| x1))))
(assert (forall ((x2 Int)(x0 Int)(x1 Int)) (=> (and (|$P4| x0 x1) (|$P3| x1 x2)) (|$P1| x2))))
(assert (forall ((x0 Int)(x1 Int)(x3 Int)(x2 Int)) (=> (and (|$P4| x0 x1) (and (|$P3| x1 x2) (|$P3| x2 x3))) (|$P5| x0 x1 x3))))
(assert (forall ((x1 Int)(x0 Int)) (=> (and (|$P0| x1) (and (= x0 1) (<= x1 0))) (|$P2| x1 x0))))
(assert (forall ((x0 Int)(x1 Int)) (=> (and (|$P0| x1) (and (>= x1 1) (= x1 (+ 1 x0)))) (|$P0| x0))))
(assert (forall ((x1 Int)(x0 Int)(x2 Int)(x3 Int)) (=> (and (|$P0| x1) (and (|$P2| x2 x3) (and (>= x1 1) (and (= x1 (+ 1 x2)) (= x0 (+ 2 x3)))))) (|$P2| x1 x0))))
(assert (forall ((x0 Int)) (=> (|$P1| x0) (|$P0| x0))))
(assert (forall ((x0 Int)(x1 Int)) (=> (and (|$P1| x0) (|$P2| x0 x1)) (|$P3| x0 x1))))
(assert (forall ((x0 Int)(x1 Int)) (|$P4| x0 x1)))
(assert (not (exists ((x2 Int)(x0 Int)(x1 Int)) (and (|$P5| x0 x1 x2) (or (< x2 0) (> x2 0))))))
(check-sat)
