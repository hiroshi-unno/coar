(set-logic HORN)
(set-info :source |
  Benchmark: ./benchmarks/ocaml/safety/tacas2015//enc-rev_accum.ml
  Generated by Refinement Caml
|)
(set-info :status unknown)
(declare-fun |$P0| (Int) Bool)
(declare-fun |$P1| (Int Int) Bool)
(declare-fun |$P2| (Int Int Int) Bool)
(assert (forall ((x1 Int)(x0 Int)(x2 Int)) (=> (and (|$P0| x1) (and (|$P1| x1 x0) (and (|$P1| x1 x2) (and (= x1 0) (= x2 x0))))) (|$P2| x1 x0 x2))))
(assert (forall ((x1 Int)(x2 Int)(x0 Int)(x3 Int)) (=> (and (|$P0| x2) (and (|$P1| x2 x3) (and (or (< x2 0) (> x2 0)) (and (= x0 (+ 1 x3)) (= x2 (+ 1 x1)))))) (|$P0| x1))))
(assert (forall ((x0 Int)(x1 Int)(x2 Int)(x3 Int)) (=> (and (|$P0| x2) (and (|$P1| x2 x3) (and (or (< x2 0) (> x2 0)) (and (= x2 (+ 1 x0)) (= x1 (+ 1 x3)))))) (|$P1| x0 x1))))
(assert (forall ((x0 Int)(x1 Int)(x4 Int)(x2 Int)(x3 Int)) (=> (and (|$P0| x0) (and (|$P1| x0 x1) (and (|$P2| x2 x3 x4) (and (or (< x0 0) (> x0 0)) (and (= x0 (+ 1 x2)) (= x3 (+ 1 x1))))))) (|$P2| x0 x1 x4))))
(assert (forall ((x0 Int)) (|$P0| x0)))
(assert (forall ((x0 Int)(x1 Int)) (=> (= x1 0) (|$P1| x0 x1))))
(assert (not (exists ((x1 Int)(x0 Int)) (and (|$P2| x0 0 x1) (<= (+ 1 x1) x0)))))
(check-sat)
