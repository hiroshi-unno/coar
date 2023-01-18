(set-logic HORN)
(set-info :source |
  Benchmark: ./benchmarks/ocaml/safety/tacas2015//max_commutative.ml
  Generated by Refinement Caml
|)
(set-info :status unknown)
(declare-fun |$P0| (Int) Bool)
(declare-fun |$P1| (Int Int) Bool)
(declare-fun |$P2| (Int Int Int) Bool)
(assert (forall ((x0 Int)(x1 Int)(x2 Int)) (=> (and (|$P0| x0) (and (|$P1| x0 x1) (and (|$P0| x2) (and (> x0 x1) (= x2 x0))))) (|$P2| x0 x1 x2))))
(assert (forall ((x1 Int)(x0 Int)(x2 Int)) (=> (and (|$P0| x1) (and (|$P1| x1 x0) (and (|$P1| x1 x2) (and (<= x1 x0) (= x2 x0))))) (|$P2| x1 x0 x2))))
(assert (forall ((x0 Int)) (|$P0| x0)))
(assert (forall ((x0 Int)(x1 Int)) (|$P1| x0 x1)))
(assert (forall ((x1 Int)(x0 Int)(x2 Int)) (=> (|$P2| x0 x1 x2) (|$P0| x1))))
(assert (forall ((x1 Int)(x0 Int)(x2 Int)) (=> (|$P2| x0 x1 x2) (|$P1| x1 x0))))
(assert (not (exists ((x0 Int)(x3 Int)(x2 Int)(x1 Int)) (and (|$P2| x2 x1 x0) (and (|$P2| x1 x2 x3) (or (< x0 x3) (> x0 x3)))))))
(check-sat)
