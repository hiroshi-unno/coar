(set-logic HORN)
(set-info :source |
  Benchmark: ./benchmarks/ocaml/safety/tacas2015//mc91_99.ml
  Generated by Refinement Caml
|)
(set-info :status unknown)
(declare-fun |$P0| (Int) Bool)
(declare-fun |$P1| (Int Int) Bool)
(assert (forall ((x1 Int)(x0 Int)) (=> (and (|$P0| x1) (and (>= x1 101) (= x1 (+ 10 x0)))) (|$P1| x1 x0))))
(assert (forall ((x0 Int)(x1 Int)) (=> (and (|$P0| x1) (and (<= x1 100) (= x0 (+ 11 x1)))) (|$P0| x0))))
(assert (forall ((x2 Int)(x0 Int)(x1 Int)) (=> (and (|$P0| x0) (and (|$P1| x1 x2) (and (<= x0 100) (= x1 (+ 11 x0))))) (|$P0| x2))))
(assert (forall ((x0 Int)(x3 Int)(x1 Int)(x2 Int)) (=> (and (|$P0| x0) (and (|$P1| x1 x2) (and (|$P1| x2 x3) (and (<= x0 100) (= x1 (+ 11 x0)))))) (|$P1| x0 x3))))
(assert (forall ((x0 Int)) (=> (<= x0 99) (|$P0| x0))))
(assert (not (exists ((x0 Int)(x1 Int)) (and (|$P1| x0 x1) (and (<= x0 99) (or (< x1 91) (> x1 91)))))))
(check-sat)
