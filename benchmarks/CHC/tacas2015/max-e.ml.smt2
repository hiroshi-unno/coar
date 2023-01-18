(set-logic HORN)
(set-info :source |
  Benchmark: ./benchmarks/ocaml/safety/tacas2015//max-e.ml
  Generated by Refinement Caml
|)
(set-info :status unknown)
(declare-fun |$P3| (Int Int) Bool)
(declare-fun |$P5| (Int Int Int Int) Bool)
(declare-fun |$P4| (Int Int Int) Bool)
(declare-fun |$P2| (Int Int Int) Bool)
(declare-fun |$P6| (Int) Bool)
(declare-fun |$P7| (Int Int) Bool)
(declare-fun |$P0| (Int) Bool)
(declare-fun |$P1| (Int Int) Bool)
(declare-fun |$P8| (Int Int Int Int Int) Bool)
(declare-fun |$P9| (Int Int Int) Bool)
(assert (forall ((x3 Int)(x2 Int)(x0 Int)(x1 Int)) (=> (and (|$P4| x2 x3 x0) (and (|$P5| x2 x3 x0 x1) (|$P3| x2 x3))) (|$P0| x3))))
(assert (forall ((x2 Int)(x3 Int)(x1 Int)(x0 Int)) (=> (and (|$P3| x1 x2) (and (|$P5| x1 x2 x3 x0) (|$P4| x1 x2 x3))) (|$P1| x2 x3))))
(assert (forall ((x4 Int)(x0 Int)(x2 Int)(x3 Int)(x1 Int)) (=> (and (|$P3| x0 x2) (and (|$P4| x0 x2 x3) (and (|$P5| x0 x2 x3 x1) (|$P2| x2 x3 x4)))) (|$P0| x4))))
(assert (forall ((x1 Int)(x4 Int)(x2 Int)(x3 Int)(x0 Int)) (=> (and (|$P3| x2 x3) (and (|$P5| x2 x3 x4 x0) (and (|$P2| x3 x4 x1) (|$P4| x2 x3 x4)))) (|$P1| x1 x4))))
(assert (forall ((x1 Int)(x2 Int)(x4 Int)(x0 Int)(x5 Int)(x3 Int)) (=> (and (|$P3| x1 x2) (and (|$P5| x1 x2 x4 x0) (and (|$P2| x2 x4 x3) (and (|$P4| x1 x2 x4) (|$P2| x3 x4 x5))))) (|$P8| x1 x2 x4 x0 x5))))
(assert (forall ((x0 Int)(x1 Int)(x2 Int)) (=> (and (|$P6| x0) (and (|$P7| x0 x1) (and (|$P6| x2) (and (>= x0 x1) (= x2 x0))))) (|$P9| x0 x1 x2))))
(assert (forall ((x1 Int)(x0 Int)(x2 Int)) (=> (and (|$P6| x1) (and (|$P7| x1 x0) (and (|$P7| x1 x2) (and (< x1 x0) (= x2 x0))))) (|$P9| x1 x0 x2))))
(assert (forall ((x0 Int)) (=> (|$P0| x0) (|$P6| x0))))
(assert (forall ((x0 Int)(x1 Int)) (=> (and (|$P0| x0) (|$P1| x0 x1)) (|$P7| x0 x1))))
(assert (forall ((x0 Int)(x1 Int)(x2 Int)) (=> (and (|$P0| x0) (and (|$P1| x0 x1) (|$P9| x0 x1 x2))) (|$P2| x0 x1 x2))))
(assert (forall ((x0 Int)(x1 Int)) (|$P3| x0 x1)))
(assert (forall ((x0 Int)(x1 Int)(x2 Int)) (|$P4| x0 x1 x2)))
(assert (forall ((x0 Int)(x1 Int)(x2 Int)(x3 Int)) (|$P5| x0 x1 x2 x3)))
(assert (forall ((x1 Int)(x0 Int)(x2 Int)(x3 Int)(x4 Int)) (=> (|$P8| x0 x1 x2 x3 x4) (|$P6| x1))))
(assert (forall ((x1 Int)(x4 Int)(x0 Int)(x2 Int)(x3 Int)) (=> (|$P8| x0 x1 x2 x3 x4) (|$P7| x1 x4))))
(assert (forall ((x2 Int)(x0 Int)(x6 Int)(x5 Int)(x1 Int)(x4 Int)(x3 Int)) (=> (and (|$P8| x1 x4 x2 x3 x5) (and (|$P9| x4 x5 x6) (or (and (> x0 0) (= x6 x5)) (and (not (> x0 0)) (not (= x6 x5)))))) (|$P6| x2))))
(assert (forall ((x4 Int)(x6 Int)(x0 Int)(x1 Int)(x3 Int)(x2 Int)(x5 Int)) (=> (and (|$P9| x3 x6 x1) (and (|$P8| x2 x3 x4 x5 x6) (or (and (> x0 0) (= x1 x6)) (and (not (> x0 0)) (not (= x1 x6)))))) (|$P7| x4 x6))))
(assert (forall ((x3 Int)(x0 Int)(x5 Int)(x7 Int)(x1 Int)(x8 Int)(x2 Int)(x4 Int)(x6 Int)) (=> (and (|$P8| x2 x4 x6 x3 x7) (and (|$P9| x4 x7 x5) (and (|$P9| x6 x7 x8) (and (or (and (> x0 0) (= x5 x7)) (and (not (> x0 0)) (not (= x5 x7)))) (or (and (> x1 0) (= x8 x7)) (and (not (> x1 0)) (not (= x8 x7)))))))) (|$P6| x3))))
(assert (forall ((x7 Int)(x8 Int)(x0 Int)(x2 Int)(x1 Int)(x3 Int)(x5 Int)(x6 Int)(x4 Int)) (=> (and (|$P9| x5 x8 x2) (and (|$P9| x6 x8 x3) (and (|$P8| x4 x5 x6 x7 x8) (and (or (and (> x0 0) (= x2 x8)) (and (not (> x0 0)) (not (= x2 x8)))) (or (and (> x1 0) (= x3 x8)) (and (not (> x1 0)) (not (= x3 x8)))))))) (|$P7| x7 x8))))
(assert (not (exists ((x0 Int)(x1 Int)(x6 Int)(x10 Int)(x2 Int)(x8 Int)(x3 Int)(x11 Int)(x4 Int)(x5 Int)(x7 Int)(x9 Int)) (and (|$P8| x4 x5 x7 x9 x10) (and (|$P9| x5 x10 x6) (and (|$P9| x7 x10 x8) (and (|$P9| x9 x10 x11) (and (or (not (> x0 0)) (not (> x1 0))) (and (or (and (> x0 0) (= x6 x10)) (and (not (> x0 0)) (not (= x6 x10)))) (and (or (and (> x2 0) (= x8 x10)) (and (not (> x2 0)) (not (= x8 x10)))) (and (or (and (> x3 0) (= x11 x10)) (and (not (> x3 0)) (not (= x11 x10)))) (or (and (> x1 0) (and (> x2 0) (> x3 0))) (and (not (> x1 0)) (not (and (> x2 0) (> x3 0))))))))))))))))
(check-sat)
