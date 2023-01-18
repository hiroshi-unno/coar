(set-logic HORN)
(set-info :source |
  Benchmark: ./benchmarks/ocaml/safety/tacas2015//a-dotprod.ml
  Generated by Refinement Caml
|)
(set-info :status unknown)
(declare-fun |$P1| (Int) Bool)
(declare-fun |$P5| (Int Int) Bool)
(declare-fun |$P9| (Int Int Int Int) Bool)
(declare-fun |$P10| (Int Int Int Int Int) Bool)
(declare-fun |$P4| (Int Int Int) Bool)
(declare-fun |$P8| (Int Int Int Int) Bool)
(declare-fun |$P2| (Int) Bool)
(declare-fun |$P0| (Int Int Int Int Int Int) Bool)
(declare-fun |$P3| (Int Int) Bool)
(declare-fun |$P6| (Int Int Int) Bool)
(declare-fun |$P7| (Int Int Int) Bool)
(assert (not (exists ((x0 Int)(x1 Int)(x3 Int)(x2 Int)) (and (|$P1| x2) (and (|$P5| x2 x3) (and (or (not (> x0 0)) (not (> x1 0))) (and (or (and (> x0 0) (<= 0 x3)) (and (not (> x0 0)) (not (<= 0 x3)))) (or (and (> x1 0) (< x3 x2)) (and (not (> x1 0)) (not (< x3 x2)))))))))))
(assert (forall ((x1 Int)(x2 Int)(x0 Int)) (=> (and (|$P1| x1) (and (|$P5| x1 x2) (and (and (<= 0 x2) (<= (+ 1 x2) x1)) (= x0 0)))) (|$P7| x1 x2 x0))))
(assert (forall ((x1 Int)(x2 Int)(x3 Int)(x4 Int)(x0 Int)(x5 Int)) (=> (and (|$P2| x1) (and (|$P9| x1 x2 x3 x4) (and (|$P10| x1 x2 x3 x4 x0) (and (|$P10| x1 x2 x3 x4 x5) (and (>= x4 x1) (= x5 x0)))))) (|$P0| x1 x2 x3 x4 x0 x5))))
(assert (forall ((x2 Int)(x5 Int)(x0 Int)(x3 Int)(x4 Int)(x1 Int)) (=> (and (|$P2| x2) (and (|$P10| x2 x3 x4 x5 x1) (and (|$P9| x2 x3 x4 x5) (and (<= (+ 1 x5) x2) (= x0 (+ 1 x5)))))) (|$P3| x2 x5))))
(assert (forall ((x3 Int)(x4 Int)(x6 Int)(x0 Int)(x5 Int)(x1 Int)(x2 Int)) (=> (and (|$P2| x3) (and (|$P10| x3 x4 x5 x6 x1) (and (|$P4| x3 x6 x2) (and (|$P9| x3 x4 x5 x6) (and (<= (+ 1 x6) x3) (= x0 (+ 1 x6))))))) (|$P6| x3 x4 x6))))
(assert (forall ((x9 Int)(x7 Int)(x0 Int)(x1 Int)(x4 Int)(x2 Int)(x5 Int)(x8 Int)(x6 Int)(x3 Int)) (=> (and (|$P9| x9 x6 x3 x7) (and (|$P10| x9 x6 x3 x7 x4) (and (|$P4| x9 x7 x5) (and (|$P8| x9 x6 x7 x8) (and (|$P2| x9) (and (<= (+ 1 x7) x9) (and (= x0 (+ 1 x7)) (and (= x1 (+ x4 x2)) (= x2 (* x5 x8)))))))))) (|$P2| x9))))
(assert (forall ((x9 Int)(x10 Int)(x7 Int)(x0 Int)(x1 Int)(x4 Int)(x2 Int)(x5 Int)(x8 Int)(x6 Int)(x3 Int)) (=> (and (|$P9| x9 x6 x3 x7) (and (|$P10| x9 x6 x3 x7 x4) (and (|$P4| x9 x7 x5) (and (|$P8| x9 x6 x7 x8) (and (|$P2| x9) (and (|$P3| x9 x10) (and (<= (+ 1 x7) x9) (and (= x0 (+ 1 x7)) (and (= x1 (+ x4 x2)) (= x2 (* x5 x8))))))))))) (|$P3| x9 x10))))
(assert (forall ((x9 Int)(x10 Int)(x11 Int)(x7 Int)(x0 Int)(x1 Int)(x4 Int)(x2 Int)(x5 Int)(x8 Int)(x6 Int)(x3 Int)) (=> (and (|$P9| x9 x6 x3 x7) (and (|$P10| x9 x6 x3 x7 x4) (and (|$P4| x9 x7 x5) (and (|$P8| x9 x6 x7 x8) (and (|$P2| x9) (and (|$P3| x9 x10) (and (|$P4| x9 x10 x11) (and (<= (+ 1 x7) x9) (and (= x0 (+ 1 x7)) (and (= x1 (+ x4 x2)) (= x2 (* x5 x8)))))))))))) (|$P4| x9 x10 x11))))
(assert (forall ((x9 Int)(x6 Int)(x11 Int)(x7 Int)(x0 Int)(x1 Int)(x4 Int)(x2 Int)(x5 Int)(x8 Int)(x3 Int)(x10 Int)) (=> (and (|$P9| x9 x6 x3 x7) (and (|$P10| x9 x6 x3 x7 x4) (and (|$P4| x9 x7 x5) (and (|$P8| x9 x6 x7 x8) (and (|$P2| x9) (and (|$P6| x9 x10 x11) (and (<= (+ 1 x7) x9) (and (= x0 (+ 1 x7)) (and (= x1 (+ x4 x2)) (= x2 (* x5 x8))))))))))) (|$P6| x9 x6 x11))))
(assert (forall ((x9 Int)(x8 Int)(x11 Int)(x12 Int)(x6 Int)(x0 Int)(x1 Int)(x4 Int)(x2 Int)(x5 Int)(x7 Int)(x10 Int)(x3 Int)) (=> (and (|$P9| x9 x10 x3 x6) (and (|$P10| x9 x10 x3 x6 x4) (and (|$P4| x9 x6 x5) (and (|$P8| x9 x10 x6 x7) (and (|$P2| x9) (and (|$P6| x9 x8 x11) (and (|$P8| x9 x10 x11 x12) (and (<= (+ 1 x6) x9) (and (= x0 (+ 1 x6)) (and (= x1 (+ x4 x2)) (= x2 (* x5 x7)))))))))))) (|$P8| x9 x8 x11 x12))))
(assert (forall ((x11 Int)(x0 Int)(x1 Int)(x3 Int)(x9 Int)(x2 Int)(x6 Int)(x4 Int)(x7 Int)(x10 Int)(x8 Int)(x5 Int)) (=> (and (|$P9| x11 x8 x5 x9) (and (|$P10| x11 x8 x5 x9 x6) (and (|$P4| x11 x9 x7) (and (|$P8| x11 x8 x9 x10) (and (|$P2| x11) (and (<= (+ 1 x9) x11) (and (= x2 (+ x6 x4)) (and (= x3 (+ 1 x9)) (= x4 (* x7 x10)))))))))) (|$P9| x11 x0 x1 x3))))
(assert (forall ((x11 Int)(x0 Int)(x1 Int)(x2 Int)(x3 Int)(x9 Int)(x6 Int)(x4 Int)(x7 Int)(x10 Int)(x8 Int)(x5 Int)) (=> (and (|$P9| x11 x8 x5 x9) (and (|$P10| x11 x8 x5 x9 x6) (and (|$P4| x11 x9 x7) (and (|$P8| x11 x8 x9 x10) (and (|$P2| x11) (and (<= (+ 1 x9) x11) (and (= x2 (+ 1 x9)) (and (= x3 (+ x6 x4)) (= x4 (* x7 x10)))))))))) (|$P10| x11 x0 x1 x2 x3))))
(assert (forall ((x7 Int)(x4 Int)(x1 Int)(x5 Int)(x2 Int)(x12 Int)(x10 Int)(x11 Int)(x0 Int)(x3 Int)(x6 Int)(x8 Int)(x9 Int)) (=> (and (|$P9| x7 x4 x1 x5) (and (|$P10| x7 x4 x1 x5 x2) (and (|$P4| x7 x5 x3) (and (|$P8| x7 x4 x5 x6) (and (|$P2| x7) (and (|$P0| x7 x8 x9 x10 x11 x12) (and (<= (+ 1 x5) x7) (and (= x10 (+ 1 x5)) (and (= x11 (+ x2 x0)) (= x0 (* x3 x6))))))))))) (|$P0| x7 x4 x1 x5 x2 x12))))
(assert (forall ((x0 Int)) (|$P1| x0)))
(assert (forall ((x0 Int)) (|$P1| x0)))
(assert (forall ((x0 Int)) (|$P2| x0)))
(assert (forall ((x0 Int)(x1 Int)) (=> (|$P3| x0 x1) (|$P5| x0 x1))))
(assert (forall ((x0 Int)(x1 Int)(x2 Int)) (=> (and (|$P3| x0 x1) (|$P7| x0 x1 x2)) (|$P4| x0 x1 x2))))
(assert (forall ((x0 Int)(x2 Int)(x1 Int)) (=> (|$P6| x0 x1 x2) (|$P5| x0 x2))))
(assert (forall ((x1 Int)(x0 Int)(x2 Int)(x3 Int)) (=> (and (|$P6| x1 x0 x2) (|$P7| x1 x2 x3)) (|$P8| x1 x0 x2 x3))))
(assert (forall ((x0 Int)(x1 Int)(x2 Int)(x3 Int)) (=> (= x3 0) (|$P9| x0 x1 x2 x3))))
(assert (forall ((x0 Int)(x1 Int)(x2 Int)(x4 Int)(x3 Int)) (=> (and (= x4 0) (= x3 x4)) (|$P10| x0 x1 x2 x4 x3))))
(check-sat)
