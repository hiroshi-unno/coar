(set-logic HORN)
(set-info :source |
  Benchmark: ./benchmarks/ocaml/safety/tacas2015//inc.ml
  Generated by Refinement Caml
|)
(set-info :status unknown)
(declare-fun |$P8| (Int) Bool)
(declare-fun |$P2| (Int Int) Bool)
(declare-fun |$P3| (Int Int Int) Bool)
(declare-fun |$P4| (Int Int Int Int) Bool)
(declare-fun |$P1| (Int Int) Bool)
(declare-fun |$P0| (Int) Bool)
(declare-fun |$P5| (Int Int Int Int Int) Bool)
(declare-fun |$P11| (Int Int Int) Bool)
(declare-fun |$P6| (Int Int Int Int) Bool)
(declare-fun |$P7| (Int) Bool)
(declare-fun |$P12| (Int Int Int) Bool)
(declare-fun |$P9| (Int Int) Bool)
(declare-fun |$P10| (Int Int) Bool)
(assert (forall ((x1 Int)(x0 Int)) (=> (and (|$P8| x1) (= x0 0)) (|$P10| x1 x0))))
(assert (forall ((x2 Int)(x3 Int)(x0 Int)(x1 Int)(x4 Int)) (=> (and (|$P2| x2 x3) (and (|$P3| x2 x3 x0) (and (|$P4| x2 x3 x0 x1) (and (|$P3| x2 x3 x4) (and (= x1 x3) (= x4 x0)))))) (|$P5| x2 x3 x0 x1 x4))))
(assert (forall ((x3 Int)(x1 Int)(x0 Int)(x2 Int)) (=> (and (|$P2| x0 x1) (and (|$P3| x0 x1 x2) (and (|$P4| x0 x1 x2 x3) (or (< x3 x1) (> x3 x1))))) (|$P0| x3))))
(assert (forall ((x0 Int)(x1 Int)(x2 Int)(x3 Int)(x4 Int)) (=> (and (|$P2| x0 x1) (and (|$P3| x0 x1 x2) (and (|$P4| x0 x1 x2 x3) (and (|$P1| x3 x4) (or (< x3 x1) (> x3 x1)))))) (|$P5| x0 x1 x2 x3 x4))))
(assert (not (exists ((x4 Int)(x2 Int)(x0 Int)(x1 Int)(x3 Int)) (and (|$P7| x2) (and (|$P12| x2 x3 x4) (and (and (<= (+ 1 x4) x2) (or (not (> x0 0)) (not (> x1 0)))) (and (or (and (> x0 0) (<= 0 x4)) (and (not (> x0 0)) (not (<= 0 x4)))) (or (and (> x1 0) (< x4 x2)) (and (not (> x1 0)) (not (< x4 x2)))))))))))
(assert (forall ((x0 Int)(x2 Int)(x1 Int)) (=> (and (|$P7| x0) (and (|$P12| x0 x1 x2) (and (<= 0 x2) (<= (+ 1 x2) x0)))) (|$P9| x0 x2))))
(assert (forall ((x2 Int)(x5 Int)(x3 Int)(x0 Int)(x4 Int)(x1 Int)) (=> (and (|$P7| x2) (and (|$P12| x2 x1 x3) (and (|$P11| x2 x3 x4) (and (|$P0| x5) (and (and (<= 0 x3) (<= (+ 1 x3) x2)) (= x0 (+ 1 x4))))))) (|$P9| x2 x5))))
(assert (forall ((x5 Int)(x6 Int)(x2 Int)(x4 Int)(x0 Int)(x3 Int)(x1 Int)) (=> (and (|$P7| x4) (and (|$P12| x4 x1 x2) (and (|$P11| x4 x2 x3) (and (|$P0| x5) (and (|$P11| x4 x5 x6) (and (and (<= 0 x2) (<= (+ 1 x2) x4)) (= x0 (+ 1 x3)))))))) (|$P1| x5 x6))))
(assert (forall ((x3 Int)(x4 Int)(x2 Int)(x0 Int)(x1 Int)) (=> (and (|$P7| x2) (and (|$P11| x2 x4 x1) (and (|$P12| x2 x3 x4) (and (and (<= 0 x4) (<= (+ 1 x4) x2)) (= x0 (+ 1 x1)))))) (|$P2| x3 x4))))
(assert (forall ((x1 Int)(x3 Int)(x0 Int)(x2 Int)(x4 Int)) (=> (and (|$P7| x2) (and (|$P12| x2 x1 x3) (and (|$P11| x2 x3 x4) (and (and (<= 0 x3) (<= (+ 1 x3) x2)) (= x0 (+ 1 x4)))))) (|$P3| x1 x3 x0))))
(assert (forall ((x5 Int)(x3 Int)(x0 Int)(x4 Int)(x1 Int)(x2 Int)) (=> (and (|$P12| x5 x2 x3) (and (|$P11| x5 x3 x4) (and (|$P7| x5) (and (and (<= 0 x3) (<= (+ 1 x3) x5)) (and (= x0 (+ 1 x4)) (= x1 (+ 1 x3))))))) (|$P7| x5))))
(assert (forall ((x2 Int)(x3 Int)(x0 Int)(x6 Int)(x5 Int)(x4 Int)(x1 Int)) (=> (and (|$P12| x5 x2 x3) (and (|$P11| x5 x3 x4) (and (|$P7| x5) (and (|$P9| x5 x6) (and (and (<= 0 x3) (<= (+ 1 x3) x5)) (and (= x0 (+ 1 x4)) (= x1 (+ 1 x3)))))))) (|$P4| x2 x3 x0 x6))))
(assert (forall ((x2 Int)(x6 Int)(x7 Int)(x4 Int)(x5 Int)(x1 Int)(x0 Int)(x3 Int)) (=> (and (|$P12| x2 x3 x4) (and (|$P11| x2 x4 x1) (and (|$P7| x2) (and (|$P9| x2 x6) (and (|$P5| x3 x4 x5 x6 x7) (and (and (<= 0 x4) (<= (+ 1 x4) x2)) (and (= x5 (+ 1 x1)) (= x0 (+ 1 x4))))))))) (|$P11| x2 x6 x7))))
(assert (forall ((x6 Int)(x0 Int)(x2 Int)(x4 Int)(x1 Int)(x5 Int)(x3 Int)) (=> (and (|$P12| x6 x3 x4) (and (|$P11| x6 x4 x5) (and (|$P7| x6) (and (and (<= 0 x4) (<= (+ 1 x4) x6)) (and (= x1 (+ 1 x5)) (= x2 (+ 1 x4))))))) (|$P12| x6 x0 x2))))
(assert (forall ((x4 Int)(x1 Int)(x2 Int)(x7 Int)(x0 Int)(x3 Int)(x6 Int)(x5 Int)) (=> (and (|$P12| x4 x1 x2) (and (|$P11| x4 x2 x3) (and (|$P7| x4) (and (|$P6| x4 x5 x6 x7) (and (and (<= 0 x2) (<= (+ 1 x2) x4)) (and (= x0 (+ 1 x3)) (= x6 (+ 1 x2)))))))) (|$P6| x4 x1 x2 x7))))
(assert (forall ((x1 Int)(x2 Int)(x3 Int)(x0 Int)) (=> (and (|$P7| x1) (and (|$P12| x1 x2 x3) (>= x3 x1))) (|$P6| x1 x2 x3 x0))))
(assert (forall ((x0 Int)) (|$P7| x0)))
(assert (forall ((x1 Int)(x0 Int)) (=> (|$P9| x0 x1) (|$P8| x1))))
(assert (forall ((x0 Int)(x1 Int)(x2 Int)) (=> (and (|$P9| x0 x1) (|$P10| x1 x2)) (|$P11| x0 x1 x2))))
(assert (forall ((x0 Int)(x1 Int)(x2 Int)) (=> (= x2 0) (|$P12| x0 x1 x2))))
(check-sat)
