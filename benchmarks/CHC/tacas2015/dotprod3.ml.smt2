(set-logic HORN)
(set-info :source |
  Benchmark: ./benchmarks/ocaml/safety/tacas2015//dotprod3.ml
  Generated by Refinement Caml
|)
(set-info :status unknown)
(declare-fun |$P0| (Int) Bool)
(declare-fun |$P5| (Int Int Int Int Int) Bool)
(declare-fun |$P7| (Int) Bool)
(declare-fun |$P11| (Int Int) Bool)
(declare-fun |$P1| (Int Int Int) Bool)
(declare-fun |$P2| (Int Int Int Int) Bool)
(declare-fun |$P3| (Int Int) Bool)
(declare-fun |$P4| (Int Int) Bool)
(declare-fun |$P15| (Int Int Int Int) Bool)
(declare-fun |$P16| (Int Int Int Int Int) Bool)
(declare-fun |$P10| (Int Int Int) Bool)
(declare-fun |$P14| (Int Int Int Int) Bool)
(declare-fun |$P8| (Int) Bool)
(declare-fun |$P6| (Int Int Int Int Int Int) Bool)
(declare-fun |$P9| (Int Int) Bool)
(declare-fun |$P12| (Int Int Int) Bool)
(declare-fun |$P13| (Int Int Int) Bool)
(assert (not (exists ((x0 Int)(x1 Int)(x3 Int)(x2 Int)) (and (|$P7| x2) (and (|$P11| x2 x3) (and (or (not (> x0 0)) (not (> x1 0))) (and (or (and (> x0 0) (<= 0 x3)) (and (not (> x0 0)) (not (<= 0 x3)))) (or (and (> x1 0) (< x3 x2)) (and (not (> x1 0)) (not (< x3 x2)))))))))))
(assert (forall ((x1 Int)(x2 Int)(x0 Int)) (=> (and (|$P7| x1) (and (|$P11| x1 x2) (and (and (<= 0 x2) (<= (+ 1 x2) x1)) (= x0 0)))) (|$P13| x1 x2 x0))))
(assert (forall ((x2 Int)(x3 Int)(x0 Int)(x1 Int)(x4 Int)) (=> (and (|$P3| x2 x3) (and (|$P1| x2 x3 x0) (and (|$P2| x2 x3 x0 x1) (and (|$P1| x2 x3 x4) (and (= x3 x1) (= x4 x0)))))) (|$P5| x2 x3 x0 x1 x4))))
(assert (forall ((x3 Int)(x1 Int)(x2 Int)(x0 Int)) (=> (and (|$P1| x2 x3 x0) (and (|$P2| x2 x3 x0 x1) (and (|$P3| x2 x3) (or (< x3 x1) (> x3 x1))))) (|$P0| x3))))
(assert (forall ((x2 Int)(x3 Int)(x0 Int)(x1 Int)(x4 Int)) (=> (and (|$P1| x2 x3 x0) (and (|$P2| x2 x3 x0 x1) (and (|$P3| x2 x3) (and (|$P4| x3 x4) (or (< x3 x1) (> x3 x1)))))) (|$P5| x2 x3 x0 x1 x4))))
(assert (forall ((x1 Int)(x2 Int)(x3 Int)(x4 Int)(x0 Int)(x5 Int)) (=> (and (|$P8| x1) (and (|$P15| x1 x2 x3 x4) (and (|$P16| x1 x2 x3 x4 x0) (and (|$P16| x1 x2 x3 x4 x5) (and (>= x4 x1) (= x5 x0)))))) (|$P6| x1 x2 x3 x4 x0 x5))))
(assert (forall ((x2 Int)(x5 Int)(x0 Int)(x3 Int)(x4 Int)(x1 Int)) (=> (and (|$P8| x2) (and (|$P16| x2 x3 x4 x5 x1) (and (|$P15| x2 x3 x4 x5) (and (<= (+ 1 x5) x2) (= x0 (+ 1 x5)))))) (|$P9| x2 x5))))
(assert (forall ((x3 Int)(x4 Int)(x6 Int)(x0 Int)(x5 Int)(x1 Int)(x2 Int)) (=> (and (|$P8| x3) (and (|$P16| x3 x4 x5 x6 x1) (and (|$P10| x3 x6 x2) (and (|$P15| x3 x4 x5 x6) (and (<= (+ 1 x6) x3) (= x0 (+ 1 x6))))))) (|$P12| x3 x4 x6))))
(assert (forall ((x9 Int)(x7 Int)(x0 Int)(x1 Int)(x4 Int)(x2 Int)(x5 Int)(x8 Int)(x6 Int)(x3 Int)) (=> (and (|$P15| x9 x6 x3 x7) (and (|$P16| x9 x6 x3 x7 x4) (and (|$P10| x9 x7 x5) (and (|$P14| x9 x6 x7 x8) (and (|$P8| x9) (and (<= (+ 1 x7) x9) (and (= x0 (+ 1 x7)) (and (= x1 (+ x4 x2)) (= x2 (* x5 x8)))))))))) (|$P8| x9))))
(assert (forall ((x9 Int)(x10 Int)(x7 Int)(x0 Int)(x1 Int)(x4 Int)(x2 Int)(x5 Int)(x8 Int)(x6 Int)(x3 Int)) (=> (and (|$P15| x9 x6 x3 x7) (and (|$P16| x9 x6 x3 x7 x4) (and (|$P10| x9 x7 x5) (and (|$P14| x9 x6 x7 x8) (and (|$P8| x9) (and (|$P9| x9 x10) (and (<= (+ 1 x7) x9) (and (= x0 (+ 1 x7)) (and (= x1 (+ x4 x2)) (= x2 (* x5 x8))))))))))) (|$P9| x9 x10))))
(assert (forall ((x9 Int)(x10 Int)(x11 Int)(x7 Int)(x0 Int)(x1 Int)(x4 Int)(x2 Int)(x5 Int)(x8 Int)(x6 Int)(x3 Int)) (=> (and (|$P15| x9 x6 x3 x7) (and (|$P16| x9 x6 x3 x7 x4) (and (|$P10| x9 x7 x5) (and (|$P14| x9 x6 x7 x8) (and (|$P8| x9) (and (|$P9| x9 x10) (and (|$P10| x9 x10 x11) (and (<= (+ 1 x7) x9) (and (= x0 (+ 1 x7)) (and (= x1 (+ x4 x2)) (= x2 (* x5 x8)))))))))))) (|$P10| x9 x10 x11))))
(assert (forall ((x9 Int)(x6 Int)(x11 Int)(x7 Int)(x0 Int)(x1 Int)(x4 Int)(x2 Int)(x5 Int)(x8 Int)(x3 Int)(x10 Int)) (=> (and (|$P15| x9 x6 x3 x7) (and (|$P16| x9 x6 x3 x7 x4) (and (|$P10| x9 x7 x5) (and (|$P14| x9 x6 x7 x8) (and (|$P8| x9) (and (|$P12| x9 x10 x11) (and (<= (+ 1 x7) x9) (and (= x0 (+ 1 x7)) (and (= x1 (+ x4 x2)) (= x2 (* x5 x8))))))))))) (|$P12| x9 x6 x11))))
(assert (forall ((x9 Int)(x8 Int)(x11 Int)(x12 Int)(x6 Int)(x0 Int)(x1 Int)(x4 Int)(x2 Int)(x5 Int)(x7 Int)(x10 Int)(x3 Int)) (=> (and (|$P15| x9 x10 x3 x6) (and (|$P16| x9 x10 x3 x6 x4) (and (|$P10| x9 x6 x5) (and (|$P14| x9 x10 x6 x7) (and (|$P8| x9) (and (|$P12| x9 x8 x11) (and (|$P14| x9 x10 x11 x12) (and (<= (+ 1 x6) x9) (and (= x0 (+ 1 x6)) (and (= x1 (+ x4 x2)) (= x2 (* x5 x7)))))))))))) (|$P14| x9 x8 x11 x12))))
(assert (forall ((x11 Int)(x0 Int)(x1 Int)(x3 Int)(x9 Int)(x2 Int)(x6 Int)(x4 Int)(x7 Int)(x10 Int)(x8 Int)(x5 Int)) (=> (and (|$P15| x11 x8 x5 x9) (and (|$P16| x11 x8 x5 x9 x6) (and (|$P10| x11 x9 x7) (and (|$P14| x11 x8 x9 x10) (and (|$P8| x11) (and (<= (+ 1 x9) x11) (and (= x2 (+ x6 x4)) (and (= x3 (+ 1 x9)) (= x4 (* x7 x10)))))))))) (|$P15| x11 x0 x1 x3))))
(assert (forall ((x11 Int)(x0 Int)(x1 Int)(x2 Int)(x3 Int)(x9 Int)(x6 Int)(x4 Int)(x7 Int)(x10 Int)(x8 Int)(x5 Int)) (=> (and (|$P15| x11 x8 x5 x9) (and (|$P16| x11 x8 x5 x9 x6) (and (|$P10| x11 x9 x7) (and (|$P14| x11 x8 x9 x10) (and (|$P8| x11) (and (<= (+ 1 x9) x11) (and (= x2 (+ 1 x9)) (and (= x3 (+ x6 x4)) (= x4 (* x7 x10)))))))))) (|$P16| x11 x0 x1 x2 x3))))
(assert (forall ((x7 Int)(x4 Int)(x1 Int)(x5 Int)(x2 Int)(x12 Int)(x10 Int)(x11 Int)(x0 Int)(x3 Int)(x6 Int)(x8 Int)(x9 Int)) (=> (and (|$P15| x7 x4 x1 x5) (and (|$P16| x7 x4 x1 x5 x2) (and (|$P10| x7 x5 x3) (and (|$P14| x7 x4 x5 x6) (and (|$P8| x7) (and (|$P6| x7 x8 x9 x10 x11 x12) (and (<= (+ 1 x5) x7) (and (= x10 (+ 1 x5)) (and (= x11 (+ x2 x0)) (= x0 (* x3 x6))))))))))) (|$P6| x7 x4 x1 x5 x2 x12))))
(assert (forall ((x0 Int)) (|$P7| x0)))
(assert (forall ((x0 Int)) (|$P7| x0)))
(assert (forall ((x0 Int)) (|$P8| x0)))
(assert (forall ((x0 Int)(x1 Int)) (=> (|$P9| x0 x1) (|$P11| x0 x1))))
(assert (forall ((x0 Int)(x1 Int)(x2 Int)) (=> (and (|$P9| x0 x1) (|$P13| x0 x1 x2)) (|$P10| x0 x1 x2))))
(assert (forall ((x0 Int)(x2 Int)(x1 Int)) (=> (|$P12| x0 x1 x2) (|$P11| x0 x2))))
(assert (forall ((x1 Int)(x0 Int)(x2 Int)(x3 Int)) (=> (and (|$P12| x1 x0 x2) (|$P13| x1 x2 x3)) (|$P14| x1 x0 x2 x3))))
(assert (forall ((x0 Int)(x1 Int)(x2 Int)(x3 Int)) (=> (= x3 0) (|$P15| x0 x1 x2 x3))))
(assert (forall ((x0 Int)(x1 Int)(x2 Int)(x3 Int)(x4 Int)) (=> (and (= x3 0) (= x4 0)) (|$P16| x0 x1 x2 x3 x4))))
(check-sat)
