(set-logic HORN)
(set-info :source |
  Benchmark: ./benchmarks/ocaml/safety/tacas2015//dotprod_.ml
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
(assert (forall ((x4 Int)(x5 Int)(x7 Int)(x0 Int)(x1 Int)(x2 Int)(x3 Int)(x6 Int)) (=> (and (|$P2| x4) (and (|$P10| x4 x5 x6 x7 x2) (and (|$P4| x4 x7 x3) (and (|$P9| x4 x5 x6 x7) (and (<= (+ 1 x7) x4) (and (= x0 (+ 1 x7)) (= x1 (+ x2 x3)))))))) (|$P6| x4 x5 x7))))
(assert (forall ((x9 Int)(x7 Int)(x0 Int)(x2 Int)(x4 Int)(x5 Int)(x1 Int)(x8 Int)(x6 Int)(x3 Int)) (=> (and (|$P9| x9 x6 x3 x7) (and (|$P10| x9 x6 x3 x7 x4) (and (|$P4| x9 x7 x5) (and (|$P8| x9 x6 x7 x8) (and (|$P2| x9) (and (<= (+ 1 x7) x9) (and (= x0 (+ 1 x7)) (and (= x2 (+ x4 x5)) (= x1 (+ x2 x8)))))))))) (|$P2| x9))))
(assert (forall ((x9 Int)(x10 Int)(x7 Int)(x0 Int)(x2 Int)(x4 Int)(x5 Int)(x1 Int)(x8 Int)(x6 Int)(x3 Int)) (=> (and (|$P2| x9) (and (|$P9| x9 x6 x3 x7) (and (|$P10| x9 x6 x3 x7 x4) (and (|$P4| x9 x7 x5) (and (|$P8| x9 x6 x7 x8) (and (|$P3| x9 x10) (and (<= (+ 1 x7) x9) (and (= x0 (+ 1 x7)) (and (= x2 (+ x4 x5)) (= x1 (+ x2 x8))))))))))) (|$P3| x9 x10))))
(assert (forall ((x9 Int)(x10 Int)(x11 Int)(x7 Int)(x0 Int)(x2 Int)(x4 Int)(x5 Int)(x1 Int)(x8 Int)(x6 Int)(x3 Int)) (=> (and (|$P2| x9) (and (|$P9| x9 x6 x3 x7) (and (|$P10| x9 x6 x3 x7 x4) (and (|$P4| x9 x7 x5) (and (|$P8| x9 x6 x7 x8) (and (|$P3| x9 x10) (and (|$P4| x9 x10 x11) (and (<= (+ 1 x7) x9) (and (= x0 (+ 1 x7)) (and (= x2 (+ x4 x5)) (= x1 (+ x2 x8)))))))))))) (|$P4| x9 x10 x11))))
(assert (forall ((x8 Int)(x9 Int)(x10 Int)(x6 Int)(x0 Int)(x2 Int)(x4 Int)(x5 Int)(x1 Int)(x7 Int)(x3 Int)) (=> (and (|$P2| x8) (and (|$P9| x8 x9 x3 x6) (and (|$P10| x8 x9 x3 x6 x4) (and (|$P4| x8 x6 x5) (and (|$P8| x8 x9 x6 x7) (and (|$P6| x8 x9 x10) (and (<= (+ 1 x6) x8) (and (= x0 (+ 1 x6)) (and (= x2 (+ x4 x5)) (= x1 (+ x2 x7))))))))))) (|$P6| x8 x9 x10))))
(assert (forall ((x8 Int)(x9 Int)(x10 Int)(x11 Int)(x6 Int)(x0 Int)(x2 Int)(x4 Int)(x5 Int)(x1 Int)(x7 Int)(x3 Int)) (=> (and (|$P2| x8) (and (|$P9| x8 x9 x3 x6) (and (|$P10| x8 x9 x3 x6 x4) (and (|$P4| x8 x6 x5) (and (|$P8| x8 x9 x6 x7) (and (|$P6| x8 x9 x10) (and (|$P8| x8 x9 x10 x11) (and (<= (+ 1 x6) x8) (and (= x0 (+ 1 x6)) (and (= x2 (+ x4 x5)) (= x1 (+ x2 x7)))))))))))) (|$P8| x8 x9 x10 x11))))
(assert (forall ((x6 Int)(x7 Int)(x3 Int)(x2 Int)(x8 Int)(x1 Int)(x4 Int)(x5 Int)(x0 Int)(x9 Int)) (=> (and (|$P2| x6) (and (|$P9| x6 x7 x3 x8) (and (|$P10| x6 x7 x3 x8 x4) (and (|$P4| x6 x8 x5) (and (|$P8| x6 x7 x8 x9) (and (<= (+ 1 x8) x6) (and (= x1 (+ x4 x5)) (and (= x0 (+ x1 x9)) (= x2 (+ 1 x8)))))))))) (|$P9| x6 x7 x3 x2))))
(assert (forall ((x6 Int)(x7 Int)(x3 Int)(x0 Int)(x1 Int)(x8 Int)(x2 Int)(x4 Int)(x5 Int)(x9 Int)) (=> (and (|$P2| x6) (and (|$P9| x6 x7 x3 x8) (and (|$P10| x6 x7 x3 x8 x4) (and (|$P4| x6 x8 x5) (and (|$P8| x6 x7 x8 x9) (and (<= (+ 1 x8) x6) (and (= x0 (+ 1 x8)) (and (= x2 (+ x4 x5)) (= x1 (+ x2 x9)))))))))) (|$P10| x6 x7 x3 x0 x1))))
(assert (forall ((x8 Int)(x11 Int)(x5 Int)(x0 Int)(x2 Int)(x3 Int)(x6 Int)(x4 Int)(x1 Int)(x9 Int)(x10 Int)(x7 Int)) (=> (and (|$P2| x8) (and (|$P10| x8 x9 x10 x11 x2) (and (|$P4| x8 x11 x3) (and (|$P8| x8 x9 x11 x4) (and (|$P0| x8 x9 x10 x5 x6 x7) (and (|$P9| x8 x9 x10 x11) (and (<= (+ 1 x11) x8) (and (= x5 (+ 1 x11)) (and (= x0 (+ x2 x3)) (and (= x6 (+ x0 x4)) (= x1 (+ 1 x11)))))))))))) (|$P3| x8 x11))))
(assert (forall ((x10 Int)(x11 Int)(x13 Int)(x6 Int)(x0 Int)(x3 Int)(x4 Int)(x7 Int)(x5 Int)(x1 Int)(x2 Int)(x9 Int)(x12 Int)(x8 Int)) (=> (and (|$P2| x10) (and (|$P10| x10 x11 x12 x13 x3) (and (|$P4| x10 x13 x4) (and (|$P8| x10 x11 x13 x5) (and (|$P0| x10 x11 x12 x6 x7 x8) (and (|$P4| x10 x13 x9) (and (|$P9| x10 x11 x12 x13) (and (<= (+ 1 x13) x10) (and (= x6 (+ 1 x13)) (and (= x0 (+ x3 x4)) (and (= x7 (+ x0 x5)) (and (= x1 (+ 1 x13)) (= x2 (+ x3 x9)))))))))))))) (|$P6| x10 x11 x13))))
(assert (forall ((x15 Int)(x13 Int)(x8 Int)(x0 Int)(x4 Int)(x5 Int)(x9 Int)(x6 Int)(x1 Int)(x3 Int)(x11 Int)(x2 Int)(x14 Int)(x12 Int)(x7 Int)(x10 Int)) (=> (and (|$P9| x15 x12 x7 x13) (and (|$P10| x15 x12 x7 x13 x4) (and (|$P4| x15 x13 x5) (and (|$P8| x15 x12 x13 x6) (and (|$P0| x15 x12 x7 x8 x9 x10) (and (|$P4| x15 x13 x11) (and (|$P8| x15 x12 x13 x14) (and (|$P2| x15) (and (<= (+ 1 x13) x15) (and (= x8 (+ 1 x13)) (and (= x0 (+ x4 x5)) (and (= x9 (+ x0 x6)) (and (= x1 (+ 1 x13)) (and (= x3 (+ x4 x11)) (= x2 (+ x3 x14)))))))))))))))) (|$P2| x15))))
(assert (forall ((x15 Int)(x16 Int)(x13 Int)(x8 Int)(x0 Int)(x4 Int)(x5 Int)(x9 Int)(x6 Int)(x1 Int)(x3 Int)(x11 Int)(x2 Int)(x14 Int)(x12 Int)(x7 Int)(x10 Int)) (=> (and (|$P9| x15 x12 x7 x13) (and (|$P10| x15 x12 x7 x13 x4) (and (|$P4| x15 x13 x5) (and (|$P8| x15 x12 x13 x6) (and (|$P0| x15 x12 x7 x8 x9 x10) (and (|$P4| x15 x13 x11) (and (|$P8| x15 x12 x13 x14) (and (|$P2| x15) (and (|$P3| x15 x16) (and (<= (+ 1 x13) x15) (and (= x8 (+ 1 x13)) (and (= x0 (+ x4 x5)) (and (= x9 (+ x0 x6)) (and (= x1 (+ 1 x13)) (and (= x3 (+ x4 x11)) (= x2 (+ x3 x14))))))))))))))))) (|$P3| x15 x16))))
(assert (forall ((x15 Int)(x16 Int)(x17 Int)(x13 Int)(x8 Int)(x0 Int)(x4 Int)(x5 Int)(x9 Int)(x6 Int)(x1 Int)(x3 Int)(x11 Int)(x2 Int)(x14 Int)(x12 Int)(x7 Int)(x10 Int)) (=> (and (|$P9| x15 x12 x7 x13) (and (|$P10| x15 x12 x7 x13 x4) (and (|$P4| x15 x13 x5) (and (|$P8| x15 x12 x13 x6) (and (|$P0| x15 x12 x7 x8 x9 x10) (and (|$P4| x15 x13 x11) (and (|$P8| x15 x12 x13 x14) (and (|$P2| x15) (and (|$P3| x15 x16) (and (|$P4| x15 x16 x17) (and (<= (+ 1 x13) x15) (and (= x8 (+ 1 x13)) (and (= x0 (+ x4 x5)) (and (= x9 (+ x0 x6)) (and (= x1 (+ 1 x13)) (and (= x3 (+ x4 x11)) (= x2 (+ x3 x14)))))))))))))))))) (|$P4| x15 x16 x17))))
(assert (forall ((x15 Int)(x12 Int)(x17 Int)(x13 Int)(x8 Int)(x0 Int)(x4 Int)(x5 Int)(x9 Int)(x6 Int)(x1 Int)(x3 Int)(x11 Int)(x2 Int)(x14 Int)(x7 Int)(x10 Int)(x16 Int)) (=> (and (|$P9| x15 x12 x7 x13) (and (|$P10| x15 x12 x7 x13 x4) (and (|$P4| x15 x13 x5) (and (|$P8| x15 x12 x13 x6) (and (|$P0| x15 x12 x7 x8 x9 x10) (and (|$P4| x15 x13 x11) (and (|$P8| x15 x12 x13 x14) (and (|$P2| x15) (and (|$P6| x15 x16 x17) (and (<= (+ 1 x13) x15) (and (= x8 (+ 1 x13)) (and (= x0 (+ x4 x5)) (and (= x9 (+ x0 x6)) (and (= x1 (+ 1 x13)) (and (= x3 (+ x4 x11)) (= x2 (+ x3 x14))))))))))))))))) (|$P6| x15 x12 x17))))
(assert (forall ((x15 Int)(x14 Int)(x17 Int)(x18 Int)(x12 Int)(x8 Int)(x0 Int)(x4 Int)(x5 Int)(x9 Int)(x6 Int)(x1 Int)(x3 Int)(x11 Int)(x2 Int)(x13 Int)(x16 Int)(x7 Int)(x10 Int)) (=> (and (|$P9| x15 x16 x7 x12) (and (|$P10| x15 x16 x7 x12 x4) (and (|$P4| x15 x12 x5) (and (|$P8| x15 x16 x12 x6) (and (|$P0| x15 x16 x7 x8 x9 x10) (and (|$P4| x15 x12 x11) (and (|$P8| x15 x16 x12 x13) (and (|$P2| x15) (and (|$P6| x15 x14 x17) (and (|$P8| x15 x16 x17 x18) (and (<= (+ 1 x12) x15) (and (= x8 (+ 1 x12)) (and (= x0 (+ x4 x5)) (and (= x9 (+ x0 x6)) (and (= x1 (+ 1 x12)) (and (= x3 (+ x4 x11)) (= x2 (+ x3 x13)))))))))))))))))) (|$P8| x15 x14 x17 x18))))
(assert (forall ((x17 Int)(x0 Int)(x1 Int)(x5 Int)(x15 Int)(x10 Int)(x2 Int)(x6 Int)(x7 Int)(x11 Int)(x8 Int)(x4 Int)(x13 Int)(x3 Int)(x16 Int)(x14 Int)(x9 Int)(x12 Int)) (=> (and (|$P9| x17 x14 x9 x15) (and (|$P10| x17 x14 x9 x15 x6) (and (|$P4| x17 x15 x7) (and (|$P8| x17 x14 x15 x8) (and (|$P0| x17 x14 x9 x10 x11 x12) (and (|$P4| x17 x15 x13) (and (|$P8| x17 x14 x15 x16) (and (|$P2| x17) (and (<= (+ 1 x15) x17) (and (= x10 (+ 1 x15)) (and (= x2 (+ x6 x7)) (and (= x11 (+ x2 x8)) (and (= x4 (+ x6 x13)) (and (= x3 (+ x4 x16)) (= x5 (+ 1 x15)))))))))))))))) (|$P9| x17 x0 x1 x5))))
(assert (forall ((x17 Int)(x0 Int)(x1 Int)(x3 Int)(x4 Int)(x15 Int)(x10 Int)(x2 Int)(x6 Int)(x7 Int)(x11 Int)(x8 Int)(x5 Int)(x13 Int)(x16 Int)(x14 Int)(x9 Int)(x12 Int)) (=> (and (|$P9| x17 x14 x9 x15) (and (|$P10| x17 x14 x9 x15 x6) (and (|$P4| x17 x15 x7) (and (|$P8| x17 x14 x15 x8) (and (|$P0| x17 x14 x9 x10 x11 x12) (and (|$P4| x17 x15 x13) (and (|$P8| x17 x14 x15 x16) (and (|$P2| x17) (and (<= (+ 1 x15) x17) (and (= x10 (+ 1 x15)) (and (= x2 (+ x6 x7)) (and (= x11 (+ x2 x8)) (and (= x5 (+ x6 x13)) (and (= x3 (+ 1 x15)) (= x4 (+ x5 x16)))))))))))))))) (|$P10| x17 x0 x1 x3 x4))))
(assert (forall ((x13 Int)(x10 Int)(x5 Int)(x11 Int)(x2 Int)(x18 Int)(x6 Int)(x0 Int)(x3 Int)(x7 Int)(x4 Int)(x1 Int)(x9 Int)(x16 Int)(x17 Int)(x12 Int)(x8 Int)(x14 Int)(x15 Int)) (=> (and (|$P9| x13 x10 x5 x11) (and (|$P10| x13 x10 x5 x11 x2) (and (|$P4| x13 x11 x3) (and (|$P8| x13 x10 x11 x4) (and (|$P0| x13 x10 x5 x6 x7 x8) (and (|$P4| x13 x11 x9) (and (|$P8| x13 x10 x11 x12) (and (|$P2| x13) (and (|$P0| x13 x14 x15 x16 x17 x18) (and (<= (+ 1 x11) x13) (and (= x6 (+ 1 x11)) (and (= x0 (+ x2 x3)) (and (= x7 (+ x0 x4)) (and (= x1 (+ x2 x9)) (and (= x16 (+ 1 x11)) (= x17 (+ x1 x12))))))))))))))))) (|$P0| x13 x10 x5 x11 x2 x18))))
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
