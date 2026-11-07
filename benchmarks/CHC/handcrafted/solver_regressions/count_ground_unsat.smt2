; Twin of count_under_forall_sat.smt2: unsatisfiable (the count is ground here, outside every binder): a
; refutation the unfolding must still find.
(set-logic HORN)
(define-fun-rec cnt ((x Int) (t Int) (a (Array Int Int))) Int
  (ite (<= t 0) 0 (+ (cnt x (- t 1) a) (ite (= (select a (- t 1)) x) 1 0))))
(declare-fun C (Int (Array Int Int) Int Int) Bool)
(assert (forall ((x Int) (m (Array Int Int))) (C x m 0 0)))
(assert (forall ((x Int) (m (Array Int Int)) (t Int) (c Int))
  (=> (and (C x m t c) (>= t 0))
      (C x m (+ t 1) (ite (= (select m t) x) (+ c 1) c)))))
(assert (forall ((x Int) (m (Array Int Int)) (t Int) (c Int) (n Int))
  (=> (and (C x m t c) (<= t 3) (>= n 1) (<= x (- n 2))
           (forall ((y Int)) (>= (select m y) 0))
           (>= (cnt x t m) 2))
      (<= c 1))))
(check-sat)
