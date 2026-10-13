; Satisfiable (C := the graph of cnt).  The goal's premises put
; the recursive count under a universal, and the unfolding of C compared with it
; is a question Z3 5.1.0 answers `sat` although it is unsatisfiable; the
; unfolding refuter read that `sat` as a countermodel and answered `unsat`.
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
           (forall ((k Int)) (or (> k (- n 1)) (<= (cnt k t m) 1))))
      (<= c 1))))
(check-sat)
