; count_under_forall_sat.smt2 in the unknown-free form: valid (instantiate the universal at k := x), so
; satisfiable.  Z3 5.1.0 answers the negation of this clause `sat` (a recursive count under a
; universal, beside a second universal), and the zero-unknown verdict's quick sweep read that
; as a countermodel and answered `unsat`.
(set-logic HORN)
(define-fun-rec cnt ((x Int) (t Int) (a (Array Int Int))) Int
  (ite (<= t 0) 0 (+ (cnt x (- t 1) a) (ite (= (select a (- t 1)) x) 1 0))))
(define-fun r ((m (Array Int Int)) (i Int) (x Int)) Int (ite (= (select m i) x) 1 0))
(assert (forall ((x Int) (m (Array Int Int)) (t Int) (n Int))
  (=> (and (<= 0 t) (<= t 3) (>= n 1) (<= x (- n 2))
           (forall ((y Int)) (>= (select m y) 0))
           (forall ((k Int)) (or (> k (- n 1)) (<= (cnt k t m) 1))))
      (<= (ite (= t 0) 0 (ite (= t 1) (r m 0 x) (ite (= t 2) (+ (r m 0 x) (r m 1 x)) (+ (r m 0 x) (r m 1 x) (r m 2 x))))) 1))))
(check-sat)
