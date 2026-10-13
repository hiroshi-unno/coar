; Z3 5.1.0 answers `sat` to this UNSATISFIABLE formula (found 2026-10-13 while
; repairing a wrong `unsat` of this tool's unfolding refuter).  `cnt x t a` counts the i < t with a[i] = x; the chain below makes c0 that count for
; t <= 3, so c0 >= 2 and x <= n - 2 contradict the universal at k := x.  The companion file
; z3_recfun_under_forall_wrong_sat_instance.smt2 is this one with that instance asserted, and
; Z3 answers it `unsat`, which proves this one unsatisfiable.  Z3 4.15.4 and cvc5 answer
; `unknown`; without the universal over y Z3 5.1.0 answers `unsat`.  Workaround: Z3interface's
; check_sat reads a `sat` about a recursive function under a quantifier as `unknown`.
(set-logic ALL)
(declare-fun m () (Array Int Int))
(define-fun-rec cnt ((x Int) (t Int) (a (Array Int Int))) Int (ite (<= t 0) 0 (+ (cnt x (- t 1) a) (ite (= (select a (- t 1)) x) 1 0))))
(declare-fun x () Int)
(declare-fun n () Int)
(declare-fun t () Int)
(declare-fun c0 () Int)
(declare-fun c1 () Int)
(declare-fun c2 () Int)
(declare-fun c3 () Int)
(declare-fun c4 () Int)
(define-fun r ((i Int)) Int (select m i))
(assert (and (<= 0 t) (<= t 3) (>= n 1) (<= x (- n 2)) (>= c0 2)))
(assert (forall ((y Int)) (>= (select m y) 0)))
(assert (forall ((k Int)) (or (> k (- n 1)) (<= (cnt k t m) 1))))
(assert (or (and (= t 0) (= c0 0)) (and (> t 0) (= c0 (ite (= (r (- t 1)) x) (+ c1 1) c1)) (or (and (= t 1) (= c1 0)) (and (> t 1) (= c1 (ite (= (r (- t 2)) x) (+ c2 1) c2)) (or (and (= t 2) (= c2 0)) (and (> t 2) (= c2 (ite (= (r (- t 3)) x) (+ c3 1) c3)) (and (= t 3) (= c3 0)))))))))
(check-sat)
