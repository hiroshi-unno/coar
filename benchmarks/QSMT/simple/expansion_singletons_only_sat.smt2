; Why an instantiation pattern must include PAIRS, half two.
;
; The same instance set as expansion_with_pairs_unsat.smt2 with its decisive instance (H,H,T) --
; two predicates at the hole, one at the constant -- replaced by a third singleton (T,T,H).  That is
; exactly what a generator producing only singletons and the full set can express, and it is not
; enough: the refutation is lost and the solver returns `unknown`.
;
; Keep the two together.  Read alone this file says only "a solver did not answer", which is the
; absence of evidence; read against its twin it says which instance shape carries the proof.
;
; expected: sat -- Z3 returns `unknown`, which is the point: the shape is missing, not the budget.
(set-logic ALL)
(declare-fun f1 ((Array Int Bool) (Array Int Bool) Int) Int)
(declare-fun f2 ((Array Int Bool) (Array Int Bool) Int) Int)
(declare-fun f3 ((Array Int Bool) (Array Int Bool) Int) Int)
(define-fun T () (Array Int Bool) ((as const (Array Int Bool)) true))
(define-fun ok ((u (Array Int Bool))) Bool
  (forall ((h Int)) (or (select u h) (select u (+ h 1)))))
(define-fun prop ((q1 (Array Int Bool)) (q2 (Array Int Bool)) (q3 (Array Int Bool)) (i Int)) Bool
  (=> (and (ok q1) (ok q2) (ok q3))
      (and (= (f1 q1 q2 i) (f2 q2 q3 i))
           (= (f2 q2 q3 i) (f3 q3 q1 i))
           (or (select q1 (f1 q1 q2 i)) (select q2 (f1 q1 q2 i)) (select q3 (f1 q1 q2 i))))))
(declare-const i Int)
(define-fun v () Int (f1 T T i))
(define-fun H () (Array Int Bool) (lambda ((n Int)) (not (= n v))))
(assert (prop T T T i))
(assert (prop H T T i))
(assert (prop T H T i))
(assert (prop T T H i))
(assert (prop H H H i))
(check-sat)
