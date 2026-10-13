; Why an instantiation pattern must include PAIRS, half one.
;
; The three-party agreement input (three predicates, each device seeing two of them, no
; communication) is refuted by five instances of its functional reading.  The decisive one is
;
;     (H, H, T)  --  TWO of the three predicates at the hole and the third at the constant
;
; and a generator that produces only "all of them at the candidate" and "one of them at the
; candidate, the rest at the constant" cannot express it.  This file is that instance set; its twin
; expansion_singletons_only_sat.smt2 is the same set with (H,H,T) replaced by another singleton, and
; the pair of verdicts is the measurement -- neither file means anything alone.
;
; H is the point hole at v = f1(T,T,i), the value named by one of the witness functions at the
; constant array; T is the constant true array.  Each f_j takes only the predicates its own
; dependency set allows, which is what makes the question the dependency-respecting one.
;
; expected: unsat
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
(assert (prop H H T i))
(assert (prop H H H i))
(check-sat)
