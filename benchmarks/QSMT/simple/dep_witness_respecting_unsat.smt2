; The refutation a dependency-quantified problem admits when the witness of a head existential
; sees only the universal function its unknown depends on -- and the twin beside it,
; dep_witness_linearised_sat.smt2, is the same thing with the witness seeing both, which is what a
; solver that drops the dependency set is left holding.
;
; The problem.  Two devices must meet on a common channel with no communication.  Ok1 and Ok2 are
; universally quantified predicates (arrays here) saying which channels each device can use; each
; device's choice may depend only on its OWN predicate.  The specification demands the two choices
; be equal and usable on at least one device.  It is unsatisfiable: equality under every
; interpretation forces both choices to be a function of the seed alone, and the adversary then
; makes that channel unusable on both.
;
; f1 takes only u1 and f2 only u2, which is the dependency the declaration states.  Two
; instantiations are enough to refute: the constant true array fixes the common value v, and the
; point hole (lambda n. n /= v) -- the array false exactly at v and nowhere else, which still has no
; two consecutive falses -- makes the specification's second conjunct false at it.
;
; expected: unsat
(set-logic ALL)
(declare-fun f1 ((Array Int Bool) Int) Int)
(declare-fun f2 ((Array Int Bool) Int) Int)
(define-fun T () (Array Int Bool) ((as const (Array Int Bool)) true))
(define-fun ok ((u (Array Int Bool))) Bool
  (forall ((c Int)) (or (select u c) (select u (+ c 1)))))
(define-fun prop ((u1 (Array Int Bool)) (u2 (Array Int Bool)) (i Int)) Bool
  (=> (and (ok u1) (ok u2))
      (and (= (f1 u1 i) (f2 u2 i)) (or (select u1 (f1 u1 i)) (select u2 (f2 u2 i))))))
(define-fun v () Int (f2 T 0))
(define-fun H () (Array Int Bool) (lambda ((n Int)) (not (= n v))))
(assert (prop H T 0))
(assert (prop H H 0))
(check-sat)
