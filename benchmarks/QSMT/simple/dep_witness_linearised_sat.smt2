; The same problem as dep_witness_respecting_unsat.smt2 with each witness function seeing BOTH
; universal predicates instead of only the one its unknown depends on -- the linearisation.
;
; It is the form a solver works on if it Skolemises a head existential with every universal in the
; clause rather than with the unknown's dependency set, and the point of the pair is that the two
; forms have different answers: the twin is refuted by two instantiations, and this one is not
; refutable at all, because the two witnesses may now coordinate through the predicate neither is
; supposed to see.  Enlarging a dependency set only admits more solutions, so `unsat` on this form
; would still be sound and `sat` on it says nothing about the original.
;
; expected: sat -- Z3 returns `unknown` on it rather than a model, which is why the pair is kept as
; a pair: the discrimination that matters is unsat here against unsat there, and only the twin
; delivers one.
(set-logic ALL)
(declare-fun f1 ((Array Int Bool) (Array Int Bool) Int) Int)
(declare-fun f2 ((Array Int Bool) (Array Int Bool) Int) Int)
(define-fun T () (Array Int Bool) ((as const (Array Int Bool)) true))
(define-fun ok ((u (Array Int Bool))) Bool
  (forall ((c Int)) (or (select u c) (select u (+ c 1)))))
(define-fun prop ((u1 (Array Int Bool)) (u2 (Array Int Bool)) (i Int)) Bool
  (=> (and (ok u1) (ok u2))
      (and (= (f1 u1 u2 i) (f2 u1 u2 i)) (or (select u1 (f1 u1 u2 i)) (select u2 (f2 u1 u2 i))))))
(define-fun v () Int (f2 T T 0))
(define-fun H () (Array Int Bool) (lambda ((n Int)) (not (= n v))))
(assert (prop H T 0))
(assert (prop H H 0))
(check-sat)
