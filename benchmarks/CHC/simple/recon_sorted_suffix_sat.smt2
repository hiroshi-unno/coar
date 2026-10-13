; A suffix of a sorted list is sorted.  [sorted] is given as a predicate
; computing a Boolean function (one defining clause per branch, as a
; verification-condition generator writes it for a recursive function), and
; [Q(l, m)] walks [l] down from [m].  The invariant [Q(l, m) := sorted(m) =>
; sorted(l)] mentions the function [sorted] itself, which no arithmetic
; qualifier expresses; reconstructing the function from its defining clauses
; makes it expressible.  Expected: sat.
(set-logic HORN)
(declare-datatypes ((Lst 0)) (((cons (head Int) (tail Lst)) (nil))))
(declare-fun sorted (Lst Bool) Bool)
(declare-fun Q (Lst Lst) Bool)
(assert (forall ((l Lst)) (=> (= l nil) (sorted l true))))
(assert (forall ((h Int) (t Lst)) (=> (= t nil) (sorted (cons h t) true))))
(assert (forall ((h1 Int) (h2 Int) (t Lst))
  (=> (> h1 h2) (sorted (cons h1 (cons h2 t)) false))))
(assert (forall ((h1 Int) (h2 Int) (t Lst) (b Bool))
  (=> (and (<= h1 h2) (sorted (cons h2 t) b)) (sorted (cons h1 (cons h2 t)) b))))
(assert (forall ((m Lst)) (Q m m)))
(assert (forall ((h Int) (t Lst) (m Lst)) (=> (Q (cons h t) m) (Q t m))))
(assert (forall ((l Lst) (m Lst))
  (=> (and (Q l m) (sorted m true) (sorted l false)) false)))
(check-sat)
