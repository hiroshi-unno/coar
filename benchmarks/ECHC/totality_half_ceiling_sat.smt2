; Satisfiable, and built to compare skolemising into a functional (FN) predicate against a
; Totality kind: a head existential whose witness is definable as a RELATION in affine arithmetic
; but not as an affine FUNCTION with integer coefficients.
;
; Solution: P(x, y) := x <= 2y /\ 2y <= x + 1, i.e. y = ceil(x / 2).  The witness is unique, so a
; functional and a merely total witness admit the same solutions; what differs is what the
; template languages can SAY.  A relational template states it with two affine atoms.  A
; functional template writes y = t(x) with t a piecewise-affine term with integer coefficients,
; and ceil(x / 2) has slope 1/2, so no finite such term equals it on all integers (a guard would
; need x mod 2).  So skolemising into FN puts the solution outside the default function template,
; while Totality would not.  Nothing has been run on this file.
(set-logic HORN)
(declare-fun P (Int Int) Bool)
(assert (forall ((x Int)) (exists ((y Int)) (P x y))))
(assert (forall ((x Int) (y Int)) (=> (P x y) (and (<= x (* 2 y)) (<= (* 2 y) (+ x 1))))))
(check-sat)
