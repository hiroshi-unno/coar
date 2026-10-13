; Satisfiable.  The total half of a pair built for the experiment that compares a functional
; witness against a merely total one; its twin fn_two_witness_window_sat.smt2 is the same problem
; with P declared functional instead.
;
; The problem both files encode is  forall x. exists y. x <= 2y <= x + 3.  P is the witness of the
; existential, declared total over its first argument (position 0): for every x some y has
; P(x, y).  It occurs only negatively, as the skolemisation of a head existential puts it.
; Totality is all the skolemisation needs: a total P whose every point satisfies the body gives
; the existential a witness at every x, and conversely the body's own witness set is such a P.
;
; The witness is NOT single-valued.  For every integer x the window [x, x + 3] holds four
; consecutive integers, exactly two of them even, so exactly two y satisfy it:
; ceil(x/2) and ceil(x/2) + 1.  (Checked with z3: with d = (x + 1) div 2, both d and d + 1 lie in
; the window for every x, and no other y does.)
;
; Why it is satisfiable: P(x, y) := x <= 2y /\ 2y <= x + 3 is total (y = ceil(x/2) is in it at
; every x) and implies the clause by construction.  It is two affine atoms and holds at two y for
; every x, so it is a solution here and not in the twin, which demands a single-valued P.  So the
; verdict is sat, the twin's verdict too, since both encodings are equisatisfiable with the
; unskolemised problem.
;
; What the pair is for, derived from reading the templates and NOT run: the solution above is
; stated only by a template that is a general relation with totality as a side condition of the
; synthesis query (a forall-exists alternation).  A template that builds totality in by
; construction contains the graph of a function y = e(x) with e piecewise affine with integer
; coefficients, and no such e stays in the window at every x (2*e(x) - x would need slope 0 on
; infinitely many x, where it is 2*c1 - 1).  So a relation-plus-function-graph template can state
; it only through its relation part, and the clause forces the function part into the window too.
; Expected of a correct run: sat, or no answer; never unsat.
(set-logic HORN)
(declare-totp (0) P (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (P x y) (and (<= x (* 2 y)) (<= (* 2 y) (+ x 3))))))
(check-sat)
