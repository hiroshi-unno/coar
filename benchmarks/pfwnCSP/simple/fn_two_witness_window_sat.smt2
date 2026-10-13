; Satisfiable.  The functional (skolemised) half of a pair built for the experiment that compares
; a functional witness against a merely total one; its twin tot_two_witness_window_sat.smt2 is
; the same problem with P declared total over its first argument instead of functional.
;
; The problem both files encode is  forall x. exists y. x <= 2y <= x + 3.  Here the existential is
; already skolemised: P is the witness, declared functional (total and single-valued), and occurs
; only negatively, as the skolemisation of a head existential puts it.
;
; The witness is NOT single-valued.  For every integer x the window [x, x + 3] holds four
; consecutive integers, exactly two of them even, so exactly two y satisfy it:
; ceil(x/2) and ceil(x/2) + 1.  (Checked with z3: with d = (x + 1) div 2, both d and d + 1 lie in
; the window for every x, and no other y does.)
;
; Why it is satisfiable: P(x, y) := (2y = x \/ 2y = x + 1), i.e. y = ceil(x/2), is total and
; single-valued and implies the clause.  So the verdict is sat, and it is the same verdict as the
; twin's, since both encodings are equisatisfiable with the unskolemised problem.
;
; What the pair is for, derived from reading the templates and NOT run: a functional template
; writes y = e(x), e a guarded choice among finitely many expressions c0 + c1*x with integer
; coefficients.  Finitely many pieces cover the integers, so one piece holds on infinitely many x,
; and there 2y - x = (2*c1 - 1)*x + 2*c0 must stay in [0, 3], impossible because 2*c1 - 1 is never
; 0.  That holds whatever the guards are, a divisibility guard included; only a term of slope 1/2
; such as (x + 1) div 2 among the template's terms would change it.  So no single-valued solution
; is in that space, while the total relation P(x, y) := x <= 2y <= x + 3 -- two affine atoms, and
; not single-valued -- is a solution the twin admits and this file does not.  Expected of a correct
; run: sat, or no answer; never unsat.
(set-logic HORN)
(declare-fnp P (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (P x y) (and (<= x (* 2 y)) (<= (* 2 y) (+ x 3))))))
(check-sat)
