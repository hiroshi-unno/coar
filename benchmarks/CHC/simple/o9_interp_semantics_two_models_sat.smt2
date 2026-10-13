; Expected: sat.  A solution exists and is written out below.
;
; This file was added as `..._two_models_unsat.smt2` with the opposite expectation, and the
; argument in its header was wrong.  It read: a solution has to satisfy every constraint in every
; model, and P does not vary with the model, so one model forces P 0 .. P 3 and another forces
; their negations, and no P exists.  The error is in the last step.  A solution is a FORMULA over
; the signature, evaluated in each model: the formula is fixed, its VALUE is not.
;
;   P(x) := (mytl mynil = mynil) /\ (x = 0 \/ x = 1 \/ x = 2 \/ x = 3)
;
; satisfies all eight clauses in every model.  Where the equality holds, P 0 .. P 3 are true and
; the first group is met while the second is vacuous; where it fails, P is false everywhere and the
; second group is met while the first is vacuous.  Asserting the negation of the conjunction of the
; eight clauses with that definition substituted is `unsat` under z3 and under cvc5, so every
; clause is valid in every model.
;
; Two external Horn solvers agree on the file itself: cvc5 and hoice both answer `sat`; z3's Horn
; engine answers `unknown`.  The problem is satisfiable under all three readings of satisfiability
; -- choose the model too, give each model its own interpretation, or exhibit the single formula
; above -- so it separates nothing and never did.
;
; The sibling `o9_interp_semantics_unsat.smt2` is the file that DOES separate the readings, and it
; is genuinely unsat under the one this tool uses: its second clause is an unconditional `not P 0`,
; so where the equality holds the two clauses force P 0 both ways.  cvc5 answers `sat` there and
; hoice answers `unsat`, which is where the two readings come apart.
;
; What this file caught, and why it is kept: the tool answered `unsat` on it for a day, with the
; refutation certified, because a ground guard was discharged whenever SOME model satisfied it.
; That licenses nothing -- dropping the guard claims the atom in every model, which needs the guard
; to be VALID -- and here the two guards are an equation and its negation, each satisfiable and
; jointly impossible.  Discharge now requires validity, and the conflict test that compares two
; examples conjoins their guards, which is the sound form of the same reasoning.
(set-logic HORN)
(declare-datatypes ((Lst 0)) (((mynil) (mycons (myhd Int) (mytl Lst)))))
(declare-fun P (Int) Bool)
(assert (=> (= (mytl mynil) mynil) (P 0)))
(assert (=> (= (mytl mynil) mynil) (P 1)))
(assert (=> (= (mytl mynil) mynil) (P 2)))
(assert (=> (= (mytl mynil) mynil) (P 3)))
(assert (=> (and (not (= (mytl mynil) mynil)) (P 0)) false))
(assert (=> (and (not (= (mytl mynil) mynil)) (P 1)) false))
(assert (=> (and (not (= (mytl mynil) mynil)) (P 2)) false))
(assert (=> (and (not (= (mytl mynil) mynil)) (P 3)) false))
(check-sat)
