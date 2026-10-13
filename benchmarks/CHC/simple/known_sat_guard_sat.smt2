; Expected: sat.  A candidate wrong-`unsat` input for the resolver's example builder.
;
; The open term is `(mytl mynil)`, a selector applied to the wrong constructor: its value is
; fixed within a model and differs across models.  Resolution can derive both
;
;   P(0)      from  R(0)  and  R(x) /\ (mytl mynil = mynil)  => P(x)
;   not P(0)  from  not T(0)  and  P(x) /\ (mytl mynil != mynil) => T(x)
;
; each from a Z3 model of its matching condition, and the model leaves the residue
; `mytl mynil = mynil` (resp. its negation) as the derived example's guard.  The guard is
; satisfiable, not valid, and the two guards are jointly impossible.  Dropping both -- which the
; builder did because the model showed each satisfiable -- makes the two examples one key on both
; sides and refutes a satisfiable problem.
;
; A solution, a formula per unknown valid in every model:
;
;   R(x) := x = 0
;   P(x) := x = 0 /\ mytl mynil = mynil
;   T(x) := false
;
; Asserting the negation of the conjunction of the four clauses with it substituted is `unsat`
; under z3 and under cvc5.  Whether the default CEGIS trajectory reaches the two derivations was
; not measured when this file was added.
(set-logic HORN)
(declare-datatypes ((Lst 0)) (((mynil) (mycons (myhd Int) (mytl Lst)))))
(declare-fun R (Int) Bool)
(declare-fun P (Int) Bool)
(declare-fun T (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (R x))))
(assert (forall ((x Int)) (=> (and (R x) (= (mytl mynil) mynil)) (P x))))
(assert (forall ((x Int)) (=> (and (P x) (not (= (mytl mynil) mynil))) (T x))))
(assert (forall ((x Int)) (=> (T x) false)))
(check-sat)
