; A universal CONSTANT a of a forall-sort and a
; universal class predicate T; the nullary unknown Q must record T(a) exactly.  Over the empty
; theory every permutation of the carrier preserving T is an automorphism, and that symmetry is
; what makes the separation from universal predicates provable here (over LIA it is only
; conjectured, see forall_fun_sign_sat.smt2).  expected: sat
(set-logic DQHORN)
(declare-forall-sort al)
(declare-forall-fun a () al)
(declare-forall-fun T (al) Bool)
(declare-dep-exists-fun Q (a T) () Bool)
(assert (=> (T a) Q))
(assert (=> Q (T a)))
(check-sat)
