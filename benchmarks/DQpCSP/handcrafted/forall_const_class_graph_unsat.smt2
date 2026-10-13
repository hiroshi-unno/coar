; The predicate simulation of forall_const_class_sat.smt2: the universal constant a is replaced by
; a universal predicate A intended as the singleton {a}.  At a two-element A meeting both T and
; its complement the first clause forces Q and the second refutes it: unsat.  Over the empty theory
; no QECHC repair exists (by the automorphism argument of forall_const_class_sat.smt2).  expected: unsat
(set-logic DQHORN)
(declare-forall-sort al)
(declare-forall-fun A (al) Bool)
(declare-forall-fun T (al) Bool)
(declare-dep-exists-fun Q (A T) () Bool)
(assert (forall ((x al)) (=> (and (A x) (T x)) Q)))
(assert (forall ((x al)) (=> (and Q (A x)) (T x))))
(check-sat)
