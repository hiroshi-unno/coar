; NOT well-founded: a self-loop; WF also occurs in a body, where inlining its definition would
; drop the well-foundedness requirement.  Expected: unsat.
(set-logic HORN)
(declare-wfp WF (Int Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (> x 0) (= y x)) (WF x y))))
(assert (forall ((x Int) (y Int)) (=> (WF x y) (Q x))))
(check-sat)
