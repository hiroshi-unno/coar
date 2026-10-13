; pred_poly_lambda_inst_sat.smt2 with a client goal the library cannot guarantee: after two
; applications of a function that only preserves (>= 0), the result may still be 0, so
; demanding r > 0 is unsat.  expected: unsat
(set-logic DQHORN)
(declare-forall-fun X (Int) Bool)
(declare-dep-exists-fun P () ((Array Int Bool) Int Int) Bool)
(assert (forall ((x Int) (m Int) (r Int)) (=> (and (X x) (X m) (X r)) (P X x r))))
(assert (forall ((r Int)) (=> (and (P (lambda ((a Int)) (>= a 0)) 0 r) (<= r 0)) false)))
(check-sat)
