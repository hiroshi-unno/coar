; Q is eliminated by resolution, and its solution must be recovered from the solution of the
; remaining clauses (a solution printed without Q, or with a wrong Q, is the defect); sat
(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int)) (=> (P x) (Q (+ x 1)))))
(assert (forall ((x Int)) (=> (and (Q x) (<= x 0)) false)))
(check-sat)
