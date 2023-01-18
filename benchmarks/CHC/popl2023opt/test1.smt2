(set-logic HORN)
(declare-fun P (Int) Bool)

(assert (forall ((x Int) (y Int)) (=> (P x) (P y))))

(check-sat)

;result :(define-fun P ((_FH_0 Int)) Bool true)