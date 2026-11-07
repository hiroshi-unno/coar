; An existential step whose transition has a local input rho in [0, 1], chosen with the successor:
; inv = {0} is a solution (rho = 0), so the system is sat. Binding rho universally demands a successor
; for rho = 1 as well, which leaves {x <= 0}: unsat, the wrong answer.
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x_X Int)) (=> (= x_X 0) (inv x_X))))
(assert (forall ((x_X Int)) (=> (inv x_X) (exists ((x_Xp Int) (x_Rho_m0 Int)) (and (= x_Xp (+ x_X x_Rho_m0)) (>= x_Rho_m0 0) (<= x_Rho_m0 1) (inv x_Xp))))))
(assert (forall ((x_X Int)) (=> (inv x_X) (<= x_X 0))))
(check-sat)
