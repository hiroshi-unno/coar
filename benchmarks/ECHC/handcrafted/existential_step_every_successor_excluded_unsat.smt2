; An existential clause head with one step: every state with P >= 1 and PC = 2 must be in phi1, phi1 implies
; P >= 1, and every phi1 state needs a successor in phi1 among five moves; every successor of a PC = 2 state has
; P <= 0, so no phi1 exists (unsat).  The refutation needs one state and one step, but after skolemisation the
; head phi1(x') mentions the witnesses' results, and refuting it means a case split over every witness value.
; The three phi1 clauses of the CTL query EF EG(p > 0) of ConSynth's ehsf/cav13/erics/18-EFEG-fail.qarmc,
; translated by hand.
(set-logic HORN)
(declare-fun phi1 (Int Int Int) Bool)
(assert (forall ((x_P Int) (x_PC Int) (x_X Int)) (=> (and (>= x_P 1) (= x_PC 2)) (phi1 x_X x_P x_PC))))
(assert (forall ((x_P Int) (x_PC Int) (x_X Int)) (=> (phi1 x_X x_P x_PC) (exists ((x_Xp Int) (x_Pp Int) (x_PCp Int)) (and (or (and (> x_X 0) (= x_PC 1) (= x_Xp (- x_X 1)) (= x_Pp x_P) (= x_PCp 1)) (and (> x_X 0) (= x_PC 1) (= x_Xp (+ x_X 1)) (= x_Pp x_P) (= x_PCp 1)) (and (<= x_X 0) (= x_PC 1) (= x_Xp x_X) (= x_Pp x_P) (= x_PCp 2)) (and (= x_PC 2) (= x_Xp x_X) (= x_Pp (- 1)) (= x_PCp 2)) (and (= x_PC 2) (= x_Xp x_X) (= x_Pp 0) (= x_PCp 2))) (phi1 x_Xp x_Pp x_PCp))))))
(assert (forall ((x_P Int) (x_PC Int) (x_X Int)) (=> (phi1 x_X x_P x_PC) (>= x_P 1))))
(check-sat)
