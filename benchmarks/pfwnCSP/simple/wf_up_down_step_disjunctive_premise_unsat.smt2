; AF (x <= 1) from x = 2 on a loop that adds or subtracts 1 forever: false,
; since the run 2, 3, 2, 3, ... never reaches x <= 1.  The transition is one
; premise with an arm per branch; the refutation needs a step of each arm
; (rank(2, 3) and rank(3, 2) close a cycle no well-founded relation admits).
; The third clause says a state that is not at x <= 1 has a successor.
(set-logic HORN)
(declare-fun inv0 (Int Int) Bool)
(declare-wfp rank (Int Int Int Int) Bool)
(assert (forall ((x_PC Int) (x_X Int)) (=> (and (= x_X 2) (= x_PC 1)) (inv0 x_X x_PC))))
(assert (forall ((x_PC Int) (x_PCp Int) (x_X Int) (x_Xp Int)) (=> (and (inv0 x_X x_PC) (not (<= x_X 1)) (or (and (= x_Xp (+ x_X 1)) (and (= x_PC 1) (= x_PCp 1))) (and (= x_Xp (- x_X 1)) (and (= x_PC 1) (= x_PCp 1))))) (rank x_X x_PC x_Xp x_PCp))))
(assert (forall ((x_PC Int) (x_X Int)) (=> (and (inv0 x_X x_PC) (not (<= x_X 1)) (not (or (= x_PC 1) (= x_PC 1)))) false)))
(assert (forall ((x_PC Int) (x_PCp Int) (x_X Int) (x_Xp Int)) (=> (and (inv0 x_X x_PC) (not (<= x_X 1)) (or (and (= x_Xp (+ x_X 1)) (and (= x_PC 1) (= x_PCp 1))) (and (= x_Xp (- x_X 1)) (and (= x_PC 1) (= x_PCp 1))))) (inv0 x_Xp x_PCp))))
(check-sat)
