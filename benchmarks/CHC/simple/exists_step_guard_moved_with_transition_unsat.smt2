; An existential step whose transition has a guard: inv(x) => exists x'. x <= 2 /\ x' = x + 1 /\ inv(x').
; inv must hold at 0, 1, 2, 3 and has no successor at 3, so the system is unsat. Splitting the guard off
; the moved transition (leaving x <= 2 in the premise) lets inv = {0..3} through: sat, the wrong answer.
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x_X Int)) (=> (= x_X 0) (inv x_X))))
(assert (forall ((x_X Int)) (=> (inv x_X) (exists ((x_Xp Int)) (and (<= x_X 2) (= x_Xp (+ x_X 1)) (inv x_Xp))))))
(assert (forall ((x_X Int)) (=> (inv x_X) (<= x_X 5))))
(check-sat)
