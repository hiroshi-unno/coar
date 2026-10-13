; (tl nil) is interpretation-dependent (its value differs across models), so a clause Z3 calls
; invalid is false only in some model, not unsatisfiable; reading it as unsat was a wrong answer; satisfiable by P(y, x) := y != nil; sat
(set-logic HORN)
(declare-datatypes ((List 0)) (((nil) (cons (hd Int) (tl List)))))
(declare-fun P (List Int) Bool)
(assert (=> (= (tl nil) nil) (not (P (tl nil) 0))))
(assert (=> (= (tl nil) nil) (not (P (tl nil) 1))))
(assert (=> (= (tl nil) nil) (not (P (tl nil) 2))))
(assert (=> (= (tl nil) nil) (not (P (tl nil) 3))))
(assert (=> (not (= (tl nil) nil)) (P (tl nil) 0)))
(assert (=> (not (= (tl nil) nil)) (P (tl nil) 1)))
(assert (=> (not (= (tl nil) nil)) (P (tl nil) 2)))
(assert (=> (not (= (tl nil) nil)) (P (tl nil) 3)))
(check-sat)
