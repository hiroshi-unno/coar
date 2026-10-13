(set-logic ALL)
(declare-fun |!| (Int Int) Bool)
(assert (|!| 0 1))
(check-sat)
