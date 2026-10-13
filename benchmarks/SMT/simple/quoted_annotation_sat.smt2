(set-logic ALL)
(declare-fun |!| (Bool Bool) Bool)
(assert (not (|!| true false)))
(check-sat)
