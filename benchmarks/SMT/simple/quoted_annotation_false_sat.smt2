(set-logic ALL)
(declare-fun |!| (Bool Bool) Bool)
(assert (|!| false false))
(check-sat)
