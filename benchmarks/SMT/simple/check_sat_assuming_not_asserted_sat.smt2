; check-sat-assuming's literals belong to that check only: the last check assumes (not a) alone.
(set-logic QF_UF)
(declare-const a Bool)
(check-sat-assuming (a))
(check-sat-assuming ((not a)))
(exit)
