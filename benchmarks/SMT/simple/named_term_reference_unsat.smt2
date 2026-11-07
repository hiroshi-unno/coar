; (! t :named n) defines n as t for every later command: the check assumes (not pos), where pos is x > 0.
(set-logic QF_LIA)
(declare-const x Int)
(assert (! (> x 0) :named pos))
(check-sat-assuming ((not pos)))
