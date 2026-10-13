; An SMT-LIB command the reader once refused: check-sat-assuming; its literals are read as assertions.  Expected: sat (P = x >= 0).
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (P x) (> x -1))))
(check-sat-assuming ((P 0)))
