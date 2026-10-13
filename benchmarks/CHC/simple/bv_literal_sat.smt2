; An SMT-LIB form the reader once refused: the indexed bit-vector literal (_ bvN w) (SMT path, -p smt with z3_smt.json).  Expected: sat.
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x (bvadd (_ bv5 8) #x02)))
(assert (= x (_ bv7 8)))
(check-sat)
