; expected: unsat
; Formula and term occurrences of one quoted Boolean symbol share identity.
(set-logic QF_UF)
(declare-const |a"b| Bool)
(assert |a"b|)
(assert (= |a"b| false))
(check-sat)
