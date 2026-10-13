; A theory-sensitive universally quantified CHC system:
;   P(0);  P(x) => P(x+1);  (forall x. P(x)) => false
; read over N.  Over Z the premise needs the guard x >= 0, or the negative integers
; falsify it and the system becomes satisfiable over Z itself.
; Standard Z: the least solution is the non-negatives, the premise holds, UNSATISFIABLE.
; A non-standard Z*: the least solution is the standard non-negatives only, the premise fails at a
; non-standard element, satisfiable.  So standard: unsat; some model: sat; every model: unsat.
; expected: unsat
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (P 0))
(assert (forall ((x Int)) (=> (P x) (P (+ x 1)))))
(assert (=> (forall ((x Int)) (=> (>= x 0) (P x))) false))
(check-sat)
