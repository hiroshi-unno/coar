; A clause uses an integer constant that nothing declares.  z3 and cvc5 reject it
; as an unknown symbol; the reader refuses it in one line.
(set-logic HORN)
(declare-fun p (Int) Bool)
(assert (forall ((x Int)) (=> (= x c_undeclared) (p x))))
(assert (forall ((x Int)) (=> (p x) (>= x 0))))
(check-sat)
