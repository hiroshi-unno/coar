; A match whose cases do not cover every constructor (nil is missing) is not
; well formed in SMT-LIB 2.6; z3 and cvc5 both reject it.  The reader refuses it
; with one line rather than invent a value for the missing constructor.
(set-logic HORN)
(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))
(declare-fun P (Lst) Bool)
(assert (P (cons 1 nil)))
(assert (forall ((l Lst)) (=> (P l) (match l (((cons h t) (> h 0)))))))
(check-sat)
