; A let may not bind -1 either: it is a numeral, and cvc5 1.4.2 refuses the binder.  Read as the
; number in the body, the binding would be silently ignored.
(set-logic ALL)
(declare-fun x () Int)
(assert (let ((-1 5)) (= x -1)))
(check-sat)
