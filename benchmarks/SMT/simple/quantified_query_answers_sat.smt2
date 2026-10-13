; expected: sat
;
; Take y = x + 1. z3 and cvc5 both answer sat in hundredths of a second.
;
; This tool did not answer it at all. Every query goes to a pooled solver inside
; a pushed scope -- cheap, and measured to be so over ten thousand calls -- but
; asserting inside a scope leaves Z3 in incremental mode, where the strategies
; available to it are not the ones it uses on a fresh solver. On this formula the
; difference is decisive: fresh gives sat in 0.03 s, the same assertion inside a
; push gives "unknown (incomplete quantifiers)" after two seconds, and through
; the wrapper it did not come back.
;
; A query carrying a quantifier now gets a solver with no scope. The three files
; beside this one are the controls that say the difference is about this shape
; and not about quantifiers in general: two other quantified queries were
; answered either way, and so was the negation of this one.
(set-logic ALL)
(assert (forall ((x Int)) (exists ((y Int)) (> y x))))
(check-sat)
