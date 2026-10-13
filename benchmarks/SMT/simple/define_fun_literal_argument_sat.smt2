; expected: sat
;
; `f 2` is 3, so the assertion holds. z3 and cvc5 both answer sat.
;
; It raised `[int_monomials_of] not supported: value(2:#svar...)`. A numeric
; literal is parsed as a value carrying a fresh sort variable, settled by the
; whole-formula type inference that runs at the very end; a definition's body is
; type-checked when it is declared, so its arithmetic is already Int-specific.
; Inlining put the second around the first, and the normalization that runs
; between the two dispatched on the typed addition and refused the untyped
; argument.
;
; Two things hid it: a call whose argument is a declared variable carries that
; variable's sort, and the same arithmetic written out in the assertion is typed
; along with everything around it. Both are in the file beside this one.
(set-logic ALL)
(define-fun f ((n Int)) Int (+ n 1))
(assert (= (f 2) 3))
(check-sat)
