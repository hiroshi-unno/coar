; expected: sat
;
; The same for `let`, whose binder shadows in exactly the same way: the inner
; binding wins, so the body is true. z3 and cvc5 answer sat.
;
; It exited 1 with `[Map.add_exn] got key already present`, the same conflation
; one level down: the inner `let` put its name into the enclosing scope with an
; insertion that refuses an existing key.
(set-logic ALL)
(assert (let ((x false)) (let ((x true)) x)))
(check-sat)
