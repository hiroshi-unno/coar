; expected: unsat
;
; The direction a repair must not overshoot into: the inner binder is read and
; its body is false for every value, so the assertion is refuted. A reader that
; accepted shadowing by dropping the inner binding -- or by letting the outer
; one answer for it -- would not get this one right.
(set-logic ALL)
(assert (forall ((x Bool)) (exists ((x Bool)) (and x (not x)))))
(check-sat)
