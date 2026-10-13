; expected: sat
;
; Shadowing ends where the inner binder ends: inside it `x` is 2, and after it
; `x` is 1 again. Both conjuncts hold, so this is satisfiable.
;
; This is the case a repair that renames the inner binder has to get right -- if
; the rename leaked past the inner body, the second conjunct would compare 2
; with 1 and the file would come back unsat.
(set-logic ALL)
(assert (let ((x 1)) (and (= (let ((x 2)) x) 2) (= x 1))))
(check-sat)
