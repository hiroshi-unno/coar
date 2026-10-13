; expected: sat
;
; No convention for `0 ^ 0` is needed to decide this: the premise says `x` is
; zero, so the two terms are the same term and are equal whatever `0 ^ 0` is.
; There is no unknown, so the question is validity, and the clause is valid.
; z3 answers `unsat` to the negation. (cvc5 rejects a symbolic exponent and is
; not an oracle here.)
;
; It answered `unsat` because `0 ^ e` was folded to `0` whenever `e` was not
; *syntactically* the literal zero -- which a variable never is, whatever its
; value -- while the ground `0 ^ 0` folded to `1`, leaving `0 = 1`. Simplifying
; and then substituting therefore disagreed with substituting and then
; simplifying. The fold now asks for a positive literal exponent, so it declines
; on a variable and the equation survives to the solver.
(set-logic HORN)
(assert (forall ((x Int)) (=> (= x 0) (= (^ 0 x) (^ 0 0)))))
(check-sat)
