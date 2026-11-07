; Expected: unsat.
;
; `(/ 1.0 0.0)` and `(/ 2.0 0.0)` are two applications of division at a zero
; divisor, and the theory of reals fixes neither: a model may give them
; different values.  In such a model the premise of the first clause holds, P 0
; is forced and the second clause forbids it, so the system has no solution --
; a solution must hold in every model.
;
; It answered `sat` because the constant folder evaluated both quotients with
; arbitrary-precision rationals, whose division by zero returns positive
; infinity for any positive numerator; the two became one literal, `distinct`
; folded to false and the first clause disappeared.
(set-logic HORN)
(declare-fun P (Real) Bool)
(assert (=> (distinct (/ 1.0 0.0) (/ 2.0 0.0)) (P 0.0)))
(assert (=> (P 0.0) false))
(check-sat)
