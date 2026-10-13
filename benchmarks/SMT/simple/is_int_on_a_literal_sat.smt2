; expected: sat
;
; `is_int` asks of a real whether it denotes an integer; 1.5 does not, so the
; negation holds and the problem is satisfiable. z3 and cvc5 both answer sat.
;
; It exited 1 with `not supported: value(3/2:#svar...)`. Constraint generation
; had no case for this predicate, and its fallback neither visits the argument
; nor gives it a sort, so the literal kept the fresh sort variable it is parsed
; with and reached the solver boundary unresolved. Binding the argument to a
; declared real first made the file pass, which is why a typed-variable example
; is not a test of this operator.
(set-logic ALL)
(assert (not (is_int 1.5)))
(check-sat)
