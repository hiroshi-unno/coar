; The negation of z3_array_literal_eq_unsound.smt2. Z3 4.15.2 answers `sat` to
; this AND to the un-negated file, so a ground formula and its negation are both
; satisfiable: the solver is not deciding the question, and any step licensed by
; that `sat` is licensed by nothing. cvc5 answers `sat` here and `unsat` there,
; which is the consistent pair.
; This tool answers `sat` here as well, through its own SMT backend.
(set-logic ALL)
(declare-datatypes ((A 0)) (((a0) (a1))))
(define-fun lhs () (Array A Bool) (store ((as const (Array A Bool)) true) a0 false))
(define-fun rhs () (Array A Bool) ((as const (Array A Bool)) false))
(assert (not (= lhs rhs)))
(check-sat)
