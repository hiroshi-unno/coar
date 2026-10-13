; UNSOUNDNESS REPRODUCER for an external solver, not a problem for this tool.
;
; The companion of z3_array_literal_eq_unsound.smt2 with an index sort that is
; finite without being an enumeration: a one-constructor record of two fields
; over a two-element sort, which is what a front end that monomorphises by name
; makes of Mut<T> once the finite-instantiation pass has fixed T to two
; elements. Z3 4.15.2 answers `sat`; cvc5 answers `unsat`, which is correct,
; since the arrays differ at (mk f0 f0). z3 also answers `sat` when the index
; sort is Bool.
;
; Why it is kept here: the rewrite this tool applies before asking such an
; equality recognised only enumerations, so this shape reached the solver, and
; a conflict between two examples whose arguments were these two different
; literals refuted a satisfiable problem. The companion is
; benchmarks/CHC/simple/array_literal_record_index_sat.smt2.
(set-logic ALL)
(set-option :produce-models true)
(declare-datatypes ((F 0)) (((f0) (f1))))
(declare-datatypes ((M 0)) (((mk (cur F) (fin F)))))
(define-fun lhs () (Array M Bool) (store ((as const (Array M Bool)) true) (mk f0 f1) false))
(define-fun rhs () (Array M Bool) ((as const (Array M Bool)) false))
(assert (= lhs rhs))
(check-sat)
(get-value ((select lhs (mk f0 f0)) (select rhs (mk f0 f0))))
