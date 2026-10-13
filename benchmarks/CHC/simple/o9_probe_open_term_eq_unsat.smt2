; Expected: unsat.  Two lines, no predicate, and it asks one question: what does the solver hold
; about a term the theory does not fix?
;
; (mytl mynil) is a selector applied to the wrong constructor.  The datatype theory declares
; selectors total and leaves that value unconstrained, so a model may give it any list.  The single
; clause here is refuted exactly when "(mytl mynil) = mynil" is NOT valid, which it is not --
; a model exists either way.  So the answer is unsat under this tool's semantics, where a
; constraint must hold in every model of the theory, and sat under the reading that lets the solver
; choose the model.
;
; The pair (this file and its sibling with the relation flipped) is the instrument: a solver that
; answers sat to BOTH picks the model; one that answers unsat to both requires every model; one
; that answers unsat to exactly one has fixed the term to a value.  Measured 2026-09-21: this tool
; answers unsat to both, and so does Eldarica 2.3, which is a CHC solver reading the term the same
; way.  cvc5 1.0.4 answers sat to both and has no CHC mode at all, so that is plain SMT with the
; predicate uninterpreted.  z3's Horn engine answers unknown to both -- it declines wherever the two
; readings differ, including on a proper CHC with a recursive predicate.  hoice answers sat to both,
; which contradicts its own unsat on o9_interp_semantics_unsat.smt2, so it cannot be cited at all.
(set-logic HORN)
(declare-datatypes ((Lst 0)) (((mynil) (mycons (myhd Int) (mytl Lst)))))
(assert (=> (= (mytl mynil) mynil) false))
(check-sat)
