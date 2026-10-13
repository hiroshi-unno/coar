; UNSOUNDNESS REPRODUCER for an external solver, not a problem for this tool.
;
; Z3 4.15.2 answers `sat` to the assertion below and then, in the model it
; offers for it, reports the two arrays as DIFFERING at a1:
;
;   sat
;   (((select lhs a1) true)
;    ((select rhs a1) false))
;
; The assertion says lhs = rhs, so those two reads must agree. cvc5 answers
; `unsat` on the same file, which is correct: the arrays differ at a1, since
; the store only overrides a0. There is no error line and no `unknown`.
;
; The negation is in z3_array_literal_eq_unsound_negation.smt2 and z3 answers
; `sat` to that as well -- a ground formula and its negation both satisfiable,
; which is the one-minute check for "is this Sat a report or a licence?".
;
; The index sort is a two-constructor datatype, i.e. a FINITE index domain, and
; that is the fragment the literature names as unsupported: Preiner, Niemetz and
; Barrett, "Satisfiability Modulo Extensional Constant Arrays (Extended
; Version)", arXiv:2605.16820, observes that existing implementations "only
; support a fragment of the theory for finite index domains" and give a decision
; procedure for arbitrary index domains. With an Int index both solvers answer
; correctly, which is the same boundary seen from our side.
;
; Why it is kept here: a resolution step in this tool read that `sat` as
; permission and derived a negative example from it, and a satisfiable
; constrained Horn problem then answered `unsat`. The companion is
; benchmarks/CHC/simple/resolution_wrong_unsat_sat.smt2. The workaround measured
; here is to expand such an equality into the conjunction of its reads over the
; finite index sort, which both solvers then answer correctly.
; THIS TOOL INHERITS THE ANSWER. Run it here with an SMT backend
; (`-c config/solver/dbg_z3_smt.json -p smt`) and it prints `sat` too, as does
; the negation file -- so the defect is not confined to any one phase: every
; path that asks the solver this question and believes the reply gets the wrong
; answer.
(set-logic ALL)
(set-option :produce-models true)
(declare-datatypes ((A 0)) (((a0) (a1))))
(define-fun lhs () (Array A Bool) (store ((as const (Array A Bool)) true) a0 false))
(define-fun rhs () (Array A Bool) ((as const (Array A Bool)) false))
(assert (= lhs rhs))
(check-sat)
(get-value ((select lhs a1) (select rhs a1)))
