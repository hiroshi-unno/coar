; An external-solver reproducer, not a problem for this tool to solve.
;
; Z3 4.15.2 answers `unknown` to the assertion below. The two lambda arrays are
; extensionally equal over the two-element index sort -- at a0 both give true,
; at a1 both give false -- so the correct answer is `sat`. Asking the NEGATION
; instead gives `unsat`, which proves they are equal, so this is incompleteness
; rather than a wrong answer: the two replies are consistent, and one of them
; carries no information.
;
; It is not about the index sort being finite: the same shape over `Int`,
;   (= (lambda ((x Int)) (= x 0)) (lambda ((y Int)) (not (distinct y 0))))
; is `unknown` too.
;
; WHAT MAKES IT FIRE, because the obvious reproducer does not. Two lambdas whose
; bodies are SYNTACTICALLY identifiable are decided instantly --
;   (= (lambda ((x Int)) (+ x 1)) (lambda ((y Int)) (+ 1 y)))   is unsat-negation
; -- because simplification closes them. The bodies here are equal only
; SEMANTICALLY, and that is what the solver does not reach.
;
; THE WORKAROUND AND ITS OTHER HALF. `Evaluator.simplify` rewrites an equality
; between two lambda arrays into the quantified form the extensionality axiom
; states, `forall i. b1[i/x] = b2[i/y]`, and the solver does decide that:
;   (assert (forall ((i A)) (= (= i a0) (not (= i a1)))))      answers sat
; so the rewrite is exact and buys the answer the direct form loses.
;
; cvc5 cannot read this file at all -- `lambda` is a Z3 extension, not SMT-LIB --
; so there is no cross-check here, only the negation and the quantified form.
(set-logic ALL)
(declare-datatypes ((A 0)) (((a0) (a1))))
(assert (= (lambda ((x A)) (= x a0)) (lambda ((y A)) (not (= y a1)))))
(check-sat)
