; The witness for benchmarks/DQpCSP/handcrafted/e3_overlap_agreement_h_coupled_premise_sat.smt2,
; and with it the evidence that the judgement rule for agreement-without-communication needs its
; PRODUCT hypothesis and not merely disjoint dependency sets.
;
; The rule's proof says: agreement forces the two deciders' outputs to be one singleton {c} with
; c = f1(i, Q1) = f2(i, Q3); f1 cannot read Q3 and f2 cannot read Q1, so c depends only on the
; intersection of the two dependency sets; that is empty, so c is a constant, and the adversary
; removes it from the predicate the specification tests.  The middle step says f1 is CONSTANT ALONG
; THE Q3 AXIS, which is a claim about the space of admissible interpretations, not about a
; signature: it holds only when Q3 can be varied with Q1 held fixed.  A premise that ties the
; predicates together destroys exactly that, and then a decider reading only its own predicate may
; still know all of them.
;
; What is checked here.  Under a premise that adds "Q1 agrees with Q2 everywhere" and "Q3 agrees
; with Q2 everywhere" to the adjacency, the two deterministic choices
;
;   c1 = (ite (Q1 i) i (+ i 1))       c2 = (ite (Q3 i) i (+ i 1))
;
; always agree and are always usable.  Q1, Q2 and Q3 are left as free uninterpreted symbols, which
; is the universal reading: `unsat` here means the specification holds for EVERY interpretation
; satisfying the premise, so those two definitions solve the dependency-quantified problem and it is
; satisfiable -- while its sibling with the same (empty) intersection of dependency sets and a
; premise that mentions one predicate at a time is unsatisfiable.
;
; Deleting the two coupling conjuncts makes this file `sat`, i.e. the specification becomes
; falsifiable and the solution stops working.  That mutation is the check that this file can fail.
;
; expected: unsat
(set-logic UFLIA)
(declare-fun Q1 (Int) Bool)
(declare-fun Q2 (Int) Bool)
(declare-fun Q3 (Int) Bool)
(declare-fun i () Int)
(assert (forall ((h Int)) (or (Q2 h) (Q2 (+ h 1)))))
(assert (forall ((h Int)) (= (Q1 h) (Q2 h))))
(assert (forall ((h Int)) (= (Q3 h) (Q2 h))))
(define-fun c1 () Int (ite (Q1 i) i (+ i 1)))
(define-fun c2 () Int (ite (Q3 i) i (+ i 1)))
(assert (not (and (= c1 c2) (Q2 c1))))
(check-sat)
