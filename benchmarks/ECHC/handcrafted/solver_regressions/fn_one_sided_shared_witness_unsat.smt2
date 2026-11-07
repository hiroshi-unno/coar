; Expected: unsat.  The smallest input on which the one-sided functional-predicate elimination
; rule both APPLIES and needs its first condition, so that condition is visible as a verdict
; rather than only as a trace line.
;
; THE SHAPE.  `q` is introduced by a head existential, which skolemisation turns into a witness
; represented as a FUNCTIONAL predicate: a solution must give, for every argument tuple, exactly
; one result.  Everywhere else `q` occurs negatively and exactly once per clause, its arguments
; are distinct variables, and no clause's remaining part mentions any unknown.  Those are the
; rule's conditions, and they all hold here, which is what makes this the positive case.
;
; THE RULE.  Where every clause mentioning such a `q` has the form
;
;     forall x y.  q(x,y) /\ B_i(x,y) => H_i(x,y)        for i = 1..k
;
; the k clauses may be replaced by the SINGLE constraint
;
;     forall x. exists y. AND_i ( B_i(x,y) => H_i(x,y) )
;
; and `q` removed.  Forward: totality gives some y0 with q(x,y0), and every clause instantiated
; there yields its implication, so y0 witnesses the conjunction.  Backward: choose a y per x and
; let `q` be the graph of that choice, which is total and single-valued by construction.
;
; WHY THE WITNESS MUST BE SHARED, AND WHY THIS FILE EXISTS.  The conjunction is inside ONE
; existential because `q` has ONE value at each x.  Replacing each clause separately by
; `forall x. exists y. (B_i => H_i)` permits a different y per clause, which no single functional
; `q` need realise -- and on this input the difference is the answer.  Shared, the constraint is
; `exists r. r > 0 /\ r < 0`, which no r satisfies, so the system is unsatisfiable.  Split, the
; two constraints are `exists r. r > 0` and `exists r. r < 0`, both satisfiable, and the system
; would be reported satisfiable.  So an implementation that takes the unsound reading answers
; `sat` here where the answer is `unsat`, and no trace has to be read to see it.
;
; The argument for `unsat` needs no solver: the first assertion demands some r with q(0,r), the
; second forces r > 0 and the third forces r < 0.
;
; SCOPE.  This is an ordinary existentially quantified constrained Horn clause problem -- no
; dependency set, no quantified sort -- and it sits in this corpus rather than beside the two
; imported E-CHC files because the rule it exercises belongs to this class: the functional
; predicate the head existential skolemises into is what this class is named for, and an
; existentially quantified CHC is the special case where the witness may depend on every
; universal of its clause.
;
; The elimination is off by default and is reached through the preprocessor's own switch, so a
; run of this file under a shipped configuration does not exercise the rule at all; it answers
; `unsat` either way, by the argument above.
(set-logic HORN)
(declare-fun q (Int Int) Bool)

(assert (forall ((m Int)) (exists ((r Int)) (q m r))))
(assert (forall ((m Int) (r Int)) (=> (q m r) (> r 0))))
(assert (forall ((m Int) (r Int)) (=> (q m r) (< r 0))))
(check-sat)
