; The input on which the two halves of the tool disagree with each other.  It does not answer:
; measured, 60 s and still running.  Z3 as an SMT solver says sat in milliseconds on the
; assertions of this file with the set-logic line removed -- the other reading of satisfiability;
; its Horn engine on the file as it stands answers unknown.
;
; (mytl mynil) is a selector on the wrong constructor, so the datatype theory does not fix its
; value: some models have (mytl mynil) = mynil and some do not.  Four copies of each clause keep
; P from being eliminated by resolution and argument erasure, so the synthesis path actually runs
; -- which is the whole point of this file, and what the one-clause version does not do.
;
;   exists-model reading (plain SMT-LIB satisfiability, what Z3 answers as an SMT solver): choose a model with
;     (mytl mynil) /= mynil, every first clause is vacuous, take P := false -> sat.
;   forall-model reading ("one P that works whatever the theory left open"): P must be false
;     everywhere by the second group, and then the first group is violated in the model where
;     (mytl mynil) = mynil -> no P survives -> unsat.  The name records this answer, because it
;     is the reading the validator enforces.
;
; What the tool does: the validator decides a candidate by VALIDITY -- it negates the clause and
; asks whether that is satisfiable -- so it rejects P := false because SOME model satisfies
; (mytl mynil) = mynil.  Traced, it asks exactly that question 2096 times in 25 s and never
; converges.  Preprocessing, on the other hand, decides an interpretation-dependent formula by
; the SATISFIABILITY of its universal closure, i.e. the other reading, which is why the
; single-clause variant of this file answers sat with zero validator queries.
(set-logic HORN)
(declare-datatypes ((Lst 0)) (((mynil) (mycons (myhd Int) (mytl Lst)))))
(declare-fun P (Int) Bool)
(assert (=> (= (mytl mynil) mynil) (P 0)))
(assert (=> (= (mytl mynil) mynil) (P 1)))
(assert (=> (= (mytl mynil) mynil) (P 2)))
(assert (=> (= (mytl mynil) mynil) (P 3)))
(assert (=> (P 0) false))
(assert (=> (P 1) false))
(assert (=> (P 2) false))
(assert (=> (P 3) false))
(check-sat)
