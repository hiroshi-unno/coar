; Expected: unsat, and the reason involves a predicate.  A solution must satisfy the constraints
; whatever the background theory left open, and the theory does not fix (mytl mynil).
;
;   P 0 must be false, by the second clause.
;   Then the first clause is violated in the model where (mytl mynil) = mynil.
;   So no P works: unsat.
;
; Deciding instead by "is there SOME model satisfying everything" answers sat -- choose a model
; with (mytl mynil) /= mynil and take P := false.  That is what Z3 answers as an SMT solver on the
; assertions of this file once the set-logic line is removed; its Horn engine on the file as it
; stands answers unknown, and the gspacer wrapper prints nothing at all.  The two
; readings differ on exactly this shape, which is why the file is kept.
;
; Note that preprocessing eliminates P here, so the verdict comes from the no-unknown site and
; not from synthesis; the companion file with four copies of each clause keeps P alive.
(set-logic HORN)
(declare-datatypes ((Lst 0)) (((mynil) (mycons (myhd Int) (mytl Lst)))))
(declare-fun P (Int) Bool)
(assert (=> (= (mytl mynil) mynil) (P 0)))
(assert (=> (P 0) false))
(check-sat)
