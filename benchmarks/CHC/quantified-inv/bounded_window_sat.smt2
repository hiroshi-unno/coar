; The same shape as bounded_prefix_sat.smt2 with the quantified range moved off
; the origin: I(a, i, bound) = forall j. 10 <= j <= i -> a[j] <= bound.
;
; It exists as the falsifier for how the cell route chooses the indices it says
; something about.  Those candidates are read off the array a counterexample
; carries -- every index it stores, the two neighbours of each, and 0..5 -- so
; a witness inside the first few indices is found by accident.  Here every
; witness is at least 10 and a constant array stores nothing, so no candidate
; can be the witness and the body side of an example demands falsity only at
; cells where the invariant legitimately holds.  Solving this needs the index
; the clause names to travel with the example.
(set-logic HORN)
(declare-fun I ((Array Int Int) Int Int) Bool)
(assert (forall ((a (Array Int Int)) (bound Int))
                (=> (<= (select a 10) bound) (I a 10 bound))))
(assert (forall ((a (Array Int Int)) (i Int) (bound Int))
                (=> (and (I a i bound) (<= (select a (+ i 1)) bound))
                    (I a (+ i 1) bound))))
(assert (forall ((a (Array Int Int)) (i Int) (j Int) (bound Int))
                (=> (and (<= 10 j) (<= j i) (I a i bound) (> (select a j) bound)) false)))
(check-sat)
