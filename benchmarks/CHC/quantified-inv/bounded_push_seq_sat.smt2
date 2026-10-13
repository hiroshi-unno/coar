; bounded_prefix_sat.smt2 in the form a sequence is usually built in, by appending: the loop
; pushes an element no larger than bound, and the query reads any position below the length.
; There is no index variable, so the invariant is the guarded universal alone.
; sat: I(s, bound) = forall j. 0 <= j < seq.len s -> seq.nth s j <= bound satisfies all three
; clauses in every model: the reads of s ++ [x] below its length are reads of s or x itself.
(set-logic HORN)
(declare-fun I ((Seq Int) Int) Bool)
(assert (forall ((x Int) (bound Int))
                (=> (<= x bound) (I (seq.unit x) bound))))
(assert (forall ((s (Seq Int)) (x Int) (bound Int))
                (=> (and (I s bound) (<= x bound)) (I (seq.++ s (seq.unit x)) bound))))
(assert (forall ((s (Seq Int)) (j Int) (bound Int))
                (=> (and (I s bound) (<= 0 j) (< j (seq.len s)) (> (seq.nth s j) bound)) false)))
(check-sat)
