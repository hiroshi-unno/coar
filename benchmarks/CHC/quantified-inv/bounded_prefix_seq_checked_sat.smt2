; bounded_prefix_seq_sat.smt2 with the query's read bounds-checked, (< j (seq.len s)), as a
; front end translating an indexing operation that panics out of range writes it.  Its
; solution needs no fact about i and the length, which bounded_prefix_seq_sat's does
; (i < seq.len s, since an unchecked read past the end is a value no model agrees on).
; sat: I(s, i, bound) = forall j. 0 <= j < seq.len s -> (j > i \/ seq.nth s j <= bound)
; satisfies all three clauses in every model (every read it makes is in range).
(set-logic HORN)
(declare-fun I ((Seq Int) Int Int) Bool)
(assert (forall ((s (Seq Int)) (bound Int))
                (=> (and (< 0 (seq.len s)) (<= (seq.nth s 0) bound)) (I s 0 bound))))
(assert (forall ((s (Seq Int)) (i Int) (bound Int))
                (=> (and (I s i bound) (<= 0 i) (< (+ i 1) (seq.len s))
                         (<= (seq.nth s (+ i 1)) bound))
                    (I s (+ i 1) bound))))
(assert (forall ((s (Seq Int)) (i Int) (j Int) (bound Int))
                (=> (and (<= 0 j) (<= j i) (< j (seq.len s)) (I s i bound)
                         (> (seq.nth s j) bound))
                    false)))
(check-sat)
