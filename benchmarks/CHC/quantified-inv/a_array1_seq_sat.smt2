; The sequence twin of a_array1.smt2: the array a becomes a sequence s, (select a j) becomes
; (seq.nth s j), and every read is kept below (seq.len s), since seq.nth out of range is a term
; the theory leaves open.
; sat: I(s, i) = 0 <= i < seq.len s /\ forall j. 0 <= j <= i -> seq.nth s j = 0 satisfies all
; three clauses in every model (every read it makes is in range).
(set-logic HORN)
(declare-fun I ((Seq Int) Int) Bool)
(assert (forall ((s (Seq Int)))
                (=> (and (< 0 (seq.len s)) (= (seq.nth s 0) 0)) (I s 0))))
(assert (forall ((s (Seq Int)) (i Int))
                (=> (and (>= i 0) (I s i) (< (+ i 1) (seq.len s)) (= (seq.nth s (+ i 1)) 0))
                    (I s (+ i 1)))))
(assert (forall ((s (Seq Int)) (i Int) (j Int))
                (=> (and (<= 0 j) (<= j i) (I s i) (< (seq.nth s j) 0)) false)))
(check-sat)
