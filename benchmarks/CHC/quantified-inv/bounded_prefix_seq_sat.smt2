; The sequence twin of bounded_prefix_sat.smt2: the array a becomes a sequence s, a read
; (select a j) becomes (seq.nth s j), and the length the array lacked is (seq.len s), which every
; read is kept inside, since seq.nth out of range is a term the theory leaves open.
; sat: I(s, i, bound) = 0 <= i < seq.len s /\ forall j. 0 <= j <= i -> seq.nth s j <= bound
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
                (=> (and (<= 0 j) (<= j i) (I s i bound) (> (seq.nth s j) bound)) false)))
(check-sat)
