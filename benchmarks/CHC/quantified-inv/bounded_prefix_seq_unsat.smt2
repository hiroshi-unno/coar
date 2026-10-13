; The sequence twin of bounded_prefix_sat.smt2 with the query reaching one position past the
; prefix the loop has checked: j <= i + 1 instead of j <= i (and j kept below seq.len s).
; unsat: s = [0, 1], bound = 0 gives I(s, 0, 0) by the first clause, and the query at i = 0,
; j = 1 then has seq.nth s 1 = 1 > 0; every read in that derivation is in range, so the
; refutation holds in every model.
(set-logic HORN)
(declare-fun I ((Seq Int) Int Int) Bool)
(assert (forall ((s (Seq Int)) (bound Int))
                (=> (and (< 0 (seq.len s)) (<= (seq.nth s 0) bound)) (I s 0 bound))))
(assert (forall ((s (Seq Int)) (i Int) (bound Int))
                (=> (and (I s i bound) (<= 0 i) (< (+ i 1) (seq.len s))
                         (<= (seq.nth s (+ i 1)) bound))
                    (I s (+ i 1) bound))))
(assert (forall ((s (Seq Int)) (i Int) (j Int) (bound Int))
                (=> (and (<= 0 j) (<= j (+ i 1)) (< j (seq.len s)) (I s i bound)
                         (> (seq.nth s j) bound))
                    false)))
(check-sat)
