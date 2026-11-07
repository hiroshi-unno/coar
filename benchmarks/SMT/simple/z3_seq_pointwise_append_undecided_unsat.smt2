; unsat.  Z3 5.1.0 leaves this undecided (timeout at 10 s, its native sequence theory does not instantiate
; the pointwise quantifier at the appended position), while the same question asked with sequences as an
; uninterpreted sort plus axioms of length, read and concatenation is proved in about 0.01 s.  Appending
; one element to each of two equal-length sequences preserves a pointwise relation between them.  The
; reproducer of the sequence-axiom fallback (seq_axiom_fallback and its siblings).
(set-logic ALL)
(declare-sort It 0) (declare-sort B 0) (declare-fun post (It B) Bool)
(declare-const s1 (Seq It)) (declare-const s (Seq B)) (declare-const v It) (declare-const b B)
(assert (= (seq.len s1) (seq.len s)))
(assert (forall ((k Int)) (=> (and (<= 0 k) (< k (seq.len s))) (post (seq.nth s1 k) (seq.nth s k)))))
(assert (not (forall ((k Int)) (=> (and (<= 0 k) (< k (seq.len s))) (post (seq.nth (seq.++ s1 (seq.unit v)) k) (seq.nth (seq.++ s (seq.unit b)) k))))))
(check-sat)
