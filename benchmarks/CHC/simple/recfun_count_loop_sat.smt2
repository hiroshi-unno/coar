; A loop counting the non-zero entries of a sequence against a recursive count (`define-fun-rec`).
; Satisfiable: inv(s, i, c) := c = cnt s i /\ 0 <= i <= seq.len s (checked: given as a define-fun it
; answers sat,0, and with c = 1 + cnt s i it answers unsat,0). Pinned because the graph resolver once
; substituted a Z3 model's entry for `cnt` (a dummy function) into the examples it derived and
; answered a wrong unsat,5 here; the tool does not find the invariant
; yet, so the smoke set asserts only that the wrong unsat does not come back. Hand-made 2026-10-02
; from a constraint problem the Thrust frontend emitted for a Rust loop counting with a recursive
; function, with declare-dep-exists-fun spelled as declare-fun.
(set-logic HORN)
(define-fun-rec cnt ((s (Seq Int)) (k Int)) Int
  (ite (<= k 0) 0 (+ (cnt s (- k 1)) (ite (= (seq.nth s (- k 1)) 0) 0 1))))
(declare-fun inv ((Seq Int) Int Int) Bool)
(assert (forall ((s (Seq Int))) (inv s 0 0)))
(assert (forall ((s (Seq Int)) (i Int) (c Int))
  (=> (and (inv s i c) (< i (seq.len s))) (inv s (+ i 1) (+ c (ite (= (seq.nth s i) 0) 0 1))))))
(assert (forall ((s (Seq Int)) (i Int) (c Int))
  (=> (and (inv s i c) (>= i (seq.len s))) (= c (cnt s (seq.len s))))))
(check-sat)
