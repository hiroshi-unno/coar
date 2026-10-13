; expected: sat
;
; The control for the file beside this one, and the thing that makes the pair a
; pair. It is the same problem with the sequence named as a universally
; quantified PREMISE instead of quantified in the conclusion, and it answers
; `sat,0` -- while its twin, which quantifies the sequence in the conclusion,
; does not answer at all.
;
; It also carries the `seq.nth` conjunct its twin drops, so the pair rules that
; out as the cause: the file with `seq.nth` and no existential answers, and the
; file with an existential and no `seq.nth` does not.
(set-logic HORN)
(define-fun produces ((s0 Int) (visited (Seq Int)) (s1 Int)) Bool
  (and (<= s0 s1)
       (= (seq.len visited) (- s1 s0))
       (=> (> (seq.len visited) 0)
           (= (seq.nth visited (- (seq.len visited) 1)) (- s1 1)))))
(declare-fun Inv (Int Int Int) Bool)
(assert (forall ((s Int) (n Int)) (=> (>= n 0) (Inv s s n))))
(assert (forall ((s0 Int) (s Int) (n Int))
  (=> (and (Inv s0 s n) (> n 0)) (Inv s0 (+ s 1) (- n 1)))))
(assert (forall ((s0 Int) (s Int) (n Int) (v (Seq Int)))
  (=> (and (Inv s0 s n) (= n 0) (produces s0 v s)) (<= s0 s))))
(check-sat)
