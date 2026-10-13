; expected: sat
;
; ANSWERED `sat,5` SINCE 2026-09-19, and it took three repairs to get there, so
; the file is kept as the smallest statement of what each one was for. It is
; satisfiable for a reason that takes one line: `Inv(s0, s, n) := s0 <= s`
; satisfies all three clauses, and the conclusion's obligation asks only for
; SOME sequence of length `s - s0`, which exists for every `s >= s0`.
;
; What stopped it, in the order the blockers came off. The qualifier eliminator
; was asked to remove the existential and did not return, so the CEGIS loop
; never started -- and the guard meant to prevent that read the FREE variables,
; where a quantified one is not, so it had never fired. With the loop running,
; the correct invariant was proposed and rejected on every iteration, because
; the validation query is one no solver in reach decides and an undecided
; validation used to be answered with a vacuous counterexample: non-empty, so
; the candidate is rejected, and saying nothing, so the next round asks the same
; question. And the query did not have to be that shape at all: the body reads
; the bound sequence only through its length, and for a non-empty element sort
; every non-negative length is realised, so the quantifier is arithmetic.
;
; The pair this belongs to isolates the cause to one ingredient. Its twin
; `seq_exists_obligation_witnessed_sat.smt2` is the same problem with the
; existential discharged -- the sequence named as a universally quantified
; premise instead of quantified in the conclusion -- and answers `sat,0`. The
; two differ in nothing else. So what stops this file is a SEQUENCE QUANTIFIED
; IN THE CONCLUSION, not the sequence operations: this file does not even use
; `seq.nth`, only `seq.len`, and its twin that does use `seq.nth` answers.
;
; It came out of reducing a contributed Creusot `Skip` benchmark whose exit
; obligation has the same shape, and it is the smallest form of what stops that
; file. Ten lines.
(set-logic HORN)
(define-fun produces ((s0 Int) (visited (Seq Int)) (s1 Int)) Bool
  (and (<= s0 s1) (= (seq.len visited) (- s1 s0))))
(declare-fun Inv (Int Int Int) Bool)
(assert (forall ((s Int) (n Int)) (=> (>= n 0) (Inv s s n))))
(assert (forall ((s0 Int) (s Int) (n Int))
  (=> (and (Inv s0 s n) (> n 0)) (Inv s0 (+ s 1) (- n 1)))))
(assert (forall ((s0 Int) (s Int) (n Int))
  (=> (and (Inv s0 s n) (= n 0)) (exists ((v (Seq Int))) (produces s0 v s)))))
(check-sat)
