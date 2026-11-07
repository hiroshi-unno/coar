; expected: unsat
;
; Five sequences of integer sequences A, B, C, D, E.  Write [t x] for the tail
; (seq.extract (x ++ [u]) 1 (seq.len x)) of x ++ [u], with u = [1, 2].  When
; every one of them is empty, every tail is empty, so the premise of the goal
; below holds -- the equalities between tails, [len D <= 0], and the two
; disjunctions [len x <= 0 \/ seq.nth x 0 = u] -- and the goal demands [false]
; there.  [P] is forced at every argument by the fact, so no interpretation of
; [P] helps: no solution exists, and the answer is `unsat`.
;
; What the file pins: the goal's premise is satisfiable, yet Z3's sequence
; theory (4.12.0 to the 5.3.4 nightly of 2026-11-02, on its incremental and
; [smt] paths) answers [unsat] to it when the elements are themselves
; sequences, while the same premise over sequences of integers is answered
; [sat].  A solver that reads that [unsat] as a proof that the goal clause is
; valid drops the clause and answers `sat`.  The answer must never be `sat`.
(set-logic HORN)
(declare-fun P ((Seq (Seq Int))) Bool)
(define-fun u () (Seq Int) (seq.++ (seq.unit 1) (seq.unit 2)))
(define-fun t ((x (Seq (Seq Int)))) (Seq (Seq Int))
  (seq.extract (seq.++ x (seq.unit u)) 1 (seq.len x)))
(assert (forall ((x (Seq (Seq Int)))) (P x)))
(assert (forall ((A (Seq (Seq Int))) (B (Seq (Seq Int))) (C (Seq (Seq Int)))
                 (D (Seq (Seq Int))) (E (Seq (Seq Int))))
  (=> (and (P A) (P B) (P C) (P D) (P E)
           (= (t A) (t B))
           (or (<= (seq.len B) 0) (= (seq.nth B 0) u))
           (or (<= (seq.len E) 0) (= (seq.nth E 0) u))
           (= (t C) (t E))
           (<= (seq.len D) 0)
           (= (t A) (t D))
           (= (t C) (t D)))
      false)))
(check-sat)
