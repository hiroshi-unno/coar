; Z3 answers `unsat` to this SATISFIABLE formula (found 2026-11-05 behind a wrong `sat` of this
; tool on a Rust-derived CHC problem): every one of A..E empty satisfies it, since each tail
; (t x) = (seq.extract (x ++ [u]) 1 (seq.len x)) is then empty.  The same assertions with those
; values substituted are answered `sat` by the same solver, cvc5 1.4.2 answers `sat`, and the
; same formula over (Seq Int) with u an integer is answered `sat`; the element sort being a
; sequence is what matters.  Seen with z3 4.12.0, 5.1.0 (the library this tool links), 5.3.3 and
; the 5.3.4 nightly of 2026-11-02; under `(check-sat)` and `(check-sat-using smt)` alike.
; The workaround in the tree: a native `unsat` on a question over sequences of sequences is read
; as `unknown` unless cvc5 proves it too (Z3interface.certify_shared_native_result).
(set-logic ALL)
(declare-fun A () (Seq (Seq Int)))
(declare-fun B () (Seq (Seq Int)))
(declare-fun C () (Seq (Seq Int)))
(declare-fun D () (Seq (Seq Int)))
(declare-fun E () (Seq (Seq Int)))
(define-fun u () (Seq Int) (seq.++ (seq.unit 1) (seq.unit 2)))
(define-fun t ((x (Seq (Seq Int)))) (Seq (Seq Int)) (seq.extract (seq.++ x (seq.unit u)) 1 (seq.len x)))
(assert (= (t A) (t B)))
(assert (or (<= (seq.len B) 0) (= (seq.nth B 0) u)))
(assert (or (<= (seq.len E) 0) (= (seq.nth E 0) u)))
(assert (= (t C) (t E)))
(assert (<= (seq.len D) 0))
(assert (= (t A) (t D)))
(assert (= (t C) (t D)))
(check-sat)
