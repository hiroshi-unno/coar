; A satisfiable negation whose model z3 does not find until one sequence length is fixed.
; Provenance: the negation of the client clause (clause [6] after preprocessing, zero unknowns
; left) of an unsatisfiable constraint problem the Thrust frontend emitted for a Rust program
; calling a FnMut closure over a range, transcribed by hand from the solver's trace with the file's
; datatypes (2026-10-02). sat = the clause is invalid = the refutation of that file.
; Its quantifier-free part forces len x4 = len x1 = 10 and len x0 = 11 by linear arithmetic.
; Checked here: Z3 5.1.0 (z3 -T:30) answers timeout as it stands, and sat in under a second with
; (assert (= (seq.len x4) 10)) added. The reproducer of the model-read length pin of the
; zero-unknown verdict (pin_seq_lengths_from_model_no_unknown_query).
(declare-datatypes ((A1 0)) (((tuple2 (p0 Int) (p1 Int)))))
(declare-datatypes ((A3 0)) (((tuple))))
(declare-datatypes ((A4 0)) (((tupleA4 (q0 A1) (q1 A3)))))
(declare-fun x0 () (Seq A3)) (declare-fun x1 () (Seq Int)) (declare-fun x2 () A4) (declare-fun x3 () Int)
(declare-fun x4 () (Seq Int)) (declare-fun x5 () A4)
(assert (not (or (distinct (q1 x2) tuple) (distinct (q1 x2) (q1 x5)) (distinct (q0 x2) (q0 x5))
  (distinct (seq.nth x0 (seq.len x4)) (q1 x2)) (distinct (seq.nth x0 0) tuple)
  (= 0 (- (+ 1 (* 10 x3)) (seq.nth x4 x3)))
  (distinct 0 (- (+ -1 (seq.len x0)) (seq.len x4)))
  (distinct 0 (- (p0 (q0 x2)) (seq.len x1)))
  (distinct 0 (- (seq.len x1) (seq.len x4)))
  (<= 0 (- -1 (seq.len x1))) (<= 0 (- -1 x3)) (<= 0 (- x3 (seq.len x4)))
  (<= 0 (+ -1 (- (p1 (q0 x2)) (p0 (q0 x2)))))
  (distinct 0 (+ -10 (p1 (q0 x2))))
  (exists ((i Int)) (and (<= 0 (- (- -1 i) (- (seq.len x4)))) (>= i 0) (or (distinct (seq.nth x0 i) tuple) (distinct 0 (+ (seq.nth x4 i) (* -10 (seq.nth x1 i)))))))
  (exists ((i Int)) (and (distinct 0 (+ (- (seq.len x1) i) (seq.nth x1 i) (- (p0 (q0 x2))))) (<= 0 (+ -1 (- i) (seq.len x1))) (>= i 0)))
  (and (<= 0 (+ -1 (p0 (q0 x2)) (- (p1 (q0 x2))))) (<= 0 (+ -1 (seq.len x1)))))))
(check-sat)
