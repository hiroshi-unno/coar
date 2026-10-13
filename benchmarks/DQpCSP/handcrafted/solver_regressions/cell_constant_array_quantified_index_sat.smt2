; Expected: sat (sat,2 under pcsat_wopp_tbq_ar, 3 of 3).  The sampled cell expansion of an
; example atom widened the atom's sort list by one cell per array but appended no terms when
; the array offered no candidate cell: a constant array indexed by a quantified sort stores
; nothing and the atom's arguments reach no term of that sort.  The next array of the same
; atom was then expanded from an atom with 3 terms and 5 sorts, and the run ended with
; (Invalid_argument "length mismatch in zip_exn: 3 <> 5").  Two arrays are needed for the
; crash; preprocessing off is what lets the example reach the cell synthesizer with both.
; P := n >= 0 is a solution.
(set-logic DQHORN)
(declare-forall-sort a)
(declare-fun P ((Array a Bool) (Array a Bool) Int) Bool)
(assert (forall ((n Int)) (=> (= n 0) (P ((as const (Array a Bool)) false) ((as const (Array a Bool)) false) n))))
(assert (forall ((x (Array a Bool)) (y (Array a Bool)) (n Int)) (=> (P x y n) (P x y (+ n 1)))))
(assert (forall ((x (Array a Bool)) (y (Array a Bool)) (n Int)) (=> (and (P x y n) (< n 0)) false)))
(check-sat)
