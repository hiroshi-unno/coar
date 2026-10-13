; Preprocessing eliminates the only predicate variable, so the verdict is decided by one
; validity query over the clause that is left.  That clause existentially quantifies a
; single-constructor datatype whose field is an array -- the shape a sequence is encoded as,
; an array of elements paired with a length.  Z3 instantiates a universal with ground terms
; the query already holds, and nothing here produces a value of that pair sort except the
; quantifier itself, so it answers "unknown (incomplete (theory array))" -- while the same
; question with the pair bound as its two fields is decided at once.
; Expected: sat (the witness is the pair built from a and n).
(set-logic HORN)
(declare-datatypes ((Pair 0)) (((mk (arr (Array Int Int)) (len Int)))))
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (> x 0) (P x))))
(assert (forall ((a (Array Int Int)) (n Int) (v Int) (y Int))
  (=> (and (P y) (= n 1) (= (select a 0) v))
      (exists ((p Pair)) (and (= (select (arr p) 0) v) (= (len p) n))))))
(check-sat)
