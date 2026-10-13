; The other direction of the same rewrite: the existential over the array-carrying pair asks
; for a length that is both n and n+1, so the clause is not valid and the answer is unsat.
; Replacing the quantifier over the pair by quantifiers over its two fields must not lose
; this -- a decided verdict turning into "unknown" is a regression, and the twin of
; array_in_tuple_exists_sat.smt2 is what pins it.  Expected: unsat.
(set-logic HORN)
(declare-datatypes ((Pair 0)) (((mk (arr (Array Int Int)) (len Int)))))
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (> x 0) (P x))))
(assert (forall ((a (Array Int Int)) (n Int) (v Int) (y Int))
  (=> (and (P y) (= n 1) (= (select a 0) v))
      (exists ((p Pair)) (and (= (select (arr p) 0) v) (= (len p) n) (= (len p) (+ n 1)))))))
(check-sat)
