; Every integer y has a quotient x by 2^32 (x = floor(y / 2^32)), so this is sat.
; MuStrat's integer strategy selects x := (y / 2^32) and substituting that term splits on
; the 2^32 residues of y; the split is to be declined with a message, not built.
(set-logic LIA)
(assert (forall ((y Int)) (exists ((x Int)) (and (<= (* 4294967296 x) y) (< y (+ (* 4294967296 x) 4294967296))))))
(check-sat)
