; A monomorphic datatype beside a recursive integer definition.  The problem
; builder adds a size function for Pair to the function environment as
; vocabulary; no clause applies it, so the SMT-LIB2 printer must neither refuse
; the input for it nor print it, while the user definition dbl is printed and
; read back.  Expected: sat (P x := x >= 0).
(set-logic HORN)
(declare-datatypes ((Pair 0)) (((pair (fst Int) (snd Int)))))
(define-fun-rec dbl ((x Int)) Int (+ x x))
(declare-fun P (Int) Bool)
(assert (forall ((p Pair)) (=> (and (= p (pair 1 2)) (>= (fst p) 0)) (P (dbl (fst p))))))
(assert (forall ((x Int)) (=> (and (P x) (< x 0)) false)))
(check-sat)
