; Z3 5.1.0 with its integer-blasting bit-vector solver (smt.bv.solver 2) answers
; unsat; the problem is sat (x = 112, i.e. xb = #x70, q = 0, y = 0), which the
; default solver and the check below agree on.  Found 2026-10-03 while
; choosing a solver for words split as 2^n * q + ubv_to_int xb.
(set-logic ALL)
(set-option :smt.bv.solver 2)
(declare-fun xb () (_ BitVec 8))
(declare-fun q () Int)
(declare-fun y () Int)
(define-fun x () Int (+ (* 256 q) (ubv_to_int xb)))
(assert (>= x 0))
(assert (< x 257))
(assert (>= y 0))
(assert (< y 256))
(assert (= (ubv_to_int (bvlshr xb #x04)) 7))
(assert (< (+ x y) 158))
(assert (= (ubv_to_int (bvand xb #x01)) 0))
(check-sat)
