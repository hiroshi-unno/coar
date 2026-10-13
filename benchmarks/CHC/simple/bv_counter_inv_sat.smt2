; A bit-vector CHC: a counter bounded by 10, over (_ BitVec 8).  Expected: sat.
; The smallest tracked input that takes the CHC path with bit-vector arguments end to end
; (`-p chc` under mucyc.json and pcsat_tbq_ar.json both answer sat).  Added 2026-09-08 because
; the bit-vector model-based projection merged that day has no tracked input at all: its corpus
; is the benchmarks/hwmcc_to_chc submodule, which is not checked out by default.  Note that
; this file does *not* exercise that projection -- MuCyc solves it without needing one.
(set-logic HORN)
(declare-fun inv ((_ BitVec 8)) Bool)
(assert (forall ((x (_ BitVec 8))) (=> (= x (_ bv0 8)) (inv x))))
(assert (forall ((x (_ BitVec 8))) (=> (and (inv x) (bvult x (_ bv10 8))) (inv (bvadd x (_ bv1 8))))))
(assert (forall ((x (_ BitVec 8))) (=> (inv x) (bvule x (_ bv10 8)))))
(check-sat)
