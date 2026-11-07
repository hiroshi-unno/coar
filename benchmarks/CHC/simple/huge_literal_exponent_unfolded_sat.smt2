; Expected: sat.
;
; The first clause's premise is false whatever the power is, so P may be
; empty and the system has a solution.
;
; Simplification raised out of the run instead: the integer power of two
; literals was folded by narrowing the exponent to a native integer, and
; 2^63 does not fit one.  Such a power is now left unfolded.
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (and (= x (^ 2 9223372036854775808)) false) (P x))))
(assert (forall ((x Int)) (=> (P x) false)))
(check-sat)
