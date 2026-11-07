; P is functional from an integer to an option: the witness some(x + 1) is a
; constructor applied to an affine term of the argument, which no datatype
; template candidate expresses: sat.
(set-logic HORN)
(declare-datatypes ((Opt 0)) (((none) (some (val Int)))))
(declare-fnp P (Int Opt) Bool)
(assert (forall ((x Int) (o Opt)) (=> (P x o) (and ((_ is some) o) (= (val o) (+ x 1))))))
(check-sat)
