; An input that declares a parametric datatype named list, with the constructors nil and
; cons; OCaml's predefined list type, which the tool knows in every process, has the same
; name and the constructors [] and ::.  The file's declaration must win.  Len is the length,
; which is never negative.
(set-logic HORN)
(declare-datatypes ((list 1)) ((par (T) ((nil) (cons (hd T) (tl (list T)))))))
(declare-fun Len ((list Int) Int) Bool)
(assert (Len (as nil (list Int)) 0))
(assert (forall ((h Int) (t (list Int)) (n Int)) (=> (Len t n) (Len (cons h t) (+ n 1)))))
(assert (forall ((l (list Int)) (n Int)) (=> (and (Len l n) (< n 0)) false)))
(check-sat)
