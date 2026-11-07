; A mutually recursive parametric datatype used at two instances: each
; instance declares Tree and Forest in one declare-datatypes command, and
; Forest's constructors (fnil, fcons) and selectors exist once per instance.
; A printed form must keep the two instances' Forest constructors apart, not
; only Tree's.  Invariant: x is fnil exactly when y is.  expected: sat
(set-logic HORN)
(declare-datatypes ((Tree 1) (Forest 1))
  ((par (T) ((node (val T) (kids (Forest T)))))
   (par (T) ((fnil) (fcons (fhd (Tree T)) (ftl (Forest T)))))))
(declare-fun P ((Forest Int) (Forest Bool)) Bool)
(assert (P (as fnil (Forest Int)) (as fnil (Forest Bool))))
(assert (forall ((x (Forest Int)) (y (Forest Bool)))
  (=> (P x y) (P (fcons (node 1 x) x) (fcons (node true y) y)))))
(assert (forall ((x (Forest Int)) (y (Forest Bool)))
  (=> (and (P x y) ((_ is fcons) x) ((_ is fnil) y)) false)))
(check-sat)
