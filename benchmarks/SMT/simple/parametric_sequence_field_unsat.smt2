; Parametric datatypes: the parameter instantiation must reach inside a compound selector
; range (an array or sequence field).
(declare-datatypes ((Box 1)) ((par (T) ((box (contents (Seq T)))))))
(declare-const x0 (Box Bool))
(declare-const x1 (Box Bool))
(declare-const x2 (Box Bool))
(assert (distinct (seq.nth (contents x0) 0) (seq.nth (contents x1) 0) (seq.nth (contents x2) 0)))
(check-sat)
