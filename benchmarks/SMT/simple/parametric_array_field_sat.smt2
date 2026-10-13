; Parametric datatypes: the parameter instantiation must reach inside a compound selector
; range (an array or sequence field).
(declare-datatypes ((Box 1)) ((par (T) ((box (contents (Array Bool T)))))))
(declare-const x0 (Box Int))
(declare-const x1 (Box Int))
(declare-const x2 (Box Int))
(assert (distinct (select (contents x0) true) (select (contents x1) true) (select (contents x2) true)))
(check-sat)
