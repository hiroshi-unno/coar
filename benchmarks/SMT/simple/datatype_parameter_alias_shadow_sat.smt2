; Expected: sat. The datatype's local parameter T is instantiated at Int.
; The unrelated Bool alias T must not override the datatype parameter.
(define-sort T () Bool)
(declare-datatypes ((Box 1)) ((par (T) ((box (value T))))))
(declare-const b (Box Int))
(assert (= (value b) 1))
(check-sat)
