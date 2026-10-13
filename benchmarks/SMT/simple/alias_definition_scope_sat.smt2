; Expected: sat. A free sort name in an alias keeps its definition-site meaning.
; Captured refers to the Bool alias T, not Box's later local parameter T.
(define-sort T () Bool)
(define-sort Captured () T)
(declare-datatypes ((Box 1)) ((par (T) ((box (value Captured))))))
(declare-const b (Box Int))
(assert (= (value b) true))
(check-sat)
