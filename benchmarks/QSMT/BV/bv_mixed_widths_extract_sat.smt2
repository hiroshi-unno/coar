; Two different widths in one prefix, related by extract.  Widths need not
; agree across a bit-vector prefix: the projection reads each variable's width
; off the atoms that mention it rather than off the prefix, so 4- and 8-bit
; variables coexist.
(set-logic BV)
(assert (forall ((x (_ BitVec 4))) (exists ((y (_ BitVec 8))) (= ((_ extract 3 0) y) x))))
(check-sat)
