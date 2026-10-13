; Three results of a Bool-valued selector cannot be distinct in a genuine recursive group (the local
; parameter B is not the datatype B).
(set-logic ALL)
(declare-datatypes ((A 1) (C 1) (B 0))
 ((par (B) ((anil) (aw (value B) (ac (C B)))))
  (par (V) ((cnil) (cw (cb B))))
  ((bnil) (bw (ba (A Bool))))))
(declare-const x0 (A Bool))
(declare-const x1 (A Bool))
(declare-const x2 (A Bool))
(assert (distinct (value x0) (value x1) (value x2)))
(check-sat)
