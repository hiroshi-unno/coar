; Every bit-vector has an additive inverse: forall x. exists y. x + y = 0.
; The quantifier elimination goes through the bit-vector projection's equality
; rule (an odd coefficient on the eliminated variable, so the equation can be
; solved for it modulo 2^8).  Note that Z3 4.x does not terminate on this file;
; cvc5 answers sat.
(set-logic BV)
(assert (forall ((x (_ BitVec 8))) (exists ((y (_ BitVec 8))) (= (bvadd x y) (_ bv0 8)))))
(check-sat)
