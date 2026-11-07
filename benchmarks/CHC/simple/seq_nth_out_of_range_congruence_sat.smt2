; expected: sat
;
; An open read is still a FUNCTION of its sequence and index: two reads at
; the same index of equal sequences are equal in every model.  This is the
; safe direction of the two files beside it -- abstracting each open read by
; an independent fresh value would lose the answer here -- and it pins that
; reads of syntactically different but equal sequences at one index are not
; given independent values.
(set-logic HORN)
(assert (forall ((a Int) (b Int))
  (=> (= a b)
      (= (seq.nth (seq.++ (seq.unit a) (seq.unit 1)) 5)
         (seq.nth (seq.++ (seq.unit b) (seq.unit 1)) 5)))))
(check-sat)
