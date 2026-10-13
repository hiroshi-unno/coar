; A model exists, but the equation does not determine the Boolean table.
(set-logic HORN)
(define-fun-rec b ((x Bool)) Bool (b x))
(assert (not (b false)))
(check-sat)
