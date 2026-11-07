; A well-founded relation is irreflexive, including on Boolean values.
; The unused recursive definition still constrains the complete context.
(set-logic HORN)
(declare-wfp P (Bool Bool) Bool)
(define-fun-rec b ((x Bool)) Bool
  (xor (not (b x)) (not (P false false))))
(assert true)
(check-sat)
