; expected: refused ("synthesis restricted by a grammar is not implemented")
;
; The same refusal, for the grammar shape that used to produce the misleading
; message: the production names the synthesis parameter `z`, which went to the
; operator table and failed as an unknown operator. cvc5 solves this one with
; f(z) = z, so the file is a reminder of what a grammar-aware synthesizer would
; have to accept first -- the identifier leaves, which is where the reader still
; has no case.
(set-logic LIA)
(synth-fun f ((z Int)) Int
  ((Start Int))
  ((Start Int (z))))
(constraint (= (f 1) 1))
(check-synth)
