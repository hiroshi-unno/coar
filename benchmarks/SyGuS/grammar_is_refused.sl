; expected: refused ("synthesis restricted by a grammar is not implemented")
;
; This is not a verdict file. The grammar admits exactly the term 0, so no
; solution satisfies f(0) = 1 and cvc5 reports the synthesis as failed. This tool
; answered sat: the grammar was parsed and then dropped -- the conversion to a
; constraint problem keeps only the function's sort -- so what was solved was the
; unrestricted problem and its answer was reported as the answer to this one.
;
; Honouring a grammar is a feature of the synthesizer, so until it exists the
; problem is refused where the grammar is read. Reading it first gave the wrong
; complaint: a production naming a synthesis parameter or another nonterminal is
; sent to the operator table, and a file was rejected with "[term_of_op] z not
; supported", which reads as a fault in the grammar rather than as a missing
; feature.
;
; No file in this repository's SyGuS corpus carries a grammar (0 of 2,661), so
; the refusal costs nothing that used to be answered.
(set-logic LIA)
(synth-fun f ((z Int)) Int
  ((Start Int))
  ((Start Int (0))))
(constraint (= (f 0) 1))
(check-synth)
