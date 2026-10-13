; expected: sat
; The printer must preserve a symbol containing its former query-helper name.
(set-logic HORN)
(declare-fun P__query__Q () Bool)
(declare-fun PfalseQ () Bool)
(assert P__query__Q)
(assert (not PfalseQ))
(check-sat)
