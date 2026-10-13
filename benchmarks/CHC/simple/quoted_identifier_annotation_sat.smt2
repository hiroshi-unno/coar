; expected: sat
;
; Two distinct predicates, one of them a quoted identifier whose text happens to
; contain the annotation opener this backend strips from the printed problem. The
; input is satisfiable and z3, native hoice and the SPACER backend agree.
;
; The Hoice wrapper corrupted it: after printing the problem it removed `(! ` and
; ` :weight ...)` from every line, including the inside of a |quoted identifier|,
; so |P(! X| became |PX| -- the same symbol as the unquoted PX declared beside it
; -- and the external solver refused the file for a duplicate declaration. A
; control containing only the quoted predicate answers sat either way, because
; renaming one isolated symbol consistently is invisible.
(set-logic HORN)
(declare-fun |P(! X| (Int) Bool)
(declare-fun PX (Int) Bool)
(assert (|P(! X| 0))
(assert (not (PX 0)))
(check-sat)
