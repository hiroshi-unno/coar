; An input that declares a datatype named option with three constructors, none of them the
; None/Some of OCaml's predefined option type, which the tool knows in every process.  The
; file's declaration must win: P holds of every value built by other, so P (other 1) holds and
; the query clause fails.
(set-logic HORN)
(declare-datatypes ((option 0)) (((nothing) (just (get Int)) (other (oth Int)))))
(declare-fun P (option) Bool)
(assert (forall ((o option)) (=> (and (not ((_ is nothing) o)) (not ((_ is just) o))) (P o))))
(assert (forall ((o option)) (=> (and (P o) (= o (other 1))) false)))
(check-sat)
