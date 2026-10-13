; expected: sat
;
; The two predicates are independent, so the problem is satisfiable; z3, native
; hoice and this tool's SPACER backend all answer sat.
;
; The Hoice wrapper refused it with `[Map.add_exn] got key already present`. The
; export needs a helper predicate and had two fixed spellings for it, the second
; tried inside the handler of the first -- so an input that declares both, and
; both are legal SMT-LIB identifiers, ran out of candidates. Two names are not
; freshness. The helper is now lengthened until it is a name the problem does not
; hold.
(set-logic HORN)
(declare-fun __query__ (Int) Bool)
(declare-fun __query__hmm__ (Int) Bool)
(assert (__query__ 0))
(assert (not (__query__hmm__ 0)))
(check-sat)
