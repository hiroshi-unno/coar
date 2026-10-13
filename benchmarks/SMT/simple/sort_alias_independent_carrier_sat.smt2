; Expected: sat, including after reading sort_alias_seed_sat.smt2.
; A fresh uninterpreted sort can have three elements; Bool cannot.
(declare-sort ScopeAlias 0)
(declare-const scope_x ScopeAlias)
(declare-const scope_y ScopeAlias)
(declare-const scope_z ScopeAlias)
(assert (distinct scope_x scope_y scope_z))
(check-sat)
