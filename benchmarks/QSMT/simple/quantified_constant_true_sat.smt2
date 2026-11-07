; A quantified formula whose body is the constant true: satisfiable.  About half of the
; weak-simulation formulas of Murphy and Kincaid's CAV 2024 evaluation have exactly this shape,
; and after simplification the whole assertion is the constant, with no arithmetic left in it.
; A solver that classifies its input by theory before solving must still accept it.
(set-logic LIA)
(assert (forall ((x Int) (y Int)) true))
(check-sat)
