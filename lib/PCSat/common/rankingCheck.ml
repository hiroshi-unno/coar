(* The linear ranking constructions live in the linear-arithmetic library,
   which does not depend on PCSat, so that other solvers can use them; this
   module keeps PCSat's name for them. *)
include Linarith.RankingCheck
