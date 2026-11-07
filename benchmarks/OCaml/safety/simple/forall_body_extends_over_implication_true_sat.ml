(* The companion of forall_body_extends_over_implication_false_unsat.ml:
   [_forall k:int. k = n => v > n] is [v > n], which holds for [v = n + 1]. *)
let f n = n + 1

[@@@assert "typeof(f) <: (n:int) -> {v:int | _forall k:int. k = n => v > n}"]
