[@@@mode "hfl_prop_as_liberal_probability"]

(* The loop of liberal_probability_geometric_lower_bound_valid.ml, whose
   probability of not failing is exactly 1/2, with the false lower bound 3/4:
   no admissible lower bound of the recursive result implies it, so the
   assertion is not typable.  Untypable is not refuted: the mode answers
   unknown, never invalid. *)
let rec loop k = 0.25 *. 0.0 +. 0.25 *. k () +. 0.5 *. loop k

[@@@assert "typeof(loop) <: (unit -> { r : prop | r = 1.0 }) -> { ret : prop | ret >= 0.75 }"]
