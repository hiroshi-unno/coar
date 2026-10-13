(* Retain recursive-result provenance through deferred copies and
   the fresh return refinements of nonrecursive aliases. The least
   expectation of loop is zero; 1 <= ret is false and ret <= 1 is true. *)
[@@@mode "hfl_prop_as_expectation"]
let rec loop n k = loop n k
let b = loop
[@@@assert "typeof(b) <: int -> (int -> { r : prop | r = 0.0 }) -> { ret : prop | 1.0 <= ret }"]
