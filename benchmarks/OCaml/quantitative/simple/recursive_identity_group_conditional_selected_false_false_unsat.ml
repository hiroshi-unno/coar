(* Independent function sibling bounds remain in the enclosing assertion. *)
[@@@mode "hfl_prop_as_expectation"]

let identity f = f
let rec zero n k = zero n k

let b = identity zero
and keep = if true then (fun (x : int) -> assert false; x) else (fun (x : int) -> x)

let run n = b (keep n) (fun _ -> 0.0)

[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
