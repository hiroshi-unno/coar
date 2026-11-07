(* As application_result_two_uses_true_sat, with the function bound syntactically: the control that answers. *)
let apply_one g = g 1
let main () = apply_one (fun x -> x + 1) + apply_one (fun x -> x + 2)
[@@@assert "typeof(main) <: unit -> {z: int | z = 5}"]
