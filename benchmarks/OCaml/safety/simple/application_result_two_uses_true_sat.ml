(* A function value computed by an application, used at two different continuations in one later item. *)
let identity f = f
let apply_one = identity (fun g -> g 1)
let main () = apply_one (fun x -> x + 1) + apply_one (fun x -> x + 2)
[@@@assert "typeof(main) <: unit -> {z: int | z = 5}"]
