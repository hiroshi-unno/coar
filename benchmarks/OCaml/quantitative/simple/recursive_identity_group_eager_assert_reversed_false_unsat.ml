(* The eager sibling assertion is false; its constraint must remain global. *)
[@@@mode "hfl_prop_as_expectation"]
let identity f = f
let rec zero n k = zero n k
let other = (fun () -> assert false; zero) () and marker = (fun x -> x + 1) 0 and b = identity zero
let run n = b n (fun _ -> 0.0)
[@@@assert "typeof(run) <: int -> { ret : prop | ret <= 1.0 }"]
