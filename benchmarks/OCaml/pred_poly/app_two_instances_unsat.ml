(* The twin of app_two_instances_sat.ml: the second use adds two, which is
   not above [u + 2].
   expected: unsat *)
let app (f : int -> int) (x : int) = f x

let main u =
  let a = app (fun z -> z + 1) u in
  let b = app (fun z -> z + 2) u in
  assert (a > u && b > u + 2)

[@@@assert "typeof(main) <: int -> unit"]
