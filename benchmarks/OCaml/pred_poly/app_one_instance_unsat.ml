(* The twin of app_one_instance_sat.ml with a bound the instance does not
   give: [app (fun z -> z + 1) u] is [u + 1], which is not above [u + 1].
   expected: unsat *)
let app (f : int -> int) (x : int) = f x

let main u =
  let a = app (fun z -> z + 1) u in
  assert (a > u + 1)

[@@@assert "typeof(main) <: int -> unit"]
