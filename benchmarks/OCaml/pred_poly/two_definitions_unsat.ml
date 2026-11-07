(* The twin of two_definitions_sat.ml: [app_succ (fun z -> z * 2) u] is
   [2 * u + 2], not [2 * u].
   expected: unsat *)
let app (f : int -> int) (x : int) = f x
let app_succ (g : int -> int) (x : int) = g (x + 1)

let main u =
  let a = app (fun z -> z + 1) u in
  let b = app_succ (fun z -> z * 2) u in
  assert (a > u && b = 2 * u)

[@@@assert "typeof(main) <: int -> unit"]
