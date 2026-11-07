(* Two higher-order functions, each checked once for every behaviour of its
   own functional argument: [app] applies it to its argument, [app_succ] to
   the successor of its argument.  Each definition's result depends on its
   own universal predicate only, so the two dependency sets are disjoint;
   the use instantiates each with its own function.
   expected: sat *)
let app (f : int -> int) (x : int) = f x
let app_succ (g : int -> int) (x : int) = g (x + 1)

let main u =
  let a = app (fun z -> z + 1) u in
  let b = app_succ (fun z -> z * 2) u in
  assert (a > u && b = 2 * u + 2)

[@@@assert "typeof(main) <: int -> unit"]
