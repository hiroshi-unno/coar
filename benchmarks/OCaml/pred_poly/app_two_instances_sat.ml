(* A higher-order function used at two instances.  [app] applies the function
   it is given once; what that function guarantees about its result is the
   predicate [app] is polymorphic in.  Checked once for every such predicate,
   [app] promises exactly what the function promises; the two uses instantiate
   it with "adds one" and "adds two", and each use needs its own instance to
   prove its bound.
   expected: sat *)
let app (f : int -> int) (x : int) = f x

let main u =
  let a = app (fun z -> z + 1) u in
  let b = app (fun z -> z + 2) u in
  assert (a > u && b > u + 1)

[@@@assert "typeof(main) <: int -> unit"]
