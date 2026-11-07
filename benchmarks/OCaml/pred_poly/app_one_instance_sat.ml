(* A higher-order function checked once for every behaviour of its
   functional argument.  [app] applies the function it is given once, so the
   predicate it is polymorphic in is what that function guarantees about its
   result, and [app] promises exactly that.  The one use instantiates it with
   "adds one", which proves the bound.
   expected: sat *)
let app (f : int -> int) (x : int) = f x

let main u =
  let a = app (fun z -> z + 1) u in
  assert (a > u)

[@@@assert "typeof(main) <: int -> unit"]
