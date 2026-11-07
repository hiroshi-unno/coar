(* check is safe only on positive arguments, and it reaches them through a
   higher-order application guarded by n > 0: a typing must refine both
   check's and app's arguments. *)
let app g x = g x
let check y = assert (y > 0)
let main n = if n > 0 then app check n else ()
[@@@assert "typeof(main) <: int -> unit"]
