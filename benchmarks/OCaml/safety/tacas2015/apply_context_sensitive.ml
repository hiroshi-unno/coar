(* This program cannot be proven safe by verifiers (e.g., PPDP2009, PLDI2008)
   which are context-insensitive *)
let apply f x = f x
let f1 x = assert (x = 0)
let f2 x = assert (x = 1)
let main () = (apply f1 0, apply f2 1)

[@@@assert "typeof(main) <: unit -> unit * unit"]
