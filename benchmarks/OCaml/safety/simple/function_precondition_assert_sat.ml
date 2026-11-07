(* f is safe only on the arguments it is called with: a typing must give its
   argument the refinement x > 0.  A placement that refines no function
   argument (assuming that functions cannot fail) has no typing of this
   program, which is safe. *)
let f x = assert (x > 0)
let main () = f 1
[@@@assert "typeof(main) <: unit -> unit"]
