(* [raise Exit] escapes [main] for every positive argument, so [main] does not
   have the asserted type, whose operation signature is empty.  A raised
   exception is read as an operation, and the subtyping of operation
   signatures refuses the file naming the operation [Exit] rather than with a
   bare internal failure. *)
let main n = if n > 0 then raise Exit else ()

[@@@assert "typeof(main) <: int -> unit"]
