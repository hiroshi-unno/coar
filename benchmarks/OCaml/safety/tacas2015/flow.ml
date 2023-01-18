let lamp (x:unit) = x
let id (x:unit->unit) = x
let fail n = assert false
let f =
  let unused = id fail in
  lamp

let main () = f ()

[@@@assert "typeof(main) <: unit -> unit"]

(*
let lamp x = x
let f =
  let id x = x in
  let unused = id (fun _ -> assert false) in
    lamp

let main () = f ()
*)
