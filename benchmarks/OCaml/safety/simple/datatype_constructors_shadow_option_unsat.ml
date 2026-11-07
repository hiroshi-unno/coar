(* [None] and [Some] of a file's own type hide those of the built-in [option]:
   [find] returns [Some x] only for an element equal to [x], so the asserted
   [y <> x] fails whenever [find] finds something. *)
type int_list = Nil | Cons of int * int_list
type int_option = None | Some of int

let rec find x l =
  match l with
  | Nil -> None
  | Cons (y, t) -> if x = y then Some y else find x t

let main x l = match find x l with None -> () | Some y -> assert (y <> x)

[@@@assert "typeof(main) <: int -> int_list -> unit"]
