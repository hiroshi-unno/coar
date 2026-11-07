(* A polymorphic map whose argument and result element types are two distinct
   type variables, with the result matched against the empty list: each empty
   list in the generated clauses must keep its own element sort. *)
let rec map f = function
  | [] -> []
  | a :: l -> let r = f a in r :: map f l

let main l f = match map f l with [] -> assert false | a :: _ -> a

[@@@assert "typeof(main) <: (l:{l:int list | l <> []}) -> (f:int -> {v : int | v < 0}) -> {r : int | r < 0}"]
