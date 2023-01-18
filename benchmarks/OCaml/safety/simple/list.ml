let rec map f = function
  | [] -> []
  | a :: l -> let r = f a in r :: map f l

let main l f = match map f l with [] -> assert false | a :: _ -> a

[@@@assert "typeof(main) <: (l:{l:int list | l <> []}) -> (f:int -> {v : int | v < 0}) -> {r : int | r < 0}"]

let rec length = function
  | [] -> 0
  | _ :: tl -> 1 + length tl

let main l = assert (length l >= 0)

[@@@assert "typeof(main) <: int list -> unit"]

let main l1 = if length l1 > 0 then assert(not (l1 = []))

[@@@assert "typeof(main) <: int list -> unit"]

let main l1 = 
  match l1 with 
  | [] -> ()
  | _ :: _ -> assert (length l1 >= 1)

[@@@assert "typeof(main) <: int list -> unit"]

let main l1 l2 = 
  if length l1 < length l2 then assert (not (l2 = []))

[@@@assert "typeof(main) <: int list -> int list -> unit"]
