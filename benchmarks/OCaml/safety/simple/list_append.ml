let hd = function [] -> assert false | hd :: _ -> hd

let rec length = function
  | [] -> 0
  | _ :: tl -> 1 + length tl

let rec ( @ ) l1 l2 =
  match l1 with
    [] -> l2
  | hd :: tl -> hd :: (tl @ l2)

let append l1 l2 = (@) l1 l2

[@@@assert "typeof(append) <: (l1:int list) -> (l2:int list) -> {ret : int list | l1 = [] => l2 = ret}"]
[@@@assert "typeof(append) <: (l1:int list) -> (l2:int list) -> {ret : int list | l2 = [] => l1 = ret}"]

let main l1 l2 = assert (hd l1 = hd (append l1 l2))

[@@@assert "typeof(main) <: (l1:{v: int list | v <> []}) -> int list -> unit"]
[@@@assert "typeof(main) <: (l1:{v: int list | v = []}) -> {v: int list | v <> []} -> unit"]
[@@@assert "typeof(main) <: int list -> int list -> unit"]

let main l1 l2 =
  match l1 with
  | [] -> ()
  | hd :: tl -> if tl = [] then assert (append l1 l2 = hd :: l2)

[@@@assert "typeof(main) <: int list -> int list -> unit"]

let main l1 l2 =  
  if not (append l1 l2 = []) then assert (not (l1 = [] && l2 = []))

[@@@assert "typeof(main) <: int list -> int list -> unit"]
