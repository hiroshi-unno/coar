let rec exists f = function [] -> false | hd :: tl -> f hd || exists f tl

let gt0 i = i > 0

let main d l1 = if gt0 d then assert (exists gt0 (d :: l1))

[@@@assert "typeof(main) <: int -> (l1:{v: int list | true }) -> unit"]

let main d l1 = if not (gt0 d) then assert (exists gt0 (d :: l1))

[@@@assert "typeof(main) <: int -> (l1:{v: int list | true }) -> unit"]

let main d l1 = if exists gt0 l1 then assert (exists gt0 (d :: l1))

[@@@assert "typeof(main) <: int -> (l1:{v: int list | true }) -> unit"]

let rec exists_gt0 l =
  match l with
  | [] -> false
  | a :: tl -> a > 0 || exists_gt0 tl

let main l1 l2 = if exists_gt0 l1 && not (exists_gt0 l2) then assert (not (l1 = l2))

[@@@assert "typeof(exists_gt0) <: (x1:{l:int list | l <> []}) -> {ret:bool | ret = true}"]

let main l1 l2 = if l1 = l2 then assert (exists_gt0 l1 = exists_gt0 l2)

[@@@assert "typeof(main) <: int list -> int list -> unit"]

let main l1 l2 = if l1 = l2 then assert (not (exists_gt0 l1 = exists_gt0 l2))

[@@@assert "typeof(main) <: int list -> int list -> unit"]

let main l1 = if not (exists_gt0 l1) then assert (exists_gt0 (0 :: l1))

[@@@assert "typeof(main) <: int list -> unit"]

let main l1 = if exists_gt0 l1 then assert (exists_gt0 (0 :: l1))

[@@@assert "typeof(main) <: int list -> unit"]

let main x = if exists_gt0 [x] then assert (x > 0)

[@@@assert "typeof(main) <: int -> unit"]

let main x l1 = if exists_gt0 (x :: l1) then assert (x > 0)

[@@@assert "typeof(main) <: int -> int list -> unit"]
