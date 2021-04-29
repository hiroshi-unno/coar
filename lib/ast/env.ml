(* Syntax of the Env *)

type key
type elem

let rec str_of_tenv = function
  | [] -> ""
  | (Ident.Tvar x, _) :: xs -> x ^ ", " ^ str_of_tenv xs

let rec str_of_penv = function
  | [] -> ""
  | (Ident.Pvar x, _) :: xs -> x ^ ", " ^ str_of_penv xs

let lookupi_exn key env =
  let rec aux i = function
    | [] -> raise Not_found
    | (k, e) :: xs ->
      if k = key then e, i
      else aux (i+1) xs
  in
  aux 0 env

let lookupi key env =
  try Some (lookupi_exn key env)
  with Not_found -> None

let lookup_exn key env =  let e, _ = lookupi_exn key env in e
let lookup key env =
  try Some(lookup_exn key env)
  with Not_found -> None

let update bounds env = bounds @ env

let keys env =
  let rec aux acc = function
    | [] -> acc
    | (key, _) :: xs -> aux (key::acc) xs
  in
  aux [] env
  |> List.rev

let elems env =
  let rec aux acc = function
    | [] -> acc
    | (_, elem) :: xs -> aux (elem :: acc) xs
  in
  aux [] env

let entries env = env

let nth = List.nth
let length = List.length
let size = List.length

let has key = List.mem_assoc key

let empty = []

type ('a, 'b) t = ('a * 'b) list

