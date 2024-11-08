open Core
open Ext

type t = int array

let make n = Array.init n ~f:(Fn.const (-1))

let rec root x uf =
  let y = uf.(x) in
  if y < 0 then x
  else
    let z = root y uf in
    uf.(x) <- z;
    z

let size x uf = -uf.(root x uf)
let find_set x y uf = root x uf = root y uf

let union_set x y uf =
  let x, y = (root x uf, root y uf) in
  if x <> y then (
    let x, y = if uf.(x) < uf.(y) then (y, x) else (x, y) in
    uf.(x) <- uf.(x) + uf.(y);
    uf.(y) <- x;
    (* x <> y; *)
    uf)
  else (* x <> y; *)
    uf

let find_class x uf =
  List.filter ~f:(fun y -> find_set x y uf)
  @@ List.init (Array.length uf) ~f:Fn.id

let all_classes uf =
  let rec aux acc = function
    | [] -> acc
    | x :: rest ->
        let a, b = List.partition_tf rest ~f:(fun y -> find_set x y uf) in
        aux ((x :: a) :: acc) b
  in
  aux [] @@ List.init (Array.length uf) ~f:Fn.id

let print uf =
  Format.printf "uf:@.{";
  Array.iter ~f:(Format.printf "%d,") uf;
  Format.printf "}@."

let print_class uf =
  List.iter (all_classes uf) ~f:(fun l ->
      Format.printf "{";
      List.iter l ~f:(Format.printf "%d,");
      Format.printf "}@.")
