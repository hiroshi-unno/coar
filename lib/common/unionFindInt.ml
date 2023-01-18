open Core
open Ext

type t = int array

let make n = Array.init n ~f:(fun _ -> -1)

let rec root x uf =
  let y = uf.(x) in
  if y < 0 then x else begin
    let z = root y uf in
    uf.(x) <- z;
    z
  end

let size x uf = -uf.(root x uf)

let find_set x y uf =
  root x uf = root y uf

let union_set x y uf =
  let x, y = root x uf, root y uf in
  if x <> y then begin
    let x, y = if uf.(x) < uf.(y) then y,x else x, y in
    uf.(x) <- uf.(x) + uf.(y);
    uf.(y) <- x;
    (* x <> y; *)
    uf
  end else begin
    (* x <> y; *)
    uf
  end

let find_class x uf =
  let l = List.init (Array.length uf) ~f:Fn.id in
  List.filter ~f:(fun y -> find_set x y uf) l

let all_classes uf =
  let l = List.init (Array.length uf) ~f:Fn.id in
  let rec aux acc = function
    | [] -> acc
    | x :: rest ->
      let a, b = List.partition_tf ~f:(fun y -> find_set x y uf) rest in
      aux ((x :: a) :: acc) b
  in
  aux [] l

let print uf =
  Format.printf "uf:@.{";
  Array.iter ~f:(Format.printf "%d,") uf;
  Format.printf "}@."

let print_class uf =
  List.iter ~f:(fun l ->
      Format.printf "{";
      List.iter ~f:(Format.printf "%d,") l;
      Format.printf "}@.")
  @@ all_classes uf
