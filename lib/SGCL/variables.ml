open Core
open Common.Ext

type t = (string * Ast.LogicOld.Sort.t) Set.Poly.t

let empty : t = Set.Poly.empty
let union vars1 vars2 : t = Set.union vars1 vars2
let add var vars : t = Set.add vars var
let sub vars1 vars2 : t = Set.diff vars1 vars2
let inter vars1 vars2 : t = Set.inter vars1 vars2
let is_mem vars varname = Set.mem vars varname
let of_list varnames : t = Set.Poly.of_list varnames

let of_tvarset tvarset : t =
  Set.to_list tvarset
  |> List.map ~f:(fun (x, s) -> (Ast.Ident.name_of_tvar x, s))
  |> of_list

let of_varname varname : t = add varname empty
let to_list (vars : t) = Set.elements vars
let string_of (vars : t) = String.concat_map_set ~sep:", " ~f:fst vars
let is_empty vars : bool = Set.is_empty vars
