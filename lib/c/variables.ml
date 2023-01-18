open Core

module StringSet = Set.Make(String)

type t = StringSet.t

let empty = StringSet.empty

let union vars1 vars2 : t = StringSet.union vars1 vars2

let add var vars : t = StringSet.add vars var

let sub vars1 vars2 : t = StringSet.diff vars1 vars2

let inter vars1 vars2 : t = StringSet.inter vars1 vars2

let is_mem varname vars = StringSet.mem varname vars

let of_list varnames : t = StringSet.of_list varnames

let of_tvarset tvarset : t =
  Set.Poly.to_list tvarset
  |> List.map ~f:Ast.Ident.name_of_tvar
  |> of_list

let of_varname varname: t = add varname empty

let to_list (vars: t) = StringSet.elements vars

let string_of (vars: t) = String.concat ~sep:", " @@ to_list vars

let is_empty vars: bool = StringSet.is_empty vars
