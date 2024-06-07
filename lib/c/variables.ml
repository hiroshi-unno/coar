open Core

type t = string Set.Poly.t

let empty : string Set.Poly.t = Set.Poly.empty
let union vars1 vars2 : t = Set.union vars1 vars2
let add var vars : t = Set.add vars var
let sub vars1 vars2 : t = Set.diff vars1 vars2
let inter vars1 vars2 : t = Set.inter vars1 vars2
let is_mem varname vars = Set.mem varname vars
let of_list varnames : t = Set.Poly.of_list varnames

let of_tvarset tvarset : t =
  Set.to_list tvarset |> List.map ~f:Ast.Ident.name_of_tvar |> of_list

let of_varname varname : t = add varname empty
let to_list (vars : t) = Set.elements vars
let string_of (vars : t) = String.concat ~sep:", " @@ to_list vars
let is_empty vars : bool = Set.is_empty vars
