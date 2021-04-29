module StringSet = Set.Make(String)

type t = StringSet.t

let empty = StringSet.empty

let union vars1 vars2: t =
  StringSet.union vars1 vars2

let add var vars: t =
  StringSet.add var vars

let sub vars1 vars2: t =
  StringSet.diff vars1 vars2

let inter vars1 vars2: t =
  StringSet.inter vars1 vars2

let is_mem varname vars =
  StringSet.mem varname vars

let of_list varnames: t =
  StringSet.of_list varnames

let of_tvarset tvarset: t =
  Core.Set.Poly.to_list tvarset
  |> List.map Ast.Ident.name_of_tvar
  |> of_list

let of_varname varname: t =
  add varname empty

let to_list (vars: t) =
  StringSet.elements vars

let string_of (vars: t) =
  to_list vars
  |> String.concat ", "

let is_empty vars: bool =
  StringSet.is_empty vars
