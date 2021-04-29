open Core
open Common.Util
open LogicOld

type t = SortMap.t * (Ident.pvar * (SortEnv.t * Formula.t)) Set.Poly.t

let str_of ((_, cand) : t) : string =
  String.concat ~sep:"\n"
  @@ Set.Poly.to_list
  @@ Set.Poly.map cand ~f:(fun (Ident.Pvar pvar, (params, phi)) ->
      let params', map = SortEnv.normalize params in
      Printf.sprintf "%s(%s) :=\n  %s"
        pvar
        (SortEnv.str_of Term.str_of_sort params')
        (Formula.str_of (Formula.rename map phi)))

let str_of_list candidates =
  String.concat ~sep:"\n"
  @@ List.mapi candidates ~f:(fun i candidate ->
      (Printf.sprintf "**** %s candidate solution\n" (Ordinal.string_of i))
      ^ (str_of candidate) ^ "\n")

let of_subst (sub : (Ident.tvar, Logic.term) Map.Poly.t) : t =
  SortMap.empty,
  Map.Poly.to_alist sub
  |> List.map ~f:(fun (Ident.Tvar x, t) ->
      let args, t' = Logic.Term.let_lam t in
      let params = Logic.SortEnv.to_old_sort_env Logic.ExtTerm.to_old_sort args in
      let params', map = LogicOld.SortEnv.normalize params in
      let phi = Formula.rename map @@ Logic.ExtTerm.to_old_formula (SortMap.of_list args) t' [] in
      Ident.Pvar x, (params', phi))
  |> Set.Poly.of_list

let of_list (cand : (Ident.pvar * (SortEnv.t * Formula.t)) list) : t =
  SortMap.empty, Set.Poly.of_list cand