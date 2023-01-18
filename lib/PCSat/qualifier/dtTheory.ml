open Core
open Common.Ext
open Ast.LogicOld
open PCSatCommon


let split_sels dt =
  List.partition_tf ~f:(function
      | Datatype.Sel _ -> true
      | Datatype.InSel (_, dt_name, dt_args) ->
        not Stdlib.(dt_name = Datatype.name_of dt) ||
        not Stdlib.(dt_args = Datatype.args_of dt))

let update_term_map ~depth sort
    (terms : (Term.t * Formula.t list) Set.Poly.t)
    (term_map : (Sort.t, (Term.t * Formula.t list) Set.Poly.t) Map.Poly.t) =
  if depth = 0 then term_map
  else
    match sort with
    | T_dt.SDT dt ->
      Set.Poly.fold terms ~init:term_map ~f:(fun term_map (term, conds) ->
          let conses = Datatype.conses_of dt in
          let sel_terms = List.concat_map conses ~f:(fun cons ->
              let sels = Datatype.sels_of_cons cons in
              let sels, insels = split_sels dt sels in
              let in_terms = List.map insels ~f:(fun sel ->
                  T_dt.mk_sel dt (Datatype.name_of_sel sel) term) in
              let sel_terms = in_terms @ (List.concat_map sels ~f:(fun sel ->
                  List.map [term] ~f:(T_dt.mk_sel dt @@ Datatype.name_of_sel sel))) in
              List.map sel_terms ~f:(fun sel_term ->
                  sel_term,
                  (Formula.mk_atom @@
                   T_dt.mk_is_cons dt (Datatype.name_of_cons cons) term) :: conds))
          in
          List.fold_left sel_terms ~init:term_map ~f:(fun term_map (sel_term, conds) ->
              let sel_sort = Term.sort_of sel_term in
              match Map.Poly.find term_map sel_sort  with
              | Some group ->
                Map.Poly.set term_map
                  ~key:sel_sort ~data:(Set.Poly.add group (sel_term, conds))
              | None ->
                Map.Poly.add_exn term_map
                  ~key:sel_sort ~data:(Set.Poly.singleton (sel_term, conds))))
    | _ -> term_map

let rec is_sub_term t2 t1 =
  match t1 with
  | Term.FunApp (_, ts, _) ->
    if List.mem ts t2 ~equal:Stdlib.(=) then true else List.mem ts t2 ~equal:(is_sub_term)
  | _ -> false
let is_cyclic t1 t2 = is_sub_term t1 t2 || is_sub_term t2 t1


let mk_eqs (ts : (Term.t * Formula.t list) list) =
  List.concat_mapi ts ~f:(fun i (t, conds) ->
      List.foldi ts ~init:[] ~f:(fun i1 ret (t1, conds1) ->
          let conds = conds @ conds1 in
          if i1 <= i
          || Stdlib.(Term.sort_of t <> Term.sort_of t1)
          || Stdlib.(t = t1)
          || is_cyclic t t1
          then ret
          else
            let qual = Formula.mk_atom (T_bool.mk_eq t t1) in
            QDep.qual_and_deps_of qual conds :: ret))

let qualifiers_of sort (terms : (Term.t * Formula.t list) Set.Poly.t) =
  match sort with
  | T_dt.SDT dt ->
    let conses = Datatype.conses_of dt in
    let testers =
      List.concat_map conses ~f:(fun cons ->
          Set.Poly.to_list @@ Set.Poly.map terms ~f:(fun (t, conds) ->
              let qual =
                Formula.mk_atom @@ T_dt.mk_is_cons dt (Datatype.name_of_cons cons) t
              in
              QDep.qual_and_deps_of qual conds)) in
    let eqs =
      Set.Poly.filter terms ~f:(fun (t, _) -> Term.is_var t || T_dt.is_sdt @@ Term.sort_of t)
      |> Set.Poly.to_list
      |> mk_eqs in
    let qdep_env =
      try Map.Poly.of_alist_exn @@ List.unique @@ testers @ eqs with _ ->
        failwith @@ "[qualifiers_of]\n" ^
                    String.concat_map_list ~sep:"\n" (testers @ eqs) ~f:(fun (phi, qdep) -> Formula.str_of phi ^ " |-> " ^ QDep.str_of qdep)
    in
    Set.Poly.of_list @@ Map.Poly.keys qdep_env, qdep_env
  | _ -> Set.Poly.empty, Map.Poly.empty
