open Core
open Common
open Util
open Ast
open LogicOld


let split_params_by_theory params =
  SortEnv.list_of params 
  |> List.fold_left ~init:(Map.Poly.empty) ~f:(
    fun ret (tvar, sort) ->
      match Map.Poly.find ret sort with
      | Some (env) -> Map.Poly.set ret ~key:sort ~data:(Set.Poly.add env @@ Term.mk_var tvar sort)
      | None ->  Map.Poly.set ret ~key:sort ~data:(Set.Poly.singleton @@ Term.mk_var tvar sort)
  ) 

let str_of_term_list ts =
  String.concat ~sep:"," (List.map ts ~f:(Term.str_of)) 

let str_of_term_list_list tss =
  String.concat ~sep:"\n" (List.map tss ~f:(str_of_term_list))


let rec combine_aux l ret pair last =
  let inner l next =
    List.fold_left l ~init:[] ~f:(
      fun ret hd -> ret @ next (Some hd)
    )
  in
  let pair' = begin match last with | Some t -> t::pair | _ -> pair end in
  match l with
  | [] -> pair'::ret
  | hd::tl -> 
    inner hd (combine_aux tl ret pair')

let combine l =
  combine_aux l [] [] None

let mk_func_app_terms (term_map:(Sort.t, Term.t Core.Set.Poly.t) Core.Map.Poly.t) fenv =
  Set.Poly.fold fenv ~init:(Set.Poly.empty) ~f:(
    fun ret (tvar, args, ret_sort, body, _) ->
      let args' = List.filter_map args ~f:(fun (_, sort) -> match Map.Poly.find term_map sort with Some ts -> Some (Set.Poly.to_list ts) | _ -> None ) in
      let args_list = combine args' in
      Set.Poly.union ret @@ Set.Poly.of_list @@ List.map args_list ~f:(fun ts -> T_recfvar.mk_recfvar_app tvar args ret_sort body ts)

  )

let default_terms_of term_map params =
  Map.Poly.fold term_map ~init:Set.Poly.empty ~f:(
    fun ~key:sort ~data:terms ret ->
      let terms = Set.Poly.filter terms ~f:(fun term -> not @@ SortEnv.exists params ~f:(
          fun (tvar1, _) -> match term with |Term.Var(tvar, _, _) -> Stdlib.(=) tvar tvar1 | _ -> false)) in
      match sort with
      | T_int.SInt | T_bool.SBool | T_real.SReal -> Set.Poly.union terms ret | _ -> ret
  )

let add_term_map term_map term =
  let sort = Term.sort_of term in
  match Map.Poly.find term_map sort with
  | Some terms -> Map.Poly.set term_map ~key:sort ~data:(Set.Poly.add terms term)
  | _ -> Map.Poly.add_exn term_map ~key:sort ~data:(Set.Poly.singleton term)

let qualifiers_of ?(fenv=Set.Poly.empty) (_nd, _nc, depth, _ubc, _ubd, _s) old_depth (params:SortEnv.t) old_quals old_terms =
  if old_depth >= depth then old_quals, old_terms
  else
    let old_depth = if old_depth < 0 then 0 else old_depth in
    let depth = old_depth in
    let rec aux d term_map =
      if d > depth then term_map 
      else Map.Poly.fold term_map ~init:term_map ~f:(
          fun ~key:sort ~data:terms term_map ->
            match sort with
            | T_dt.SDT _ -> DtTheory.update_term_map ~d:d sort terms term_map
            | T_array.SArray _ -> ArrayTheory.update_term_map ~d:d sort terms term_map
            | _ -> term_map
        ) |> aux (d + 1) in
    let term_map = split_params_by_theory params in
    let term_map = Set.Poly.fold old_terms ~init:term_map ~f:(add_term_map) in
    let _func_terms = mk_func_app_terms term_map fenv in
    let term_map = Set.Poly.fold _func_terms ~init:term_map ~f:(add_term_map) in
    let term_map = aux 0 term_map in
    Map.Poly.fold term_map ~init:old_quals ~f:(
      fun ~key:sort ~data:terms ret ->
        Set.Poly.union ret @@ match sort with
        | T_dt.SDT _ -> DtTheory.qualifiers_of sort terms
        | T_array.SArray _ -> ArrayTheory.qualifiers_of sort terms
        | T_bool.SBool | T_int.SInt | T_real.SReal -> ret
        | _ -> T_bool.mk_eqs (Set.Poly.to_list terms) |> List.map ~f:(Formula.mk_atom) |> Set.Poly.of_list
    ) , default_terms_of term_map params



