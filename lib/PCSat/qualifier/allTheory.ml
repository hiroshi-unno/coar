open Core
open Common.Ext
open Ast
open LogicOld
open PCSatCommon

let split_params_by_theory params =
  List.fold_left params ~init:(Map.Poly.empty) ~f:(fun ret (tvar, sort) ->
      match Map.Poly.find ret sort with
      | Some (env) -> Map.Poly.set ret ~key:sort ~data:(Set.Poly.add env @@ (Term.mk_var tvar sort, []))
      | None ->  Map.Poly.set ret ~key:sort ~data:(Set.Poly.singleton @@ (Term.mk_var tvar sort, [])))

let str_of_term_list ts = String.concat_map_list ~sep:"," ts ~f:Term.str_of
let str_of_term_list_list tss = String.concat_map_list ~sep:"\n" tss ~f:str_of_term_list


let mk_func_app_terms
    (term_map:(Sort.t, (Term.t * Formula.t list) Set.Poly.t) Map.Poly.t) fenv =
  Map.Poly.fold fenv ~init:(Set.Poly.empty)
    ~f:(fun ~key:tvar ~data:(param_env, ret_sort, _, _, _) ret ->
        if Ident.is_size_fun_var tvar then ret
        else
          let args' = List.map param_env ~f:(fun (_, sort) ->
              match Map.Poly.find term_map sort with
              | Some ts -> Set.Poly.to_list ts |> List.unzip |> fst
              | _ -> [Term.mk_dummy sort]) in
          let args_permutation = List.permutation_without_repetion_of args' in
          Set.Poly.union ret @@
          Set.Poly.of_list @@
          List.map args_permutation ~f:(fun ts ->
              Term.mk_fvar_app tvar (List.map ~f:snd param_env @ [ret_sort]) ts))

let int_real_terms_of term_map params =
  Map.Poly.fold term_map ~init:Set.Poly.empty
    ~f:(fun ~key:sort ~data:(terms) ret ->
        let terms =
          Set.Poly.filter_map terms ~f:(fun (term, _dep) ->
              match term with
              | Term.Var (tvar, _, _)
                when List.exists params ~f:(fun (tvar1, _) -> Stdlib.(tvar = tvar1)) -> None
              | _ -> Some term)
        in
        match sort with
        | T_int.SInt | T_real.SReal -> Set.Poly.union terms ret | _ -> ret)
let bool_quals_of terms params =
  let terms =
    Set.Poly.filter_map terms ~f:(fun (term, dep) ->
        match term with
        | Term.Var (tvar, _, _)
          when List.exists params ~f:(fun (tvar1, _) -> Stdlib.(tvar = tvar1)) -> None
        | _ -> Some (term, dep))
  in
  Set.Poly.map terms ~f:(fun (t, dep) ->
      let qual = Formula.eq t (T_bool.mk_true ()) in
      QDep.qual_and_deps_of qual dep)
  |> Set.Poly.to_list
  |> List.map ~f:(fun (qual, dep) -> (qual, (qual, dep)))
  |> List.unzip |> (fun (quals, qdeps) -> Set.Poly.of_list quals, Map.Poly.of_alist_exn qdeps)


let add_term_map term_map term =
  let sort = Term.sort_of term in
  match Map.Poly.find term_map sort with
  | Some terms -> Map.Poly.set term_map ~key:sort ~data:(Set.Poly.add terms (term, []))
  | _ -> Map.Poly.add_exn term_map ~key:sort ~data:(Set.Poly.singleton (term, []))

let add_mod_quals quals =
  let rec inner i quals =
    let quals' = Set.Poly.union quals @@ Set.Poly.map quals ~f:(fun qual ->
        Formula.map_term qual ~f:(function
            | Term.FunApp (T_int.Mod, [t1; t2], info) when T_int.is_int t2 ->
              let m = Z.to_int @@ T_int.let_int t2 in
              if m > i && m mod i = 0 then
                Term.FunApp (T_int.Mod, [t1; T_int.mk_int (Z.of_int i)], info)
              else Term.FunApp (T_int.Mod, [t1; t2], info)
            | t -> t)) in
    if Set.Poly.length quals' = Set.Poly.length quals then quals'
    else inner (i + 1) quals'
  in
  inner 2 quals
let add_quals_form_affine_eq_quals quals =
  Set.Poly.union quals @@
  Set.concat @@ Set.Poly.filter_map quals ~f:(fun phi ->
      if Formula.is_atom phi then
        match Formula.let_atom phi with
        | Atom.App (Predicate.Psym (T_bool.Eq | T_bool.Neq), [t1; t2], _), _
          when Stdlib.(Term.sort_of t1 = T_int.SInt) && AffineTerm.is_affine t1 ->
          Option.some @@ Set.Poly.of_list [Formula.mk_atom @@ T_int.mk_gt t1 t2]
        | _ -> None
      else None)

let add_mod_quals_terms quals terms =
  let quals' = add_mod_quals quals in
  if Set.Poly.length quals' = Set.Poly.length quals then quals, terms
  else
    (* let terms =
       Set.concat_map quals ~f:Formula.terms_of
       |> Set.Poly.filter ~f:(T_int.is_mod)
       |> Set.Poly.union terms
       in *)
    quals', terms

let mk_mod_quals params =
  Set.Poly.of_list @@ List.filter_map params ~f:(fun (v, s) ->
      if not Stdlib.(T_int.SInt = s) then None
      else
        Option.some @@
        Formula.eq (T_int.mk_mod (Term.mk_var v s) (T_int.mk_int (Z.of_int 2))) (T_int.zero ()))

let mk_eq_quals_for_ith_param params i =
  if i >= List.length params || List.length params <= 1 then Set.Poly.empty
  else
    let (vi, si) = List.nth_exn params i in
    List.fold params ~init:Set.Poly.empty ~f:(fun acc (v, s) ->
        if Stdlib.(v = vi) || Stdlib.(s <> si) then acc
        else Set.Poly.add acc (Formula.eq (Term.mk_var v s) (Term.mk_var vi si)))

let reduce_dedup_quals quals =
  Set.Poly.map quals ~f:(fun phi -> Evaluator.simplify phi |> Normalizer.normalize)
  |> Set.Poly.map ~f:Evaluator.simplify

let qualifiers_of ?(add_mod2_quals=false) ~fenv
    depth _old_depth (params:sort_env_list) old_quals old_qdeps old_terms =
  let old_quals, old_terms = add_mod_quals_terms old_quals old_terms in
  let old_quals = add_quals_form_affine_eq_quals old_quals in
  let old_quals =
    if add_mod2_quals then Set.Poly.union (mk_mod_quals params) old_quals else old_quals
  in
  let rec aux d term_map =
    if d > depth then term_map
    else
      aux (d + 1) @@
      Map.Poly.fold term_map ~init:term_map ~f:(fun ~key:sort ~data:terms term_map ->
          match sort with
          | T_dt.SDT _ -> DtTheory.update_term_map ~depth:d sort terms term_map
          | T_array.SArray _ -> ArrayTheory.update_term_map ~d:d sort terms term_map
          | _ -> term_map)
  in
  let term_map = split_params_by_theory params in
  let term_map = Set.Poly.fold old_terms ~init:term_map ~f:add_term_map in
  let func_terms = mk_func_app_terms term_map fenv in
  let term_map = Set.Poly.fold func_terms ~init:term_map ~f:add_term_map in
  let term_map = aux 0 term_map in
  let quals, qdeps =
    Map.Poly.fold term_map ~init:(old_quals, old_qdeps)
      ~f:(fun ~key:sort ~data:terms (quals, qdeps) ->
          match sort with
          | T_dt.SDT _ ->
            let quals', qdeps' = DtTheory.qualifiers_of sort terms in
            Set.Poly.union quals' quals,
            Map.force_merge qdeps qdeps'
          | T_array.SArray _ ->
            ArrayTheory.qualifiers_of sort terms,
            qdeps (* TODO: Update param qdeps for array quals*)
          | T_bool.SBool ->
            let quals', qdeps' = bool_quals_of terms params in
            Set.Poly.union quals' quals,
            Map.force_merge qdeps qdeps'
          | T_int.SInt | T_real.SReal | T_tuple.STuple _(*ToDo*) | Sort.SArrow _(*ToDo*) ->
            quals, qdeps
          | _ ->
            (*print_endline ("@" ^ Term.str_of_sort sort);*)
            Set.Poly.of_list @@ List.map ~f:Formula.mk_atom @@
            T_bool.mk_eqs (fst @@ List.unzip @@ Set.Poly.to_list terms),
            qdeps(*ToDo*))
  in
  reduce_dedup_quals quals, qdeps, int_real_terms_of term_map params
