open Core
open Common.Ext
open Common.Combinator
open Ast
open LogicOld
open PCSatCommon
open PCSatCommon.HypSpace

let split_params_by_theory =
  List.fold_left ~init:Map.Poly.empty ~f:(fun ret (tvar, sort) ->
      let term = Term.mk_var tvar sort in
      match Map.Poly.find ret sort with
      | Some env -> Map.Poly.set ret ~key:sort ~data:(Set.add env (term, []))
      | None -> Map.Poly.set ret ~key:sort ~data:(Set.Poly.singleton (term, [])))

let str_of_term_list = String.concat_map_list ~sep:"," ~f:Term.str_of
let str_of_term_list_list = String.concat_map_list ~sep:"\n" ~f:str_of_term_list

let mk_func_app_terms
    (term_map : (Sort.t, (Term.t * Formula.t list) Set.Poly.t) Map.Poly.t) fenv
    =
  Map.Poly.fold fenv ~init:Set.Poly.empty
    ~f:(fun ~key:tvar ~data:(param_env, ret_sort, _, _, _) ret ->
      if Ident.is_size_fun_var tvar then ret
      else
        let sorts = List.map ~f:snd param_env @ [ ret_sort ] in
        Set.union ret @@ Set.Poly.of_list
        @@ List.map ~f:(Term.mk_fvar_app tvar sorts)
        @@ List.permutation_without_repetion_of
        @@ List.map param_env ~f:(fun (_, sort) ->
               match Map.Poly.find term_map sort with
               | Some ts -> List.map ~f:fst @@ Set.to_list ts
               | _ -> [ Term.mk_dummy sort ]))

let int_real_terms_of term_map params =
  Map.Poly.fold term_map ~init:Set.Poly.empty
    ~f:(fun ~key:sort ~data:terms ret ->
      match sort with
      | T_int.SInt | T_real.SReal ->
          Set.union ret
          @@ Set.Poly.filter_map terms
               ~f:
                 (fst >> function
                  | Term.Var (x, _, _)
                    when List.exists params ~f:(fst >> Stdlib.( = ) x) ->
                      None
                  | term -> Some term)
      | _ -> ret)

let bool_quals_of terms params =
  Set.Poly.filter_map terms ~f:(fun (term, dep) ->
      match term with
      | Term.Var (x, _, _) when List.exists params ~f:(fst >> Stdlib.( = ) x) ->
          None
      | _ -> Some (term, dep))
  |> Set.Poly.map ~f:(fun (t, dep) ->
         QDep.qual_and_deps_of (Formula.eq t (T_bool.mk_true ())) dep)
  |> Set.to_list
  |> List.map ~f:(fun (qual, dep) -> (qual, (qual, dep)))
  |> List.unzip
  |> fun (quals, qdeps) -> (Set.Poly.of_list quals, Map.Poly.of_alist_exn qdeps)

let add_term_map term_map term =
  let sort = Term.sort_of term in
  match Map.Poly.find term_map sort with
  | Some terms ->
      Map.Poly.set term_map ~key:sort ~data:(Set.add terms (term, []))
  | _ ->
      Map.Poly.add_exn term_map ~key:sort ~data:(Set.Poly.singleton (term, []))

let add_mod_quals quals =
  let rec inner i quals =
    let quals' =
      Set.union quals
      @@ Set.Poly.map quals ~f:(fun qual ->
             Formula.map_term qual ~f:(function
               | Term.FunApp (T_int.Mod, [ t1; t2 ], info) as t
                 when T_int.is_int t2 ->
                   let m = Z.to_int (*ToDo*) @@ T_int.let_int t2 in
                   if m > i && m mod i = 0 then
                     Term.FunApp (T_int.Mod, [ t1; T_int.from_int i ], info)
                   else t
               | t -> t))
    in
    if Set.equal quals quals' then quals else inner (i + 1) quals'
  in
  inner 2 quals

let add_quals_form_affine_eq_quals quals =
  Set.union quals @@ Set.concat
  @@ Set.Poly.filter_map quals ~f:(fun phi ->
         if Formula.is_atom phi then
           match Formula.let_atom phi with
           | ( Atom.App (Predicate.Psym (T_bool.Eq | T_bool.Neq), [ t1; t2 ], _),
               _ )
             when (Term.is_int_sort @@ Term.sort_of t1)
                  && AffineTerm.is_affine t1 ->
               Option.some
               @@ Set.Poly.of_list [ Formula.mk_atom @@ T_int.mk_gt t1 t2 ]
           | _ -> None
         else None)

let add_mod_quals_terms quals terms =
  let quals' = add_mod_quals quals in
  if Set.equal quals' quals then (quals, terms)
  else
    (* let terms =
       Set.concat_map quals ~f:Formula.terms_of
       |> Set.filter ~f:T_int.is_mod
       |> Set.union terms
       in *)
    (quals', terms)

let mk_mod_quals params =
  Set.Poly.of_list
  @@ List.filter_map params ~f:(fun (v, s) ->
         if Fn.non Term.is_int_sort s then None
         else
           Option.some
           @@ Formula.eq
                (T_int.mk_mod (Term.mk_var v s) (T_int.from_int 2))
                (T_int.zero ()))

let mk_eq_quals_for_ith_param params i =
  if i >= List.length params || List.length params <= 1 then Set.Poly.empty
  else
    let vi, si = List.nth_exn params i in
    List.fold params ~init:Set.Poly.empty ~f:(fun acc (v, s) ->
        if Stdlib.(v = vi) || Stdlib.(s <> si) then acc
        else Set.add acc (Formula.eq (Term.mk_var v s) (Term.mk_var vi si)))

let qualifiers_of ?(add_mod2_quals = false) ~fenv depth hspace =
  let quals, terms = add_mod_quals_terms hspace.quals hspace.terms in
  let quals =
    let quals = add_quals_form_affine_eq_quals quals in
    if add_mod2_quals then Set.union (mk_mod_quals hspace.params) quals
    else quals
  in
  let term_map =
    let rec aux d term_map =
      if d > depth then term_map
      else
        aux (d + 1)
        @@ Map.Poly.fold term_map ~init:term_map
             ~f:(fun ~key:sort ~data:terms ->
               match sort with
               | T_dt.SDT _ -> DtTheory.update_term_map ~depth:d sort terms
               | T_array.SArray _ ->
                   ArrayTheory.update_term_map ~depth:d sort terms
               | _ -> Fn.id)
    in
    let term_map =
      Set.fold terms
        ~init:(split_params_by_theory hspace.params)
        ~f:add_term_map
    in
    mk_func_app_terms term_map fenv
    |> Set.fold ~init:term_map ~f:add_term_map
    |> aux 0
  in
  let quals, qdeps =
    Map.Poly.fold term_map ~init:(quals, hspace.qdeps)
      ~f:(fun ~key:sort ~data:terms (quals, qdeps) ->
        match sort with
        | T_dt.SDT _ ->
            let quals', qdeps' = DtTheory.qualifiers_of sort terms in
            (Set.union quals' quals, Map.force_merge qdeps qdeps')
        | T_array.SArray _ ->
            ( ArrayTheory.qualifiers_of sort terms,
              qdeps (* TODO: Update param qdeps for array quals*) )
        | T_bool.SBool ->
            let quals', qdeps' = bool_quals_of terms hspace.params in
            (Set.union quals' quals, Map.force_merge qdeps qdeps')
        | T_int.SInt | T_real.SReal | T_tuple.STuple _ (*ToDo*)
        | Sort.SArrow _ (*ToDo*) ->
            (quals, qdeps)
        | _ ->
            (*print_endline ("@" ^ Term.str_of_sort sort);*)
            ( Set.Poly.of_list
              @@ List.map ~f:Formula.mk_atom
              @@ T_bool.mk_eqs (fst @@ List.unzip @@ Set.to_list terms),
              qdeps (*ToDo*) ))
  in
  {
    hspace with
    depth;
    quals =
      Set.Poly.map quals
        ~f:Evaluator.(simplify >> Normalizer.normalize >> simplify);
    qdeps;
    terms = int_real_terms_of term_map hspace.params;
  }
