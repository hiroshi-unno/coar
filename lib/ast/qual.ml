open Core
open Common.Ext
open Common.Combinator
open LogicOld

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
    ~f:(fun ~key:tvar ~data:(param_env, sret, _, _, _) ret ->
      if Ident.is_size_fun_var tvar then ret
      else
        let sargs = List.map ~f:snd param_env in
        Set.union ret @@ Set.Poly.of_list
        @@ List.map ~f:(Term.mk_fvar_app tvar sargs sret)
        @@ List.permutation_without_repetion_of
        @@ List.map param_env ~f:(fun (_, sort) ->
            match Map.Poly.find term_map sort with
            | Some ts -> List.map ~f:fst @@ Set.to_list ts
            | _ -> [ Term.mk_dummy sort ]))

let bool_quals_of terms params =
  let quals, qdeps =
    Set.filter terms ~f:(fun (term, _dep) ->
        match term with
        | Term.Var (x, _, _) ->
            not @@ List.Assoc.mem params ~equal:Stdlib.( = ) x
        | _ -> true)
    |> Set.Poly.map ~f:(fun (t, dep) ->
        QualDep.qual_and_deps_of (Formula.eq t (T_bool.mk_true ())) dep)
    |> Set.to_list
    |> List.map ~f:(fun (qual, dep) -> (qual, (qual, dep)))
    |> List.unzip
  in
  (Set.Poly.of_list quals, Map.Poly.of_alist_exn qdeps)

let add_quals_form_affine_eq_quals quals =
  Set.union quals @@ Set.concat
  @@ Set.Poly.filter_map quals ~f:(fun phi ->
      if Formula.is_atom phi then
        match Formula.let_atom phi with
        | Atom.App (Predicate.Psym T_bool.(Eq | Neq), [ t1; t2 ], _), _
          when AffineTerm.is_affine t1 && (Term.is_int_sort @@ Term.sort_of t1)
          ->
            Option.some @@ Set.Poly.of_list [ Formula.gt t1 t2 ]
        | _ -> None
      else None)

let add_mod_quals_terms quals terms =
  let quals' =
    let rec inner i quals =
      let quals' =
        Set.union quals
        @@ Set.Poly.map quals ~f:(fun qual ->
            Formula.map_term qual ~f:(function
              | Term.FunApp (T_int.Rem modulo, [ t1; t2 ], info) as t
                when T_int.is_int t2 ->
                  let m = Z.to_int (*ToDo*) @@ T_int.let_int t2 in
                  if m > i && m mod i = 0 then
                    Term.FunApp
                      (T_int.Rem modulo, [ t1; T_int.from_int i ], info)
                  else t
              | t -> t))
      in
      if Set.equal quals quals' then quals else inner (i + 1) quals'
    in
    inner 2 quals
  in
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
             (T_int.mk_rem Value.Euclidean (Term.mk_var v s) (T_int.from_int 2))
             (T_int.zero ()))

let mk_eq_quals_for_ith_param params i =
  if i >= List.length params || List.length params <= 1 then Set.Poly.empty
  else
    let vi, si = List.nth_exn params i in
    List.fold params ~init:Set.Poly.empty ~f:(fun acc (v, s) ->
        if Stdlib.(v = vi) || Stdlib.(s <> si) then acc
        else Set.add acc (Formula.eq (Term.mk_var vi si) (Term.mk_var v s)))

let extract_terms_from_quals ~qelim params quals =
  let vret, sret = List.last_exn params in
  let quals_ret, quals_rest =
    Set.partition_tf quals ~f:(fun qual -> Set.mem (Formula.tvs_of qual) vret)
  in
  let termss, quals =
    List.partition_map (Set.to_list quals_ret) ~f:(fun phi ->
        let terms =
          if Term.is_irb_sort sret then
            AffineTerm.extract_terms_from_formula (vret, sret)
              (Evaluator.simplify_term >> Normalizer.normalize_term)
              Normalizer.normalize phi
          else Set.Poly.empty
        in
        if Set.is_empty terms then
          let qual =
            qelim
            @@ Formula.exists [ List.last_exn params ]
            @@ Normalizer.normalize phi
          in
          if Formula.(is_bind qual || is_ground qual) then First Set.Poly.empty
          else Second qual
        else First terms)
  in
  (Set.union quals_rest (Set.Poly.of_list quals), Set.Poly.union_list termss)

let extract_wf_terms_from_quals_terms ~qelim params_x params_y (quals, terms) =
  let rename_y_x = Formula.rename (ren_of_sort_env_list params_y params_x) in
  if false then
    ( Set.concat_map quals ~f:(fun phi ->
          let qual1 = qelim @@ Formula.exists params_y phi in
          let qual2 = qelim @@ Formula.exists params_x phi in
          Set.union
            (if Formula.(is_bind qual1 || is_ground qual1) then Set.Poly.empty
             else Set.Poly.singleton qual1)
            (if Formula.(is_bind qual2 || is_ground qual2) then Set.Poly.empty
             else Set.Poly.singleton (rename_y_x qual2))),
      terms )
  else
    ( Set.Poly.filter_map quals ~f:(fun phi ->
          if Formula.is_ground phi then None
          else
            let fvs = Formula.fvs_of phi in
            if
              Set.is_subset fvs
                ~of_:(Set.Poly.of_list @@ List.map ~f:fst params_x)
            then Some phi
            else if
              Set.is_subset fvs
                ~of_:(Set.Poly.of_list @@ List.map ~f:fst params_y)
            then Some (rename_y_x phi)
            else (* ToDo: use the information about transition predicates *)
              None),
      terms )
