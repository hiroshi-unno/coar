open Core
open Common.Ext
open Common.Combinator
open LogicOld

type hspace = {
  depth : int;
  params : sort_env_list;
  quals : Formula.t Set.Poly.t;
  qdeps : (Formula.t, QualDep.t) Map.Poly.t;
  terms : Term.t Set.Poly.t;
  consts : Term.t Set.Poly.t;
}

let add_term_map term_map term =
  let sort = Term.sort_of term in
  match Map.Poly.find term_map sort with
  | Some terms ->
      Map.Poly.set term_map ~key:sort ~data:(Set.add terms (term, []))
  | None ->
      Map.Poly.add_exn term_map ~key:sort ~data:(Set.Poly.singleton (term, []))

let qualifiers_of ?(add_mod2_quals = false) ~fenv depth hspace =
  let terms, quals, qdeps =
    let quals, terms = Qual.add_mod_quals_terms hspace.quals hspace.terms in
    let quals = Qual.add_quals_form_affine_eq_quals quals in
    let quals =
      if add_mod2_quals then Set.union (Qual.mk_mod_quals hspace.params) quals
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
                 | T_dt.SDT _ -> QualDT.update_term_map ~depth:d sort terms
                 | T_array.SArray _ ->
                     QualArr.update_term_map ~depth:d sort terms
                 | _ -> Fn.id)
      in
      let term_map =
        Set.fold terms
          ~init:(Qual.split_params_by_theory hspace.params)
          ~f:add_term_map
      in
      aux 0
      @@ Set.fold ~init:term_map ~f:add_term_map
      @@ Qual.mk_func_app_terms term_map fenv
    in
    let quals, qdeps =
      Map.Poly.fold term_map ~init:(quals, hspace.qdeps)
        ~f:(fun ~key:sort ~data:terms (quals, qdeps) ->
          match sort with
          | T_bool.SBool ->
              let quals', qdeps' = Qual.bool_quals_of terms hspace.params in
              (Set.union quals' quals, Map.force_merge qdeps qdeps')
          | T_int.SInt | T_real.SReal | T_tuple.STuple _ (*ToDo*)
          | Sort.SArrow _ (*ToDo*) ->
              (quals, qdeps)
          | T_dt.SDT _ ->
              let quals', qdeps' = QualDT.qualifiers_of sort terms in
              (Set.union quals' quals, Map.force_merge qdeps qdeps')
          | T_array.SArray _ ->
              let quals' = QualArr.qualifiers_of sort terms in
              ( Set.union quals' quals,
                qdeps (* TODO: Update param qdeps for array quals *) )
          | _ ->
              if false then print_endline ("@" ^ Term.str_of_sort sort);
              ( Set.Poly.of_list
                @@ Formula.eqs (fst @@ List.unzip @@ Set.to_list terms),
                qdeps (*ToDo*) ))
    in
    ( Map.Poly.fold term_map ~init:Set.Poly.empty
        ~f:(fun ~key:sort ~data:terms ret ->
          match sort with
          | T_int.SInt | T_real.SReal ->
              Set.union ret
              @@ Set.Poly.filter_map terms
                   ~f:
                     ( fst >> function
                       | Term.Var (x, _, _)
                         when List.Assoc.mem hspace.params ~equal:Stdlib.( = ) x
                         ->
                           None
                       | term -> Some term )
          | _ -> ret),
      Set.Poly.map quals
        ~f:Evaluator.(simplify >> Normalizer.normalize >> simplify),
      qdeps )
  in
  { hspace with depth; quals; qdeps; terms }
