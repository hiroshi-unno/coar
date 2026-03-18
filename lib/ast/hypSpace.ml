open Core
open Common.Ext
open Common.Combinator
open LogicOld

type hspace = {
  depth : int;
  params : sort_env_list;
  consts : Term.t Set.Poly.t;
  terms : Term.t Set.Poly.t;
  quals : Formula.t Set.Poly.t;
  qdeps : (Formula.t, QualDep.t) Map.Poly.t;
}

let add_term_map term_map term =
  let sort = Term.sort_of term in
  match Map.Poly.find term_map sort with
  | Some terms ->
      Map.Poly.set term_map ~key:sort ~data:(Set.add terms (term, []))
  | None ->
      Map.Poly.add_exn term_map ~key:sort ~data:(Set.Poly.singleton (term, []))

let qualifiers_of ?(add_mod2_quals = false) ?(add_bv_quals = false) ~fenv depth
    hspace =
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
                 | T_array.SArray _ ->
                     QualArr.update_term_map ~depth:d sort terms
                 | T_dt.SDT _ -> QualDT.update_term_map ~depth:d sort terms
                 | _ -> Fn.id)
      in
      let term_map =
        Set.fold terms
          ~init:(Qual.split_params_by_theory hspace.params)
          ~f:add_term_map
      in
      Qual.mk_func_app_terms term_map fenv
      |> Set.fold ~init:term_map ~f:add_term_map
      |> aux 0
    in
    let quals, qdeps =
      Map.Poly.fold term_map ~init:(quals, hspace.qdeps)
        ~f:(fun ~key:sort ~data:terms (quals, qdeps) ->
          match sort with
          | Sort.SArrow _ -> (quals, qdeps)
          | T_bool.SBool ->
              let quals', qdeps' = Qual.bool_quals_of terms hspace.params in
              (Set.union quals' quals, Map.force_merge qdeps qdeps')
          | T_int.SInt | T_real.SReal -> (quals, qdeps)
          | T_bv.SBV _ ->
              let quals' =
                Set.Poly.union_list
                @@ List.map hspace.params ~f:(fun (x, s) ->
                       match s with
                       | T_bv.SBV size ->
                           let tx = Term.mk_var x s in
                           Set.Poly.of_list
                           @@ List.map ~f:Formula.mk_atom
                                [
                                  T_bool.mk_eq
                                    ((*lsb*) T_bv.mk_bvextract ~size 0 0 tx)
                                    (T_bv.bvone ~size:(Some 1) ());
                                  T_bool.mk_eq
                                    ((*msb*) let bits = T_bv.bits_of size in
                                     T_bv.mk_bvextract ~size (bits - 1)
                                       (bits - 1) tx)
                                    (T_bv.bvone ~size:(Some 1) ());
                                ]
                           @ (if false then []
                              else (*ToDo: trivial?*)
                                List.map ~f:Formula.mk_atom
                                  [
                                    T_bv.mk_bvleq ~size ~signed:(Some false)
                                      (T_bv.bvmin ~size ~signed:(Some false) ())
                                      tx;
                                    T_bv.mk_bvleq ~size ~signed:(Some false) tx
                                      (T_bv.bvmax ~size ~signed:(Some false) ());
                                    T_bv.mk_bvleq ~size ~signed:(Some true)
                                      (T_bv.bvmin ~size ~signed:(Some true) ())
                                      tx;
                                    T_bv.mk_bvleq ~size ~signed:(Some true) tx
                                      (T_bv.bvmax ~size ~signed:(Some true) ());
                                  ])
                           @ (if not add_bv_quals then []
                              else
                                let bits = T_bv.bits_of size in
                                let half_bits = bits / 2 in
                                let half_size = Some half_bits in
                                if half_bits <= 0 then []
                                else
                                  let zext =
                                    T_bv.mk_bvzext ~size:half_size
                                      (bits - half_bits)
                                  in
                                  let sext =
                                    T_bv.mk_bvsext ~size:half_size
                                      (bits - half_bits)
                                  in
                                  List.map ~f:Formula.mk_atom
                                    [
                                      T_bv.mk_bvgt ~size ~signed:(Some false)
                                        (zext
                                        @@ T_bv.bvmin ~size:half_size
                                             ~signed:(Some false) ())
                                        tx;
                                      T_bv.mk_bvgt ~size ~signed:(Some false) tx
                                        (zext
                                        @@ T_bv.bvmax ~size:half_size
                                             ~signed:(Some false) ());
                                      T_bv.mk_bvgt ~size ~signed:(Some true)
                                        (sext
                                        @@ T_bv.bvmin ~size:half_size
                                             ~signed:(Some true) ())
                                        tx;
                                      T_bv.mk_bvgt ~size ~signed:(Some true) tx
                                        (sext
                                        @@ T_bv.bvmax ~size:half_size
                                             ~signed:(Some true) ());
                                    ])
                           @
                           if not add_bv_quals then []
                           else
                             let bits = T_bv.bits_of size in
                             let half_bits = bits / 2 in
                             let quad_bits = half_bits / 2 in
                             let quad_size = Some quad_bits in
                             if quad_bits <= 0 then []
                             else
                               let zext =
                                 T_bv.mk_bvzext ~size:quad_size
                                   (bits - quad_bits)
                               in
                               let sext =
                                 T_bv.mk_bvsext ~size:quad_size
                                   (bits - quad_bits)
                               in
                               List.map ~f:Formula.mk_atom
                                 [
                                   T_bv.mk_bvgt ~size ~signed:(Some false)
                                     (zext
                                     @@ T_bv.bvmin ~size:quad_size
                                          ~signed:(Some false) ())
                                     tx;
                                   T_bv.mk_bvgt ~size ~signed:(Some false) tx
                                     (zext
                                     @@ T_bv.bvmax ~size:quad_size
                                          ~signed:(Some false) ());
                                   T_bv.mk_bvgt ~size ~signed:(Some true)
                                     (sext
                                     @@ T_bv.bvmin ~size:quad_size
                                          ~signed:(Some true) ())
                                     tx;
                                   T_bv.mk_bvgt ~size ~signed:(Some true) tx
                                     (sext
                                     @@ T_bv.bvmax ~size:quad_size
                                          ~signed:(Some true) ());
                                 ]
                       | _ -> Set.Poly.empty)
              in
              (Set.union quals' quals, qdeps)
          | T_array.SArray _ ->
              let quals' = QualArr.qualifiers_of sort terms in
              ( Set.union quals' quals,
                qdeps (* TODO: Update param qdeps for array quals *) )
          | T_tuple.STuple _ -> (quals, qdeps)
          | T_dt.SDT _ ->
              let quals', qdeps' = QualDT.qualifiers_of sort terms in
              (Set.union quals' quals, Map.force_merge qdeps qdeps')
          | _ ->
              if false then print_endline ("@" ^ Term.str_of_sort sort);
              let quals' =
                Set.Poly.of_list
                @@ Formula.eqs (List.map ~f:fst @@ Set.to_list terms)
              in
              (Set.union quals' quals, qdeps (*ToDo*)))
    in
    let terms =
      Set.Poly.filter_map ~f:(function
        | Term.Var (x, _, _)
          when List.Assoc.mem hspace.params ~equal:Ident.tvar_equal x ->
            None
        | term -> Some term)
      @@ Map.Poly.fold term_map ~init:Set.Poly.empty
           ~f:(fun ~key:sort ~data:terms ret ->
             Set.union ret
               (match sort with
               | T_int.SInt | T_real.SReal | T_bv.SBV _ | T_array.SArray _
               | T_tuple.STuple _ | T_dt.SDT _ ->
                   Set.Poly.map ~f:fst terms
               | _ -> (*ToDo*) Set.Poly.empty))
    in
    ( terms,
      Set.Poly.map quals
        ~f:Evaluator.(simplify >> Normalizer.normalize >> simplify),
      qdeps )
  in
  if false then (
    Set.iter terms ~f:(fun t ->
        print_endline @@ sprintf "term: %s" (Term.str_of t));
    Set.iter quals ~f:(fun q ->
        print_endline @@ sprintf "qual: %s" (Formula.str_of q));
    Set.iter hspace.consts ~f:(fun t ->
        print_endline @@ sprintf "const: %s" (Term.str_of t)));
  { hspace with depth; quals; qdeps; terms }
