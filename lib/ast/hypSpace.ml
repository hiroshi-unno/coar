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

(* [normalize_memo]: with it set, the normal form every qualifier is given at
   the end of [qualifiers_of] (simplify, normalise, simplify) is kept per
   domain, keyed by the qualifier, and a qualifier met again -- in the next
   unknown's hypothesis space, whose parameters bear the same names, or in the
   next rebuild -- takes the kept form.  The three steps are functions of the
   formula alone (no fresh name is drawn, no solver is asked), so the kept form
   is the one recomputing gives.  Process-wide, only ever switched on. *)
let normalize_memo = Atomic.make false
let normalize_memo_hits = Atomic.make 0
let normalize_memo_misses = Atomic.make 0

let normalize_table : (Formula.t, Formula.t) Hashtbl.t Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> Hashtbl.PolyDeep.create ())

let normal_form_of_qual =
  Evaluator.(simplify >> Normalizer.normalize >> simplify)

let normal_form_of_qual_memo phi =
  if not (Atomic.get normalize_memo) then normal_form_of_qual phi
  else
    let tbl = Stdlib.Domain.DLS.get normalize_table in
    match Hashtbl.find tbl phi with
    | Some q ->
        Atomic.incr normalize_memo_hits;
        q
    | None ->
        Atomic.incr normalize_memo_misses;
        let q = normal_form_of_qual phi in
        Hashtbl.set tbl ~key:phi ~data:q;
        q

let add_term_map term_map term =
  let sort = Term.sort_of term in
  match Map.Poly.find term_map sort with
  | Some terms ->
      Map.Poly.set term_map ~key:sort ~data:(Set.add terms (term, []))
  | None ->
      Map.Poly.add_exn term_map ~key:sort ~data:(Set.Poly.singleton (term, []))

let qualifiers_of ?(add_mod2_quals = false) ?(add_bv_quals = false)
    ?(guarded_partial_selector_quals = false)
    ?(guarded_partial_selector_offset = 0) ?(selector_path_quals = false)
    ?(selector_path_consts = []) ?curried_leaf_reads ?keep_generated
    ?keep_opaque_term ?on_family ~fenv depth hspace =
  (* [keep_generated]: a test every qualifier of the families generated below
     over combinations of reached terms must pass to be offered (the
     qualifiers given in [hspace.quals] are not tested); absent, every one is
     offered.  [keep_opaque_term]: a test every reached term of an opaque
     sort (the sorts of the catch-all case below) must pass to enter the
     pairwise equalities over its sort; absent, every one does.
     [on_family name before after] reports each family as generated
     and as kept, before the normal form, for a census and a test; it changes
     nothing. *)
  let filter_family name quals =
    let kept =
      match keep_generated with
      | None -> quals
      | Some keep -> Set.filter quals ~f:keep
    in
    Option.iter on_family ~f:(fun f -> f name quals kept);
    kept
  in
  let filter_qdeps quals qdeps =
    match keep_generated with
    | None -> qdeps
    | Some _ -> Map.Poly.filter_keys qdeps ~f:(Set.mem quals)
  in
  let terms, quals, qdeps =
    let quals, terms =
      Common.PhaseTime.with_phase "mod-quals" @@ fun () ->
      Qual.add_mod_quals_terms hspace.quals hspace.terms
    in
    let quals =
      Common.PhaseTime.with_phase "affine-eq-quals" @@ fun () ->
      Qual.add_quals_form_affine_eq_quals quals
    in
    let quals =
      if add_mod2_quals then Set.union (Qual.mk_mod_quals hspace.params) quals
      else quals
    in
    let term_map =
      Common.PhaseTime.with_phase "term-map" @@ fun () ->
      let rec aux d term_map =
        if d > depth then term_map
        else
          aux (d + 1)
          @@ Map.Poly.fold term_map ~init:term_map
               ~f:(fun ~key:sort ~data:terms ->
                 match sort with
                 | T_array.SArray _ ->
                     QualArr.update_term_map ~depth:d ?curried_leaf_reads sort
                       terms
                 | T_seq.SSeq _ -> QualSeq.update_term_map ~depth:d sort terms
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
      Common.PhaseTime.with_phase "sort-quals" @@ fun () ->
      Map.Poly.fold term_map ~init:(quals, hspace.qdeps)
        ~f:(fun ~key:sort ~data:terms (quals, qdeps) ->
          match sort with
          | Sort.SArrow _ -> (quals, qdeps)
          | T_bool.SBool ->
              let quals', qdeps' = Qual.bool_quals_of terms hspace.params in
              let quals' = filter_family "bool" quals' in
              let qdeps' = filter_qdeps quals' qdeps' in
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
              let quals' = filter_family "bv" quals' in
              (Set.union quals' quals, qdeps)
          | T_array.SArray _ ->
              let quals' = filter_family "array" @@ QualArr.qualifiers_of sort terms in
              ( Set.union quals' quals,
                qdeps (* TODO: Update param qdeps for array quals *) )
          | T_seq.SSeq _ ->
              let quals' = filter_family "seq" @@ QualSeq.qualifiers_of sort terms in
              (Set.union quals' quals, qdeps)
          | T_tuple.STuple _ -> (quals, qdeps)
          | T_dt.SDT _ ->
              let quals', qdeps' = QualDT.qualifiers_of sort terms in
              let quals' = filter_family "dt" quals' in
              let qdeps' = filter_qdeps quals' qdeps' in
              (* Two datatype sorts can contribute the same qualifier with
                 different dependencies, so the merge must combine rather than
                 refuse: [force_merge] raised [Failure "force_merge"] and ended
                 the run with no verdict.  Conjunction is what the consumer does
                 with the map's values in any case. *)
              ( Set.union quals' quals,
                Map.Poly.merge_skewed qdeps qdeps' ~combine:(fun ~key:_ ->
                    QualDep.merge_dep) )
          | _ ->
              if false then print_endline ("@" ^ Term.str_of_sort sort);
              let terms = List.map ~f:fst @@ Set.to_list terms in
              let terms =
                match keep_opaque_term with
                | None -> terms
                | Some keep -> List.filter terms ~f:keep
              in
              let quals' =
                filter_family "other" @@ Set.Poly.of_list @@ Formula.eqs terms
              in
              (Set.union quals' quals, qdeps (*ToDo*)))
    in
    (* Guarded payload comparisons (see [QualDT.guarded_payload_quals]): they
       carry their tester inside the qualifier, so they need no dependency and
       are added to the qualifiers only, never to [terms], which the affine
       part of a template uses unguarded. *)
    let quals =
      if guarded_partial_selector_quals then
        Set.union quals @@ filter_family "guarded-payload"
        @@ QualDT.guarded_payload_quals
             ~offset:guarded_partial_selector_offset
             ~consts:(Set.to_list hspace.consts)
             hspace.params
      else quals
    in
    (* Cross-parameter and constant comparisons of the integer fields reached
       through total selectors (see [QualDT.selector_path_quals]).  Like the
       guarded payload comparisons they go to the qualifiers only.  The
       constants are the predicate's own together with [selector_path_consts],
       which a caller may fill from the whole problem. *)
    let quals =
      if selector_path_quals then
        Set.union quals @@ filter_family "selector-path"
        @@ QualDT.selector_path_quals ~cross:true
             ~consts:(Set.to_list hspace.consts @ selector_path_consts)
             hspace.params
      else quals
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
      (Common.PhaseTime.with_phase "normalize-quals" @@ fun () ->
       let normal =
         Common.PhaseTime.with_phase "normal-forms" @@ fun () ->
         List.map (Set.to_list quals) ~f:normal_form_of_qual_memo
       in
       Common.PhaseTime.with_phase "set-of-normal-forms" @@ fun () ->
       Set.Poly.of_list normal),
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
