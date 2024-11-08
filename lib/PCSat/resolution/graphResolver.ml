open Core
open Common
open Common.Ext
open Ast
open Ast.LogicOld
open PCSatCommon

module Make
    (Config : SMTResolver.Config.ConfigType)
    (APCSP : PCSP.Problem.ProblemType) : sig
  val run_phase : int -> State.u -> State.u Or_error.t
end = struct
  let config = Config.config
  let id = PCSP.Problem.id_of APCSP.problem

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_id id
  let old_dpos = ref Set.Poly.empty
  let old_dneg = ref Set.Poly.empty
  let old_und = ref Set.Poly.empty
  let insert_source src = Option.map ~f:(fun a -> (a, src))

  let src_exs_of (hide_und : bool) =
    Set.Poly.map ~f:(fun ex -> (ex, [ (ClauseGraph.mk_example ex, hide_und) ]))

  let src_cls_of (hide_und : bool) =
    Set.Poly.map ~f:(fun cl -> (cl, [ (ClauseGraph.mk_clause cl, hide_und) ]))

  exception E

  let unifiable = function
    | Atom.True _, Atom.True _ | False _, False _ -> Some (Formula.mk_true ())
    | App (pred, terms, _), App (pred', terms', _)
      when Stdlib.( = ) pred pred' && List.length terms = List.length terms'
      -> (
        try
          Some
            (Formula.and_of
            @@ List.filter_map (List.zip_exn terms terms') ~f:(function
                 | FunApp (T_int.Int n1, [], _), FunApp (T_int.Int n2, [], _) ->
                     if Z.Compare.( = ) n1 n2 then None else raise E
                 | FunApp (T_real.Real r1, [], _), FunApp (T_real.Real r2, [], _)
                   ->
                     if Q.( = ) r1 r2 then None else raise E
                 | ( FunApp (T_bool.Formula (Formula.Atom (atm1, _)), [], _),
                     FunApp (T_bool.Formula (Formula.Atom (atm2, _)), [], _) )
                   when (Atom.is_true atm1 || Atom.is_false atm1)
                        && (Atom.is_true atm2 || Atom.is_false atm2) ->
                     if
                       (Atom.is_true atm1 && Atom.is_true atm2)
                       || (Atom.is_false atm1 && Atom.is_false atm2)
                     then None
                     else raise E
                 | t1, t2 -> Some (Formula.eq t1 t2)))
        with E -> None)
    | _ -> None

  let contradicts ~dpos ~dneg ~graph fenv exi_senv
      (((uni_senv, c_pos, c_neg, c_phi), source), params, theta) =
    ignore graph;
    try
      (*Debug.print @@ lazy ("  checking contradiction: " ^ Clause.str_of exi_senv (uni_senv, c_pos, c_neg, c_phi));*)
      let positive =
        Set.Poly.filter_map dpos
          ~f:(fun (e, (src : (ClauseGraph.vertex * bool) list)) ->
            insert_source src @@ ExClause.old_atom_of_uclause e)
      in
      let negative =
        Set.Poly.filter_map dneg
          ~f:(fun (e, (src : (ClauseGraph.vertex * bool) list)) ->
            insert_source src @@ ExClause.old_atom_of_uclause e)
      in
      let eqs, srcs =
        Set.union
          (Set.Poly.map c_pos ~f:(fun atm ->
               let xs, srcs =
                 Set.Poly.filter_map negative
                   ~f:(fun
                       (neg_atm, (src : (ClauseGraph.vertex * bool) list)) ->
                     let _param_senv (*ToDo*), atm' =
                       Atom.refresh_tvar neg_atm
                     in
                     insert_source src
                     @@ unifiable
                          ( Logic.ExtTerm.to_old_atom exi_senv uni_senv atm [],
                            atm' ))
                 |> Set.to_list |> List.unzip
               in
               if List.is_empty xs then raise E
               else (Formula.or_of xs, List.concat srcs)))
          (Set.Poly.map c_neg ~f:(fun atm ->
               let xs, srcs =
                 Set.Poly.filter_map positive ~f:(fun (pos_atm, src) ->
                     let _param_senv (*ToDo*), atm' =
                       Atom.refresh_tvar pos_atm
                     in
                     insert_source src
                     @@ unifiable
                          ( Logic.ExtTerm.to_old_atom exi_senv uni_senv atm [],
                            atm' ))
                 |> Set.to_list |> List.unzip
               in
               if List.is_empty xs then raise E
               else (Formula.or_of xs, List.concat srcs)))
        |> Set.to_list |> List.unzip
      in
      let srcs = List.concat srcs in
      let phi =
        Formula.and_of
        @@ Formula.mk_neg (Logic.ExtTerm.to_old_fml exi_senv (uni_senv, c_phi))
           :: eqs
      in
      let fvs = Formula.term_sort_env_of phi in
      let bvs =
        Set.filter fvs ~f:(fun (x, _) -> not @@ Map.Poly.mem exi_senv x)
      in
      let cond =
        Formula.exists (Set.to_list bvs)
          phi (* unbound variables are non-predicate function variables *)
      in
      (*Debug.print @@ lazy ("    sufficient condition: " ^ Formula.str_of cond ^ " is valid?");*)
      insert_source (source @ srcs)
      @@
      if Set.eqlen fvs bvs then
        (* without non-predicate function variables*)
        match Z3Smt.Z3interface.check_sat ~id fenv [ phi ] with
        | `Sat model ->
            (*Debug.print @@ lazy "    yes";*)
            let sub =
              LogicOld.remove_dontcare ~freshvar:true model
              |> Map.Poly.of_alist_exn
            in
            let theta = Map.Poly.map theta ~f:(Term.subst sub) in
            Some
              (Map.Poly.merge sub theta ~f:(fun ~key:_x -> function
                 | `Left v | `Right v -> Some v
                 | `Both (v1, v2) ->
                     if Stdlib.(v1 = v2) then Some v1
                     else
                       (*failwith (Ident.name_of_tvar x ^ ":" ^ LogicOld.Term.str_of v1 ^ ":" ^ LogicOld.Term.str_of v2)*)
                       raise E))
        | _ -> (*Debug.print @@ lazy "    no";*) None
      else if Set.is_empty (Set.inter (Set.Poly.map ~f:fst bvs) params) then
        (* with function variables and without parameters *)
        if Evaluator.is_valid (Z3Smt.Z3interface.is_valid ~id fenv) cond then
          (*let _ = Debug.print @@ lazy "    yes" in*) Some theta
        else (*let _ = Debug.print @@ lazy "    no" in*) None
      else None
    with E -> (*Debug.print @@ lazy "    unification failed";*)
              None

  let contradicts_assuming_pos ~dpos ~dneg ~graph fenv exi_senv cs
      ((param_senv, atm), source) =
    let params =
      Set.filter ~f:(Fn.non @@ Map.Poly.mem exi_senv) @@ Atom.fvs_of atm
    in
    ClauseGraph.resolve_one_step_all
      ~print:(fun _ -> () (*Debug.print*))
      (Set.Poly.singleton
         ( (Logic.of_old_sort_env_map param_senv, Logic.ExtTerm.of_old_atom atm),
           source ))
      Set.Poly.empty exi_senv cs
    |> Set.find_map ~f:(fun (c, sub) ->
           contradicts ~dpos ~dneg ~graph fenv exi_senv
             (c, params, Map.Poly.filter_keys sub ~f:(Set.mem params)))

  let contradicts_assuming_neg ~dpos ~dneg ~graph fenv exi_senv cs
      ((param_senv, atm), source) =
    let params =
      Set.filter ~f:(Fn.non @@ Map.Poly.mem exi_senv) @@ Atom.fvs_of atm
    in
    ClauseGraph.resolve_one_step_all
      ~print:(fun _ -> () (*Debug.print*))
      Set.Poly.empty
      (Set.Poly.singleton
         ( (Logic.of_old_sort_env_map param_senv, Logic.ExtTerm.of_old_atom atm),
           source ))
      exi_senv cs
    |> Set.find_map ~f:(fun (c, sub) ->
           contradicts ~dpos ~dneg ~graph fenv exi_senv
             (c, params, Map.Poly.filter_keys sub ~f:(Set.mem params)))

  let prove ~dpos ~dneg ~graph fenv exi_senv cs ((param_senv, atm), source) =
    match
      contradicts_assuming_neg ~dpos ~dneg ~graph fenv exi_senv cs
        ((param_senv, atm), source)
    with
    | Some (sub, source') ->
        Debug.print
        @@ lazy
             ("  added as a positive example with: "
             ^ LogicOld.TermSubst.str_of sub);
        let unknowns = Map.key_set exi_senv in
        let cl =
          ExClause.normalize_params unknowns
          @@ ExClause.mk_unit_pos
          @@ ExAtom.of_old_atom exi_senv (Formula.mk_true ())
          @@ Atom.subst sub atm
        in
        Debug.print @@ lazy ("  add positive example " ^ ExClause.str_of cl);
        Set.add dpos (cl, source')
    | None -> dpos

  let refute ~dpos ~dneg ~graph fenv exi_senv cs ((param_senv, atm), source) =
    match
      contradicts_assuming_pos ~dpos ~dneg ~graph fenv exi_senv cs
        ((param_senv, atm), source)
    with
    | Some (sub, source') ->
        Debug.print
        @@ lazy
             ("  added as a negative example with: "
             ^ LogicOld.TermSubst.str_of sub);
        let unknowns = Map.key_set exi_senv in
        let cl =
          ExClause.normalize_params unknowns
          @@ ExClause.mk_unit_neg
          @@ ExAtom.of_old_atom exi_senv (Formula.mk_true ())
          @@ Atom.subst sub atm
        in
        Debug.print @@ lazy ("  add negative example " ^ ExClause.str_of cl);
        Set.add dneg (cl, source')
    | None -> dneg

  let acquire_papp ~graph fenv parametric ucs pure atm =
    ignore graph;
    let x, _, ts, _ = Atom.let_pvar_app atm in
    Debug.print @@ lazy ("checking " ^ Atom.str_of ~priority:0 atm);
    let enforce_new, srcs =
      if config.enforce_new then
        (fun (phis, srcs) -> (Formula.and_of phis, List.concat srcs))
        @@ List.unzip @@ Set.to_list
        @@ Set.Poly.map
             (Set.Poly.filter_map ucs ~f:(fun (ex, src) ->
                  insert_source src @@ ExClause.papp_of_uclause ex))
             ~f:(fun (((y, _), ts'), src) ->
               if Stdlib.(x = y) then
                 ( Formula.or_of
                     (List.map2_exn ts ts' ~f:(fun t t' ->
                          (*ToDo: here t' is assumed to have no variable*)
                          assert (Set.is_empty @@ Term.tvs_of t');
                          Formula.mk_atom (T_bool.mk_neq t t'))),
                   src )
               else (Formula.mk_true (), []))
      else (Formula.mk_true (), [])
    in
    match
      Z3Smt.Z3interface.check_sat ~id fenv [ Formula.mk_neg pure; enforce_new ]
    with
    | `Sat model ->
        Some
          ( LogicOld.remove_dontcare ~freshvar:parametric model
            |> Map.Poly.of_alist_exn,
            srcs )
    | _ -> None

  let acquire fenv exi_senv ~dpos ~dneg ~und ~graph cs =
    if Set.is_empty cs then (dpos, dneg, und)
    else (
      Debug.print @@ lazy "********** one-step resolved constraints ***********";
      Debug.print
      @@ lazy
           (PCSP.Problem.str_of
              (PCSP.Problem.of_clauses ~params:(PCSP.Params.make exi_senv)
              @@ Set.Poly.map ~f:fst cs));
      Debug.print @@ lazy "";
      Set.fold cs ~init:(dpos, dneg, und)
        ~f:(fun (dpos, dneg, und) ((uni_senv, pos, neg, pure), source) ->
          match (Set.to_list pos, Set.to_list neg) with
          | [ atm ], [] | [], [ atm ] ->
              let atm = Logic.ExtTerm.to_old_atom exi_senv uni_senv atm [] in
              let pure = Logic.ExtTerm.to_old_fml exi_senv (uni_senv, pure) in
              let tvs = Set.union (Atom.tvs_of atm) (Formula.tvs_of pure) in
              let fnvs = Set.inter tvs (Map.key_set exi_senv) in
              (* if Set.exists (Set.Poly.union_list [Formula.pvs_of pure;Atom.pvs_of atm] |> Set.Poly.map ~f:Ident.pvar_to_tvar) ~f:(PCSP.Problem.is_ne_pred APCSP.problem) || true then
                 dpos, dneg, und
                 else *)
              if Set.is_empty fnvs then (
                (* without function variables *)
                let parametric =
                  config.parametric_examples && Fn.non Set.is_empty tvs
                in
                if Set.is_empty neg then (
                  if
                    (* positive unit clause *)
                    parametric && config.add_unit_clause_as_is
                  then assert false
                  else
                    match acquire_papp ~graph fenv parametric dpos pure atm with
                    | None -> (dpos, dneg, und)
                    | Some (sub, src) ->
                        Debug.print
                        @@ lazy
                             ("  added as a positive example with: "
                             ^ LogicOld.TermSubst.str_of sub);
                        let unknowns = Map.key_set exi_senv in
                        let cl =
                          ExClause.normalize_params unknowns
                          @@ ExClause.mk_unit_pos
                          @@ ExAtom.of_old_atom exi_senv (Formula.mk_true ())
                          @@ Atom.subst sub atm
                        in
                        (Set.add dpos (cl, src @ source), dneg, und))
                else if
                  (* negative unit clause *)
                  parametric && config.add_unit_clause_as_is
                then assert false
                else
                  match acquire_papp ~graph fenv parametric dneg pure atm with
                  | None -> (dpos, dneg, und)
                  | Some (sub, src) ->
                      Debug.print
                      @@ lazy
                           ("  added as a negative example with: "
                           ^ LogicOld.TermSubst.str_of sub);
                      let unknowns = Map.key_set exi_senv in
                      let cl =
                        ExClause.normalize_params unknowns
                        @@ ExClause.mk_unit_neg
                        @@ ExAtom.of_old_atom exi_senv (Formula.mk_true ())
                        @@ Atom.subst sub atm
                      in
                      (dpos, Set.add dneg (cl, src @ source), und))
              else (* with function variables *) (dpos, dneg, und)
          | [], [] -> (
              let pure = Logic.ExtTerm.to_old_fml exi_senv (uni_senv, pure) in
              let tvs = Formula.tvs_of pure in
              let fnvs = Set.inter tvs (Map.key_set exi_senv) in
              if Set.is_empty fnvs then
                (* without function variables *)
                (dpos, dneg, und)
              else
                (* with function variables *)
                match
                  ExClause.make exi_senv Set.Poly.empty Set.Poly.empty pure
                with
                | None -> (dpos, dneg, und)
                | Some cl ->
                    let unknowns = Map.key_set exi_senv in
                    ( dpos,
                      dneg,
                      (*ToDo*)
                      Set.add und (ExClause.normalize_params unknowns cl, source)
                    ))
          | _, _ -> (dpos, dneg, und)))

  let resolve e =
    let open State.Monad_infix in
    Ok e >>=? fun vs _a ->
    let dpos0, dneg0, und0 = VersionSpace.pos_neg_und_examples_of vs in
    let d_dpos = Set.diff dpos0 !old_dpos in
    let d_dneg = Set.diff dneg0 !old_dneg in
    let d_und = Set.diff und0 !old_und in
    let fenv = VersionSpace.fenv_of vs in
    old_dpos := dpos0;
    old_dneg := dneg0;
    old_und := und0;
    let clauses =
      Set.union
        (PCSP.Problem.clauses_of APCSP.problem)
        (VersionSpace.learned_clauses_of vs
        |> Hash_set.to_list |> Set.Poly.of_list)
    in
    let cs = clauses |> src_cls_of false in
    let exi_senv = PCSP.Problem.senv_of APCSP.problem in
    let graph = (VersionSpace.example_graph_of vs).graph in
    let dpos, dneg =
      let to_be_refuted, to_be_proved =
        let to_be_refuted, to_be_proved =
          if config.refute then
            ( Set.Poly.filter_map
                (if config.only_diff then d_dpos else dpos0)
                ~f:(fun c ->
                  ExAtom.to_old_atom @@ ExClause.exatom_of_uclause c
                  |> Option.map ~f:(fun a ->
                         (a, [ (ClauseGraph.mk_example c, false) ]))),
              Set.Poly.filter_map
                (if config.only_diff then d_dneg else dneg0)
                ~f:(fun c ->
                  ExAtom.to_old_atom @@ ExClause.exatom_of_uclause c
                  |> Option.map ~f:(fun a ->
                         (a, [ (ClauseGraph.mk_example c, false) ]))) )
          else (Set.Poly.empty, Set.Poly.empty)
        in
        if config.decide then
          let atms =
            Set.Poly.filter_map ~f:(fun (a, c) ->
                Option.map ~f:(fun a -> (a, c)) @@ ExAtom.to_old_atom a)
            @@ Set.concat_map ~f:(fun c ->
                   ExClause.exatoms_of c
                   |> Set.Poly.map ~f:(fun a ->
                          (a, [ (ClauseGraph.mk_example c, false) ])))
            @@
            (* Set.filter ~f:(fun ex ->
                Debug.print @@ lazy ("decide:" ^ ExClause.str_of ex);
                let pvs = ExClause.pvs_of ex |> Set.Poly.map ~f:Ident.pvar_to_tvar in
                not @@ Set.exists pvs ~f:(PCSP.Problem.is_ne_pred APCSP.problem)) @@ *)
            if config.only_diff then d_und else und0
          in
          (Set.union to_be_refuted atms, Set.union to_be_proved atms)
        else (to_be_refuted, to_be_proved)
      in
      let bvs = Map.key_set exi_senv in
      Set.union
        (Set.Poly.map ~f:(fun a -> (false, a))
        @@ ExAtomSet.reduce_with_source bvs to_be_refuted)
        (Set.Poly.map ~f:(fun a -> (true, a))
        @@ ExAtomSet.reduce_with_source bvs to_be_proved)
      |> Set.Poly.map ~f:(fun (b, ((param_senv, atm), source)) ->
             (Map.Poly.length param_senv, b, ((param_senv, atm), source)))
      |> Set.to_list
      |> List.sort ~compare:(fun (n1, _, _) (n2, _, _) -> n2 - n1)
      |> List.fold
           ~init:(src_exs_of false dpos0, src_exs_of false dneg0)
           ~f:(fun (dpos, dneg) (_, b, ((param_senv, atm), source)) ->
             if b then (
               Debug.print
               @@ lazy
                    ("proving "
                    ^ Formula.str_of
                        ((*Formula.exists (Set.to_list @@ Atom.term_sort_env_of atm) @@*)
                         Formula.mk_atom atm));
               ( prove ~dpos ~dneg ~graph fenv exi_senv cs
                   ((param_senv, atm), source),
                 dneg ))
             else (
               Debug.print
               @@ lazy
                    ("refuting "
                    ^ Formula.str_of
                        ((*Formula.forall (Set.to_list @@ Atom.term_sort_env_of atm) @@*)
                         Formula.mk_atom atm));
               ( dpos,
                 refute ~dpos ~dneg ~graph fenv exi_senv cs
                   ((param_senv, atm), source) )))
    in
    let dpos, dneg, und =
      (* if not config.acquire_und then dpos, dneg, und0 else *)
      (if config.only_diff then d_und else und0)
      |> src_exs_of true
      |> ExClauseSet.refresh_params_with_src exi_senv
      |> ClauseGraph.to_clause_set_with_src exi_senv
      |> ClauseGraph.resolve_one_step_all
           ~print:(fun _ -> () (*Debug.print*))
           (Set.Poly.filter_map dpos ~f:(fun (ex, src) ->
                insert_source src @@ ExClause.atom_of_uclause ex))
           (Set.Poly.filter_map dneg ~f:(fun (ex, src) ->
                insert_source src @@ ExClause.atom_of_uclause ex))
           exi_senv
      |> Set.Poly.map ~f:fst
      |> ClauseGraph.simplify_with
           (Set.Poly.filter_map dpos ~f:(fun (ex, src) ->
                insert_source src @@ ExClause.atom_of_uclause ex))
           (Set.Poly.filter_map dneg ~f:(fun (ex, src) ->
                insert_source src @@ ExClause.atom_of_uclause ex))
      |> acquire fenv exi_senv ~dpos ~dneg ~und:(src_exs_of true und0) ~graph
    in
    let dpos, dneg, und =
      (if config.acquire_org then cs else Set.Poly.empty)
      |> ClauseGraph.resolve_one_step_all
           ~print:(fun _ -> () (*Debug.print*))
           (Set.Poly.filter_map dpos ~f:(fun (ex, src) ->
                insert_source src @@ ExClause.atom_of_uclause ex))
           (Set.Poly.filter_map dneg ~f:(fun (ex, src) ->
                insert_source src @@ ExClause.atom_of_uclause ex))
           exi_senv
      |> Set.Poly.map ~f:fst
      |> Set.union
           (if config.unit_prop then
              Set.filter cs ~f:(fun (cl, _c) -> Clause.is_unit cl)
            else Set.Poly.empty)
      |> ClauseGraph.simplify_with
           (Set.Poly.filter_map dpos ~f:(fun (ex, src) ->
                insert_source src @@ ExClause.atom_of_uclause ex))
           (Set.Poly.filter_map dneg ~f:(fun (ex, src) ->
                insert_source src @@ ExClause.atom_of_uclause ex))
      |> acquire fenv exi_senv ~dpos ~dneg ~und ~graph
    in
    let added =
      Set.diff
        (Set.Poly.map ~f:fst @@ Set.Poly.union_list [ dpos; dneg; und ])
        (Set.Poly.union_list [ dpos0; dneg0; und0 ])
    in
    Debug.print @@ lazy "*** Example Instances obtained by Resolution:";
    Debug.print
    @@ lazy
         (String.concat_map_list ~sep:";\n" ~f:ExClause.str_of
         @@ Set.to_list added);
    Debug.print @@ lazy "";
    Ok (State.of_examples vs @@ Set.Poly.union_list [ dpos; dneg; und ])

  let run_phase _iters = resolve
end
