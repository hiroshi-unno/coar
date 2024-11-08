open Core
open Common
open Common.Ext
open Ast
open Ast.LogicOld
open PCSatCommon

module Config = struct
  type t = {
    verbose : bool;
    only_diff : bool;  (** use only newly added positive/negative examples *)
    refute : bool;  (** try to refute existing positive/negative examples *)
    decide : bool;  (** try to decide undecided atoms *)
    acquire_und : bool;
        (** try to acquire new positive/negative examples from undecided examples *)
    acquire_org : bool;
        (** try to acquire new positive/negative examples from original constraints *)
    unit_prop : bool;  (** perform unit propagation *)
    enforce_new : bool;
    parametric_examples : bool;
    add_unit_clause_as_is : bool;
  }
  [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  let instantiate_ext_files cfg = Ok cfg
end

module Make
    (Config : Config.ConfigType)
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

  exception E

  let unifiable =
    let open Atom in
    function
    | True _, True _ | False _, False _ -> Some (Formula.mk_true ())
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

  let contradicts ~dpos ~dneg fenv exi_senv
      ((uni_senv, c_pos, c_neg, c_phi), params, theta) =
    try
      (*Debug.print @@ lazy ("  checking contradiction: " ^ Clause.str_of exi_senv (uni_senv, c_pos, c_neg, c_phi));*)
      let positive = Set.Poly.filter_map ~f:ExClause.old_atom_of_uclause dpos in
      let negative = Set.Poly.filter_map ~f:ExClause.old_atom_of_uclause dneg in
      let eqs =
        Set.union
          (Set.Poly.map c_pos ~f:(fun atm ->
               let xs =
                 Set.Poly.filter_map negative ~f:(fun neg_atm ->
                     let _param_senv (*ToDo*), atm' =
                       Atom.refresh_tvar neg_atm
                     in
                     unifiable
                       (Logic.ExtTerm.to_old_atom exi_senv uni_senv atm [], atm'))
                 |> Set.to_list
               in
               if List.is_empty xs then raise E else Formula.or_of xs))
          (Set.Poly.map c_neg ~f:(fun atm ->
               let xs =
                 Set.Poly.filter_map positive ~f:(fun pos_atm ->
                     let _param_senv (*ToDo*), atm' =
                       Atom.refresh_tvar pos_atm
                     in
                     unifiable
                       (Logic.ExtTerm.to_old_atom exi_senv uni_senv atm [], atm'))
                 |> Set.to_list
               in
               if List.is_empty xs then raise E else Formula.or_of xs))
        |> Set.to_list
      in
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

  let contradicts_assuming_pos ~dpos ~dneg fenv exi_senv cs (param_senv, atm) =
    let params =
      Set.filter ~f:(Fn.non @@ Map.Poly.mem exi_senv) @@ Atom.fvs_of atm
    in
    ClauseSet.resolve_one_step_all ~print:Debug.print
      (Set.Poly.singleton
         (Logic.of_old_sort_env_map param_senv, Logic.ExtTerm.of_old_atom atm))
      Set.Poly.empty exi_senv cs
    |> Set.find_map ~f:(fun (c, sub) ->
           contradicts ~dpos ~dneg fenv exi_senv
             (c, params, Map.Poly.filter_keys sub ~f:(Set.mem params)))

  let contradicts_assuming_neg ~dpos ~dneg fenv exi_senv cs (param_senv, atm) =
    let params =
      Set.filter ~f:(Fn.non @@ Map.Poly.mem exi_senv) @@ Atom.fvs_of atm
    in
    ClauseSet.resolve_one_step_all ~print:Debug.print Set.Poly.empty
      (Set.Poly.singleton
         ( Map.Poly.map param_senv ~f:Logic.ExtTerm.of_old_sort,
           Logic.ExtTerm.of_old_atom atm ))
      exi_senv cs
    |> Set.find_map ~f:(fun (c, sub) ->
           contradicts ~dpos ~dneg fenv exi_senv
             (c, params, Map.Poly.filter_keys sub ~f:(Set.mem params)))

  let acquire_papp fenv parametric ucs pure atm =
    let x, _, ts, _ = Atom.let_pvar_app atm in
    Debug.print @@ lazy ("checking " ^ Atom.str_of ~priority:0 atm);
    let enforce_new =
      if config.enforce_new then
        Formula.and_of @@ Set.to_list
        @@ Set.Poly.map (Set.Poly.filter_map ucs ~f:ExClause.papp_of_uclause)
             ~f:(fun ((y, _), ts') ->
               if Stdlib.(x = y) then
                 Formula.or_of
                   (List.map2_exn ts ts' ~f:(fun t t' ->
                        (*ToDo: here t' is assumed to have no variable*)
                        assert (Set.is_empty @@ Term.tvs_of t');
                        Formula.mk_atom (T_bool.mk_neq t t')))
               else Formula.mk_true ())
      else Formula.mk_true ()
    in
    match
      Z3Smt.Z3interface.check_sat ~id fenv [ Formula.mk_neg pure; enforce_new ]
    with
    | `Sat model ->
        Some
          (LogicOld.remove_dontcare ~freshvar:parametric model
          |> Map.Poly.of_alist_exn)
    | _ -> None

  let acquire fenv exi_senv ~dpos ~dneg ~und cs =
    if Set.is_empty cs then (dpos, dneg, und)
    else (
      Debug.print @@ lazy "********** one-step resolved constraints ***********";
      Debug.print
      @@ lazy
           (PCSP.Problem.str_of
              (PCSP.Problem.of_clauses ~params:(PCSP.Params.make exi_senv) cs));
      Debug.print @@ lazy "";
      let unknowns = Map.key_set exi_senv in
      Set.fold cs ~init:(dpos, dneg, und)
        ~f:(fun (dpos, dneg, und) (uni_senv, pos, neg, pure) ->
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
                    match acquire_papp fenv parametric dpos pure atm with
                    | None -> (dpos, dneg, und)
                    | Some sub ->
                        Debug.print
                        @@ lazy
                             ("  added as a positive example with: "
                             ^ LogicOld.TermSubst.str_of sub);
                        let cl =
                          ExClause.normalize_params unknowns
                          @@ ExClause.mk_unit_pos
                          @@ ExAtom.of_old_atom exi_senv (Formula.mk_true ())
                          @@ Atom.subst sub atm
                        in
                        (Set.add dpos cl, dneg, und))
                else if
                  (* negative unit clause *)
                  parametric && config.add_unit_clause_as_is
                then assert false
                else
                  match acquire_papp fenv parametric dneg pure atm with
                  | None -> (dpos, dneg, und)
                  | Some sub ->
                      Debug.print
                      @@ lazy
                           ("  added as a negative example with: "
                           ^ LogicOld.TermSubst.str_of sub);
                      let cl =
                        ExClause.normalize_params unknowns
                        @@ ExClause.mk_unit_neg
                        @@ ExAtom.of_old_atom exi_senv (Formula.mk_true ())
                        @@ Atom.subst sub atm
                      in
                      (dpos, Set.add dneg cl, und))
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
                    ( dpos,
                      dneg,
                      (*ToDo*)
                      Set.add und (ExClause.normalize_params unknowns cl) ))
          | _, _ -> (dpos, dneg, und)))

  let prove ~dpos ~dneg fenv exi_senv cs (param_senv, atm) =
    match
      contradicts_assuming_neg ~dpos ~dneg fenv exi_senv cs (param_senv, atm)
    with
    | Some sub ->
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
        Set.add dpos cl
    | None -> dpos

  let refute ~dpos ~dneg fenv exi_senv cs (param_senv, atm) =
    match
      contradicts_assuming_pos ~dpos ~dneg fenv exi_senv cs (param_senv, atm)
    with
    | Some sub ->
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
        Set.add dneg cl
    | None -> dneg

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
    (* Debug.print @@ lazy "********** examples ***********";
       Debug.print @@ lazy (ExClauseSet.str_of dpos0);
       Debug.print @@ lazy (ExClauseSet.str_of dneg0);
       Debug.print @@ lazy (ExClauseSet.str_of und0); *)
    let cs = PCSP.Problem.clauses_of APCSP.problem in
    let exi_senv = PCSP.Problem.senv_of APCSP.problem in
    let dpos, dneg =
      let to_be_refuted, to_be_proved =
        let to_be_refuted, to_be_proved =
          if config.refute then
            ( Set.Poly.filter_map
                (if config.only_diff then d_dpos else dpos0)
                ~f:(fun c -> ExAtom.to_old_atom @@ ExClause.exatom_of_uclause c),
              Set.Poly.filter_map
                (if config.only_diff then d_dneg else dneg0)
                ~f:(fun c -> ExAtom.to_old_atom @@ ExClause.exatom_of_uclause c)
            )
          else (Set.Poly.empty, Set.Poly.empty)
        in
        if config.decide then
          let atms =
            Set.Poly.filter_map ~f:ExAtom.to_old_atom
            @@ Set.concat_map ~f:ExClause.exatoms_of
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
        @@ ExAtomSet.reduce bvs to_be_refuted)
        (Set.Poly.map ~f:(fun a -> (true, a))
        @@ ExAtomSet.reduce bvs to_be_proved)
      |> Set.Poly.map ~f:(fun (b, (param_senv, atm)) ->
             (Map.Poly.length param_senv, b, (param_senv, atm)))
      |> Set.to_list
      |> List.sort ~compare:(fun (n1, _, _) (n2, _, _) -> n2 - n1)
      |> List.fold ~init:(dpos0, dneg0)
           ~f:(fun (dpos, dneg) (_, b, (param_senv, atm)) ->
             if b then (
               Debug.print
               @@ lazy
                    ("proving "
                    ^ Formula.str_of
                        ((*Formula.exists (Set.to_list @@ Atom.term_sort_env_of atm) @@*)
                         Formula.mk_atom atm));
               (prove ~dpos ~dneg fenv exi_senv cs (param_senv, atm), dneg))
             else (
               Debug.print
               @@ lazy
                    ("refuting "
                    ^ Formula.str_of
                        ((*Formula.forall (Set.to_list @@ Atom.term_sort_env_of atm) @@*)
                         Formula.mk_atom atm));
               (dpos, refute ~dpos ~dneg fenv exi_senv cs (param_senv, atm))))
    in
    let dpos, dneg, und =
      if not config.acquire_und then (dpos, dneg, und0)
      else
        (if config.only_diff then d_und else und0)
        |> ExClauseSet.refresh_params exi_senv
        |> ExClauseSet.to_clause_set exi_senv
        |> ClauseSet.resolve_one_step_all ~print:Debug.print
             (Set.Poly.filter_map dpos ~f:ExClause.atom_of_uclause)
             (Set.Poly.filter_map dneg ~f:ExClause.atom_of_uclause)
             exi_senv
        |> Set.Poly.map ~f:fst
        |> ClauseSet.simplify_with
             (Set.Poly.filter_map dpos ~f:ExClause.atom_of_uclause)
             (Set.Poly.filter_map dneg ~f:ExClause.atom_of_uclause)
        |> acquire fenv exi_senv ~dpos ~dneg ~und:und0
    in
    let dpos, dneg, und =
      (if config.acquire_org then cs else Set.Poly.empty)
      |> ClauseSet.resolve_one_step_all ~print:Debug.print
           (Set.Poly.filter_map d_dpos ~f:ExClause.atom_of_uclause)
           (Set.Poly.filter_map d_dneg ~f:ExClause.atom_of_uclause)
           exi_senv
      |> Set.Poly.map ~f:fst
      |> Set.union
           (if config.unit_prop then Set.filter cs ~f:Clause.is_unit
            else Set.Poly.empty)
      |> ClauseSet.simplify_with
           (Set.Poly.filter_map dpos ~f:ExClause.atom_of_uclause)
           (Set.Poly.filter_map dneg ~f:ExClause.atom_of_uclause)
      |> acquire fenv exi_senv ~dpos ~dneg ~und
    in
    let added =
      Set.diff
        (Set.Poly.union_list [ dpos; dneg; und ])
        (Set.Poly.union_list [ dpos0; dneg0; und0 ])
    in
    Debug.print @@ lazy "*** Example Instances obtained by Resolution:";
    Debug.print
    @@ lazy
         (String.concat_set ~sep:";\n" @@ Set.Poly.map ~f:ExClause.str_of added);
    Debug.print @@ lazy "";
    let old_examples = VersionSpace.examples_of vs in
    let new_examples = Set.Poly.union_list [ dpos; dneg; und ] in
    Set.iter (Set.diff old_examples new_examples) ~f:(fun ex ->
        ClauseGraph.hide_vertex (VersionSpace.example_graph_of vs)
        @@ ClauseGraph.mk_example ex);
    let new_examples =
      Set.diff new_examples old_examples
      |> Set.Poly.map ~f:(fun ex -> (ex, [ (ClauseGraph.Dummy, false) ]))
      (*TODO: add sources of new_undecided *)
    in
    Ok (State.of_examples vs new_examples)

  let run_phase _iters = resolve
end
