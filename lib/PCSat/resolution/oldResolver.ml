open Core
open Common
open Common.Ext
open Common.Util
open Ast
open PCSatCommon

module Config = struct
  type t = { verbose : bool } [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  let instantiate_ext_files cfg = Ok cfg

  let load_ext_file = function
    | ExtFile.Filename filename -> (
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x -> instantiate_ext_files x >>= fun x -> Ok (ExtFile.Instance x)
        | Error msg ->
            error_string
            @@ sprintf "Invalid DefaultResolver Configuration (%s): %s" filename
                 msg)
    | Instance x -> Ok (Instance x)
end

module Make
    (Config : Config.ConfigType)
    (APCSP : PCSP.Problem.ProblemType) : sig
  val run_phase : int -> State.u -> State.u Or_error.t
end = struct
  let config = Config.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  open Debug

  let old_dpos = ref Set.Poly.empty
  let old_dneg = ref Set.Poly.empty

  (* Assuming that only papp_x may have term variables. *)
  let unify bvs papp_x papp_c = LogicOld.Atom.unify bvs papp_x papp_c
  (*(* assume that papp_c has no term variable and papp_x is of the form P(x_1,...,x_n) where x_i's are distinct *)
    let unify papp_x papp_c =
    let open Atom in
    match papp_x, papp_c with
    | True _ , True _ | False _, False _ -> Some Map.Poly.empty
    | App (pred, terms, _), App (pred', terms', _)
      when pred = pred' && List.length terms = List.length terms'->
      List.map2_exn ~f:(function Term.Var (tvar, _, _) -> fun t -> tvar, t | _ -> assert false) terms terms'
      |> Map.Poly.of_alist
      |> (function `Ok map -> Some map | _ -> assert false)
    | _ -> assert false*)

  let is_ground_atom exi_senv papp =
    Set.is_subset (Logic.Term.fvs_of papp) ~of_:(Map.key_set exi_senv)

  let refuted phi =
    match Logic.ExtTerm.eval Map.Poly.empty phi with
    | Logic.ExtTerm.BoolLit b -> not b
    | _ -> false
    | exception _ -> false

  let classify_clauses exi_senv =
    Set.fold ~init:(Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)
      ~f:(fun (c0, c1, c0x1) ((_, c_pos, c_neg, _) as c) ->
        let num_of_ground_atoms =
          (Set.length @@ Set.filter ~f:(is_ground_atom exi_senv) c_pos)
          + (Set.length @@ Set.filter ~f:(is_ground_atom exi_senv) c_neg)
        in
        let num_of_non_ground_atoms =
          Set.length c_pos + Set.length c_neg - num_of_ground_atoms
        in
        if num_of_ground_atoms >= 2 then (c0, c1, c0x1)
        else if num_of_ground_atoms = 1 then (c0, Set.add c1 c, c0x1)
        else if num_of_non_ground_atoms = 1 then (c0, c1, Set.add c0x1 c)
        else if num_of_non_ground_atoms = 0 then (c0, c1, c0x1)
        else (Set.add c0 c, c1, c0x1))

  let gen_uclause_c1 exi_senv _undecided c1
      ((pos : ExClauseSet.t), (neg : ExClauseSet.t)) :
      ExClauseSet.t * ExClauseSet.t =
    let is_eligible ex pure withvars =
      let rec inner ex pure withvars =
        match (ex, withvars) with
        | _, [] -> refuted pure
        | [], _ :: _ -> false
        | e :: ex, w :: withvars -> (
            match ExClause.old_atom_of_uclause e with
            | None -> inner ex pure (w :: withvars)
            | Some (_param_senv (*ToDo*), e) -> (
                match
                  unify
                    Set.Poly.empty (*ToDo: is it OK with function varibles?*)
                    (Logic.ExtTerm.to_old_atom exi_senv (*ToDo*) Map.Poly.empty
                       w [])
                    e
                with
                | Some theta ->
                    (* TODO: simplified version *)
                    let theta =
                      Map.Poly.map theta ~f:Logic.ExtTerm.of_old_term
                    in
                    inner ex
                      (Logic.Term.subst theta pure)
                      (List.map ~f:(Logic.Term.subst theta) withvars)
                | None -> inner ex pure (w :: withvars)))
      in
      inner (Set.to_list ex) pure (Set.to_list withvars)
    in
    Set.fold c1 ~init:(pos, neg)
      ~f:(fun (pos, neg) (_c_senv, c_pos, c_neg, c_pure) ->
        let with_tvar_neg =
          Set.filter ~f:(Fn.non @@ is_ground_atom exi_senv) c_neg
        in
        let with_tvar_pos =
          Set.filter ~f:(Fn.non @@ is_ground_atom exi_senv) c_pos
        in
        match Set.find ~f:(is_ground_atom exi_senv) c_pos with
        | None ->
            (* c1 will be a negative unit clause *)
            let candidate = Set.find_exn ~f:(is_ground_atom exi_senv) c_neg in
            if
              is_eligible pos c_pure with_tvar_neg
              && is_eligible neg c_pure with_tvar_pos
            then
              ( pos,
                Set.add neg
                  {
                    positive = Set.Poly.empty;
                    negative =
                      Set.Poly.singleton
                      @@ ExAtom.of_ground_atom
                           (LogicOld.Formula.mk_true ())
                           exi_senv candidate;
                  } )
            else (pos, neg)
        | Some candidate ->
            (* c1 will be a positive unit clause *)
            if
              is_eligible pos c_pure with_tvar_neg
              && is_eligible neg c_pure with_tvar_pos
            then
              ( Set.add pos
                  {
                    positive =
                      Set.Poly.singleton
                      @@ ExAtom.of_ground_atom
                           (LogicOld.Formula.mk_true ())
                           exi_senv candidate;
                    negative = Set.Poly.empty;
                  },
                neg )
            else (pos, neg))

  (* assume that c0x1 has no undecided ground atoms and exactly 1 non-ground atom.  *)
  let gen_uclause_c0x1 exi_senv undecided c0x1
      ((pos : ExClauseSet.t), (neg : ExClauseSet.t)) :
      (ExClauseSet.t * ExClauseSet.t) option =
    let undecided_papps =
      Set.fold ~init:Set.Poly.empty undecided ~f:(fun acc ex ->
          Set.Poly.union_list
            [ acc; ex.ExClause.positive; ex.ExClause.negative ])
    in
    let is_eligible papp pure undecided_app =
      match ExAtom.to_atom undecided_app with
      | None -> false
      | Some (_param_senv (*ToDo*), papp') -> (
          match
            unify Set.Poly.empty (*ToDo: is it OK with function varibles?*)
              (Logic.ExtTerm.to_old_atom exi_senv (*ToDo*) Map.Poly.empty papp
                 [])
              (Logic.ExtTerm.to_old_atom exi_senv (*ToDo*) Map.Poly.empty papp'
                 [])
          with
          | None -> false
          | Some theta ->
              let theta = Map.Poly.map theta ~f:Logic.ExtTerm.of_old_term in
              refuted @@ Logic.Term.subst theta pure)
    in
    Set.fold c0x1
      ~init:(Some (pos, neg))
      ~f:(fun acc (_c_senv, c_pos, c_neg, c_pure) ->
        let open Option in
        match
          ( Set.find ~f:(Fn.non @@ is_ground_atom exi_senv) c_pos,
            Set.find ~f:(Fn.non @@ is_ground_atom exi_senv) c_neg )
        with
        | None, None | Some _, Some _ ->
            failwith "assume that c0x1 has exactly 1 non-ground atom."
        | Some papp, None ->
            (* papp will be positive unit clause *)
            Set.fold undecided_papps ~init:acc ~f:(fun acc undecided ->
                acc >>= fun (pos, neg) ->
                if
                  Set.exists ~f:(is_eligible papp c_pure)
                  @@ ExClauseSet.exatoms_of neg
                then None (* unsat *)
                else if is_eligible papp c_pure undecided then
                  Some (Set.add pos @@ ExClause.mk_unit_pos undecided, neg)
                else acc)
        | None, Some papp ->
            (* papp will be negative unit clause *)
            Set.fold undecided_papps ~init:acc ~f:(fun acc undecided ->
                acc >>= fun (pos, neg) ->
                if
                  Set.exists ~f:(is_eligible papp c_pure)
                  @@ ExClauseSet.exatoms_of pos
                then None
                else if is_eligible papp c_pure undecided then
                  Some (pos, Set.add neg @@ ExClause.mk_unit_neg undecided)
                else acc))

  let rec resolution_loop (dpos, dneg, undecided) exi_senv cs =
    let params = PCSP.Params.make exi_senv in
    print @@ lazy "********** one-step resolved constraints ***********";
    print @@ lazy (PCSP.Problem.str_of (PCSP.Problem.of_clauses ~params cs));
    if Set.is_empty cs || ClauseSet.has_only_pure cs then Some (dpos, dneg)
    else
      cs
      |> ClauseSet.simplify_with
           (Set.Poly.filter_map dpos ~f:ExClause.atom_of_uclause)
           (Set.Poly.filter_map dneg ~f:ExClause.atom_of_uclause)
      |> (fun cs ->
           print @@ lazy "********** simplified constraints ***********";
           print
           @@ lazy (PCSP.Problem.str_of (PCSP.Problem.of_clauses ~params cs));
           cs)
      |> classify_clauses exi_senv
      |> fun (c0, c1, c0x1) ->
      print
      @@ lazy
           ("***** c0\n"
           ^ PCSP.Problem.str_of (PCSP.Problem.of_clauses ~params c0));
      print
      @@ lazy
           ("***** c1\n"
           ^ PCSP.Problem.str_of (PCSP.Problem.of_clauses ~params c1));
      print
      @@ lazy
           ("***** c0x1\n"
           ^ PCSP.Problem.str_of (PCSP.Problem.of_clauses ~params c0x1));
      (dpos, dneg)
      |> gen_uclause_c1 exi_senv undecided c1
      |> gen_uclause_c0x1 exi_senv undecided c0x1
      |> function
      | None -> None
      | Some (dpos', dneg') ->
          let c0' =
            Set.Poly.map ~f:fst
            @@ ClauseSet.resolve_one_step_all ~print:Debug.print
                 (Set.Poly.filter_map dpos' ~f:ExClause.atom_of_uclause)
                 (Set.Poly.filter_map dneg' ~f:ExClause.atom_of_uclause)
                 exi_senv c0
          in
          resolution_loop (dpos', dneg', undecided) exi_senv c0'

  let resolve e =
    let open State.Monad_infix in
    Ok e >>=? fun vs _a ->
    let dpos, dneg, undecided = VersionSpace.pos_neg_und_examples_of vs in
    let d_diff = (Set.diff dpos !old_dpos, Set.diff dneg !old_dneg) in
    old_dpos := dpos;
    old_dneg := dneg;
    print @@ lazy "********** new decided clauses ***********";
    print @@ lazy (ExClauseSet.str_of (fst d_diff));
    print @@ lazy (ExClauseSet.str_of (snd d_diff));
    (*|> (fun cs -> print @@ lazy ("***** original\n" ^ PCSP.Problem.str_of (PCSP.Problem.of_clauses ~params:(PCSP.Params.make exi_senv) cs)); cs)*)
    let senv = PCSP.Problem.senv_of APCSP.problem in
    PCSP.Problem.clauses_of APCSP.problem
    |> ClauseSet.resolve_one_step_all ~print:Debug.print
         (Set.Poly.filter_map (fst d_diff) ~f:ExClause.atom_of_uclause)
         (Set.Poly.filter_map (snd d_diff) ~f:ExClause.atom_of_uclause)
         senv
    |> Set.Poly.map ~f:fst
    |> resolution_loop (dpos, dneg, undecided) senv
    |> Option.value_map ~default:State.Unsat ~f:(fun (dpos', dneg') ->
           let dpos' = ExClauseSet.normalize dpos' in
           let dneg' = ExClauseSet.normalize dneg' in
           let added = Set.diff (Set.union dpos' dneg') (Set.union dpos dneg) in
           print @@ lazy "*** Newly obtained example instances:";
           print
           @@ lazy
                (String.concat_set ~sep:";\n"
                @@ Set.Poly.map ~f:ExClause.str_of added);
           print @@ lazy "";
           let new_examples =
             Set.Poly.union_list [ dpos'; dneg'; undecided ]
             |> (fun exs -> Set.diff exs (VersionSpace.examples_of vs))
             |> Set.Poly.map ~f:(fun ex -> (ex, [ (ClauseGraph.Dummy, false) ]))
           in
           (*TODO: add sources for new_undecided *)
           State.of_examples vs new_examples)
    |> fun e -> Ok e

  let run_phase _iters = resolve
end
