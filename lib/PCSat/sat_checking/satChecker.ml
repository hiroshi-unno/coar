open Core
open Common
open Common.Util
open Ast
open PCSatCommon

module Config = struct
  type strategy =
    | SAT (* SAT solving *)
    | SAT_Biased (* SAT solving with positive bias to WF and alternating positive and negative bias to the other predicate variables *)
    | CBandit (* Contextual bandit *)
    | Bandit_BDD (* Bandit with BDDs *)
  [@@deriving yojson]
  type t = {
    verbose : bool;
    num_labelings : int;
    strategy : strategy;
    sat_solver : SATSolver.Config.t ext_file
  } [@@deriving yojson]

  let instantiate_ext_files cfg =
    let open Or_error in
    SATSolver.Config.load_ext_file cfg.sat_solver >>= fun sat ->
    Ok { cfg with sat_solver = sat }

  let load_ext_file = function
    | ExtFile.Filename filename -> (
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x -> instantiate_ext_files x >>= fun x -> Ok (ExtFile.Instance x)
        | Error msg ->
          error_string
          @@ Printf.sprintf "Invalid Classifier Configuration (%s): %s"
            filename msg )
    | Instance x -> Ok (Instance x)

  let str_of_strategy = function
    | SAT -> "SAT solving"
    | SAT_Biased -> "SAT solving with bias"
    | CBandit -> "Contextual bandit"
    | Bandit_BDD -> "Bandit with BDDs"

  module type ConfigType = sig val config : t end
end

module type ClassifierType = sig
  val run_phase : State.u -> State.u Or_error.t
end

module Make (Cfg : Config.ConfigType) (APCSP : PCSP.Problem.ProblemType) :
  ClassifierType = struct
  let config = Cfg.config

  module Debug = Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let sat_solver =
    let open Or_error in
    ExtFile.unwrap config.sat_solver >>= fun cfg ->
    Ok (module SATSolver.Solver.Make (struct let config = cfg end) : SATSolver.Solver.SolverType)

  (* ToDo: this may be of no use because pos is always empty? *)
  let rec learn_clauses_to_remove_nondet_functions pos res = function
    | [] -> res
    | (pvar, sorts) :: fnpvs ->
      let sample = Set.Poly.filter pos ~f:(fun ((pvar', _), _) -> Stdlib.(=) pvar' pvar) in
      if Set.Poly.is_empty sample then learn_clauses_to_remove_nondet_functions pos res fnpvs
      else
        let map =
          Set.Poly.map sample ~f:(fun ((_pvar, _sorts), (terms : LogicOld.Term.t list)) ->
              (List.take terms (List.length terms - 1), List.last_exn terms))
          |> Set.Poly.to_list |> Map.Poly.of_alist_multi
        in
        let res' =
          Map.Poly.fold map ~init:res ~f:(fun ~key:args ~data:rets res ->
              Set.fold_distinct_pairs (Set.Poly.of_list rets) ~init:res
                ~f:(fun r1 r2 ->
                    ExClause.{
                      positive = Set.Poly.empty;
                      negative =
                        Set.Poly.of_list
                          [
                            ExAtom.PApp ((pvar, sorts), args @ [ r1 ]);
                            ExAtom.PApp ((pvar, sorts), args @ [ r2 ]);
                          ];
                    }))
        in
        learn_clauses_to_remove_nondet_functions pos res' fnpvs

  (* the return value may contain a unit clause*)
  let rec learn_clauses_to_remove_cycles pos res = function
    | [] -> res
    | (pvar, sorts) :: wfpvs ->
      let sample = Set.Poly.filter pos ~f:(fun ((pvar', _), _) -> Stdlib.(=) pvar' pvar) in
      if Set.Poly.is_empty sample then learn_clauses_to_remove_cycles pos res wfpvs
      else
        let has_self_loop (_, terms) =
          let size = List.length terms / 2 in
          List.(Stdlib.( = ) (take terms size) (drop terms size))
        in
        (* ToDo: Better add all? *)
        match Set.Poly.find sample ~f:has_self_loop with
        | Some ((_pvar, sorts), terms) ->
          let res' = Set.Poly.add res (ExClause.mk_unit_neg (ExAtom.PApp ((pvar, sorts), terms))) in
          learn_clauses_to_remove_cycles pos res' wfpvs
        | None ->
          let open Graph in
          let open Pack.Digraph in
          LoopDetector.gen_graph sample
          |> (fun (graph, node_map_rev) -> graph, Components.scc_list graph, node_map_rev)
          |> LoopDetector.detect res pvar sorts
          |> flip (learn_clauses_to_remove_cycles pos) wfpvs

  let abstract_exatom map atm =
    match Map.Poly.find map atm with
    | None -> failwith @@ Printf.sprintf "Not found: %s" (ExAtom.str_of atm)
    | Some p -> p
  let abstract_clause map clause =
    let ps = Set.Poly.map ~f:(abstract_exatom map) clause.ExClause.positive in
    let ns = Set.Poly.map ~f:(fun e -> PropLogic.Formula.mk_neg (abstract_exatom map e)) clause.ExClause.negative in
    PropLogic.Formula.or_of @@ Set.Poly.to_list @@ Set.Poly.union ps ns
  let abstract map cls =
    PropLogic.Formula.and_of @@ Set.Poly.to_list @@
    Set.Poly.map cls ~f:(abstract_clause map)

  let gen_fresh_prop =
    let prop_count = ref 0 in
    fun () ->
      prop_count := !prop_count + 1;
      PropLogic.Formula.mk_atom ("A" ^ string_of_int !prop_count)
  let mk_labels pos neg und =
    assert (Set.Poly.is_empty (Set.Poly.inter pos neg));
    Map.of_set @@ Set.Poly.union_list @@
    [Set.Poly.filter_map und ~f:(fun atm ->
         if Set.Poly.mem pos atm || Set.Poly.mem neg atm then (*ToDo: reachable?*)None
         else Some (atm, gen_fresh_prop ()));
     Set.Poly.map pos ~f:(fun atm -> atm, PropLogic.Formula.mk_true ());
     Set.Poly.map neg ~f:(fun atm -> atm, PropLogic.Formula.mk_false ())]

  let of_assignment map assign =
    Map.Poly.fold map ~init:(Set.Poly.empty, Set.Poly.empty)
      ~f:(fun ~key:app ~data:prop (pos, neg) ->
          match prop with
          | PropLogic.Formula.Atom (bvar, _) -> begin
              match List.Assoc.find assign bvar ~equal:Stdlib.(=) with
              | None (*ignore don't care*) -> pos, neg
              | Some true -> Set.Poly.add pos app, neg
              | Some false -> pos, Set.Poly.add neg app
            end
          | True _ -> Set.Poly.add pos app, neg
          | False _ -> pos, Set.Poly.add neg app
          | _ -> pos, neg)
  let pos_bias = ref true
  let check_sat_with _wfpvs map cls = function
    | (Config.SAT | SAT_Biased) as strategy ->
      (*Set.Poly.iter cls ~f:(fun cl -> Debug.print @@ lazy ("checking: " ^ ExClause.str_of cl));*)
      let open Or_error.Monad_infix in
      sat_solver >>= fun (module SatSolver : SATSolver.Solver.SolverType) ->
      let check phi =
        let cnf = SAT.Problem.of_list @@ PropLogic.Formula.cnf_of phi in
        (*Debug.print @@ lazy ("checking: " ^ SAT.Problem.str_of cnf);*)
        SatSolver.solve cnf in
      let constr = abstract map cls in
      (*Debug.print @@ lazy ("checking: " ^ PropLogic.Formula.str_of constr);*)
      if Stdlib.(=) strategy SAT then
        check constr >>= (function
            | SAT.Problem.Unsat -> Ok None
            | SAT.Problem.Sat sol -> Ok (Some (of_assignment map sol)))
      else
        let biased =
          let map = Map.Poly.to_alist map in
          PropLogic.Formula.and_of @@
          List.filter_map map ~f:(fun (atm, prop) ->
              match ExAtom.pvar_of atm, prop with
              | Some _, PropLogic.Formula.Atom (_, _) ->
                Some (if !pos_bias then prop else PropLogic.Formula.mk_neg prop)
              | _ -> None)
        in
        let _ = pos_bias := not !pos_bias in
        check (PropLogic.Formula.and_of [constr; biased]) >>= (function
            | SAT.Problem.Unsat ->
              check constr >>= (function
                  | SAT.Problem.Unsat -> Ok None
                  | SAT.Problem.Sat sol -> Ok (Some (of_assignment map sol)))
            | SAT.Problem.Sat sol -> Ok (Some (of_assignment map sol)))
    | CBandit | Bandit_BDD -> failwith "not implemented"

  (** ToDo: extend to support the case where [undecided] contains function variables *)
  let check_sat_main wfpvs fnpvs pos_atms neg_atms undecided =
    let und_atms = ExClauseSet.exatoms_of undecided in
    let map = mk_labels pos_atms neg_atms und_atms in
    let rec outer_loop ps_ns_list cls n =
      let open Or_error.Monad_infix in
      let rec inner_loop lcls(* learnt clauses *) sample =
        let block_prev_assignments = (* constraints to block previous assignments *)
          Set.Poly.map (Set.Poly.of_list ps_ns_list) ~f:(fun (ps, ns) ->
              { ExClause.positive = ns; ExClause.negative = ps} )
        in
        check_sat_with wfpvs map (Set.Poly.union_list [ lcls; sample; block_prev_assignments ]) config.strategy >>= function
        | None ->
          Debug.print @@ lazy ("learnt clauses:\n" ^ ExClauseSet.str_of ~max_display:None lcls);
          Debug.print @@ lazy ("example instances:\n" ^ ExClauseSet.str_of ~max_display:None sample);
          Ok None
        | Some (pos, neg) ->
          let lcls' =
            let papps = Set.Poly.filter_map pos ~f:(function
                | PApp papp -> Some papp
                | _ -> (*ToDo: is it OK to ignore parametric examples?*)None) in
            Set.Poly.union
              (learn_clauses_to_remove_cycles papps Set.Poly.empty wfpvs)
              (learn_clauses_to_remove_nondet_functions papps Set.Poly.empty fnpvs)
          in
          if Set.Poly.is_empty lcls' then (*sat*) Ok (Some ((pos, neg), lcls))
          else inner_loop (Set.Poly.union lcls lcls') sample
      in
      if n <= 0 then Ok (ps_ns_list, cls)
      else
        inner_loop cls undecided >>= function
        | None -> Ok (ps_ns_list, cls)
        | Some ((pos, neg), lcls) ->
          outer_loop ((pos, neg) :: ps_ns_list) (Set.Poly.union cls lcls) (n - 1)
    in
    assert (config.num_labelings > 0);
    outer_loop [] Set.Poly.empty config.num_labelings

  let str_of_conflicts conflicts =
    "********* conflicts *********\n"
    ^ String.concat ~sep:", " @@ Set.Poly.to_list @@ Set.Poly.map ~f:ExAtom.str_of conflicts

  let check_sat vs () =
    let (dpos, dneg, undecided) = VersionSpace.examples_of vs in
    (*Debug.print @@ lazy ("undecided:\n" ^ ExClauseSet.str_of ~max_display:None undecided);*)
    Debug.print @@ lazy ("*** satisfiability checking with " ^ Config.str_of_strategy config.strategy);
    let wfpvs =
      PCSP.Problem.wfpvs_senv_of APCSP.problem |> Logic.SortMap.to_alist
      |> List.map ~f:(fun (Ident.Tvar n, sort) ->
          Ident.Pvar n,
          Logic.Sort.args_of sort |> List.map ~f:Logic.ExtTerm.to_old_sort)
    in
    let fnpvs =
      PCSP.Problem.fnpvs_senv_of APCSP.problem |> Logic.SortMap.to_alist
      |> List.map ~f:(fun (Ident.Tvar n, sort) ->
          Ident.Pvar n,
          Logic.Sort.args_of sort |> List.map ~f:Logic.ExtTerm.to_old_sort)
    in
    let open Or_error in
    let pos_atms, neg_atms, undecided_inst =
      (*ToDo: extend satisfiability checker to support parametric examples*)
      ExClauseSet.exatoms_of_uclauses @@ (*ExClauseSet.normalize @@*) ExClauseSet.instantiate dpos,
      ExClauseSet.exatoms_of_uclauses @@ (*ExClauseSet.normalize @@*) ExClauseSet.instantiate dneg,
      (*ExClauseSet.normalize @@*) ExClauseSet.instantiate undecided
    in
    let conflicts = Set.Poly.inter pos_atms neg_atms in
    if not @@ Set.Poly.is_empty conflicts then begin
      Debug.print @@ lazy (str_of_conflicts conflicts);
      Ok State.Unsat
    end else
      check_sat_main wfpvs fnpvs pos_atms neg_atms undecided_inst >>= function
      | [], _ -> Ok State.Unsat
      | pos_neg_list, loop_cls ->
        let undecided' = Set.Poly.union loop_cls undecided in
        let vs' = VersionSpace.set_examples (dpos, dneg, undecided') vs in
        let labeling_list = List.map pos_neg_list ~f:(fun (pos, neg) ->
            let labeling =
              Set.Poly.fold pos ~init:Map.Poly.empty ~f:(fun l atm ->
                  VersionSpace.set_label vs' TruthTable.label_pos l (ExAtom.normalize_params atm))
            in
            let labeling =
              Set.Poly.fold neg ~init:labeling ~f:(fun l atm ->
                  VersionSpace.set_label vs' TruthTable.label_neg l (ExAtom.normalize_params atm))
            in
            labeling) in
        let vs' = VersionSpace.set_labelings labeling_list vs' in
        Ok (State.Continue ((vs', ())))

  let unit_propagation vs () =
    Debug.print @@ lazy "*** unit propagation";
    let (dpos, dneg, undecided) = VersionSpace.examples_of vs in
    match ExClauseSet.unit_propagation (Map.key_set @@ PCSP.Problem.senv_of APCSP.problem) dpos dneg undecided with
    | `Unsat conflicts ->
      Debug.print @@ lazy (str_of_conflicts conflicts);
      Ok State.Unsat
    | `Result (dpos', dneg', undecided') ->
      Debug.print @@ lazy (VersionSpace.str_of_examples (dpos', dneg', undecided'));
      Ok (State.of_examples vs (dpos', dneg', undecided'))

  let run_phase e =
    Debug.print @@ lazy "**** satisfiability checker";
    let open State.Monad_infix in
    Ok e >>=? unit_propagation >>=? check_sat
end

let make config pcsp =
  (module Make (struct let config = config end) (struct let problem = pcsp end) : ClassifierType)
