open Core
open Common
open Common.Ext
open Common.Util
open Ast
open PCSatCommon

module Config = struct
  type perturbation =
    | None
    | Trans of int(* max_iters *)
    | Uniform of float(* bound *)
    | Gaussian of float(* standard deviation *)
  [@@deriving yojson]
  type strategy =
    | SAT (* SAT solving *)
    | ORACLE_SAT of strategy
    | POS_BIASED_SAT (* Positively biased SAT solving *)
    | NEG_BIASED_SAT (* Negatively biased SAT solving *)
    | RAND_MAX_SAT of (* Randomly weighted MAX-SAT solving *)
        float(* cut-off lower-bound *) * float(* cut-off upper-bound *)
    | BMI_MAX_SAT of (* BMI weighted MAX-SAT solving *)
        int(* num *) * int(* bound *) * float(* ratio *) *
        perturbation *
        float(* cut-off lower-bound *) * float(* cut-off upper-bound *) *
        float(* enc_bool_to_float *) *
        bool(* ignore_bool_args_variance *)
    | ORACLE_MAX_SAT of strategy
    | POS_BIASED_MAX_SAT of (* Positively biased MAX-SAT solving *)
        bool(* use examples *) * float(* weight *)
    | NEG_BIASED_MAX_SAT of (* Negatively biased MAX-SAT solving *)
        bool(* use examples *) * float(* weight *)
    | Mixed of (strategy * bool(* enable sampling *)) list
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
    | ExtFile.Filename filename ->
      begin
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x -> instantiate_ext_files x >>= fun x -> Ok (ExtFile.Instance x)
        | Error msg ->
          error_string @@ Printf.sprintf
            "Invalid Labeler Configuration (%s): %s" filename msg
      end
    | Instance x -> Ok (Instance x)

  let str_of_perturbation = function
    | None -> "None"
    | Trans max_iters -> "Trans(" ^ string_of_int max_iters ^ ")"
    | Uniform bound -> "Uniform(" ^ string_of_float bound ^ ")"
    | Gaussian sigma -> "Gaussian(" ^ string_of_float sigma ^ ")"
  let rec str_of_strategy = function
    | SAT -> "SAT solving"
    | ORACLE_SAT s -> "Oracle SAT solving [" ^ str_of_strategy s ^ "]"
    | POS_BIASED_SAT -> "Positively biased SAT solving"
    | NEG_BIASED_SAT -> "Negatively biased SAT solving"
    | RAND_MAX_SAT (cut_off_lb, cut_off_ub) ->
      "Randomly weighted MAX-SAT solving (" ^
      string_of_float cut_off_lb ^ ", " ^
      string_of_float cut_off_ub ^ ")"
    | BMI_MAX_SAT (num, bound, ratio, perturbation, cut_off_lb, cut_off_ub, enc_bool_to_float, ignore_bool_args_variance) ->
      "BMI weighted MAX-SAT solving (" ^
      string_of_int num ^ ", " ^
      string_of_int bound ^ ", " ^
      string_of_float ratio ^ ", " ^
      str_of_perturbation perturbation ^ ", " ^
      string_of_float cut_off_lb ^ ", " ^
      string_of_float cut_off_ub ^ ", " ^
      string_of_float enc_bool_to_float ^ ", " ^
      string_of_bool ignore_bool_args_variance ^ ")"
    | ORACLE_MAX_SAT s -> "Oracle MAX-SAT solving [" ^ str_of_strategy s ^ "]"
    | POS_BIASED_MAX_SAT (b, w) -> "Positively biased MAX-SAT solving (" ^ string_of_bool b ^ ", " ^ string_of_float w ^ ")"
    | NEG_BIASED_MAX_SAT (b, w) -> "Negatively biased MAX-SAT solving (" ^ string_of_bool b ^ ", " ^ string_of_float w ^ ")"
    | Mixed ss ->
      "[" ^ (String.concat_map_list ~sep:", " ss ~f:(fun (s, b) -> (if b then "!" else "") ^ str_of_strategy s)) ^ "]"
    | CBandit -> "Contextual bandit"
    | Bandit_BDD -> "Bandit with BDDs"

  module type ConfigType = sig val config : t end
end

module type ClassifierType = sig
  val run_phase : int -> State.u -> State.u Or_error.t
end

module Make (RLCfg: RLConfig.ConfigType) (Cfg : Config.ConfigType) (APCSP : PCSP.Problem.ProblemType) :
  ClassifierType = struct
  let config = Cfg.config
  let id = PCSP.Problem.id_of APCSP.problem

  module Debug = Debug.Make (val Debug.Config.(if config.verbose then enable else disable))
  let _ = Debug.set_id id

  let sat_solver =
    let open Or_error in
    ExtFile.unwrap config.sat_solver >>= fun cfg ->
    Ok (module SATSolver.Solver.Make (struct let config = cfg end) : SATSolver.Solver.SolverType)

  (* ToDo: this may be of no use because pos is always empty? *)
  let rec learn_clauses_to_remove_nondet_functions pos res = function
    | [] -> res
    | (pvar, sorts) :: fnpvs ->
      let sample = Set.Poly.filter pos ~f:(fun ((pvar', _), _) -> Stdlib.(pvar = pvar')) in
      if Set.Poly.is_empty sample then learn_clauses_to_remove_nondet_functions pos res fnpvs
      else
        let map =
          Set.Poly.map sample ~f:(fun ((_pvar, _sorts), (terms : LogicOld.Term.t list)) ->
              (List.take terms (List.length terms - 1), List.last_exn terms))
          |> Set.Poly.to_list |> Map.Poly.of_alist_multi
        in
        let res' =
          Map.Poly.fold map ~init:res ~f:(fun ~key:args ~data:rets res ->
              Set.fold_distinct_pairs (Set.Poly.of_list rets) ~init:res ~f:(fun r1 r2 ->
                  ExClause.{
                    positive = Set.Poly.empty;
                    negative =
                      Set.Poly.of_list
                        [
                          ExAtom.PApp ((pvar, sorts), args @ [ r1 ]);
                          ExAtom.PApp ((pvar, sorts), args @ [ r2 ])
                        ];
                  }))
        in
        learn_clauses_to_remove_nondet_functions pos res' fnpvs

  (* the return value may contain a unit clause*)
  let rec learn_clauses_to_remove_cycles pos res = function
    | [] -> res
    | (pvar, sorts) :: wfpvs ->
      let sample = Set.Poly.filter pos ~f:(fun ((pvar', _), _) -> Stdlib.(pvar = pvar')) in
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
          |> Fn.flip (learn_clauses_to_remove_cycles pos) wfpvs

  let rec learn_clauses_to_remove_cycles_for_nwf pos res = function
    | [] -> res
    | (pvar, sorts, sorts_l, sorts_r) :: nwfpvs ->
      let sample = Set.Poly.filter pos ~f:(fun ((pvar', _), _) -> Stdlib.(pvar = pvar')) in
      if Set.Poly.is_empty sample then learn_clauses_to_remove_cycles_for_nwf pos res nwfpvs
      else
        let has_self_loop (_, terms) =
          let terms = List.drop terms (List.length sorts) in
          let size_x = List.length sorts_l in
          List.(Stdlib.( = ) (take terms size_x) (drop terms size_x))
        in
        (* ToDo: Better add all? *)
        match Set.Poly.find sample ~f:has_self_loop with
        | Some ((_pvar, sorts), terms) ->
          let res' = Set.Poly.add res (ExClause.mk_unit_neg (ExAtom.PApp ((pvar, sorts), terms))) in
          learn_clauses_to_remove_cycles_for_nwf pos res' nwfpvs
        | None ->
          let open Graph in
          let open Pack.Digraph in
          NWFLoopDetector.gen_graph (sorts, sorts_l, sorts_r) sample
          |> (fun (graph, node_map_rev) -> graph, Components.scc_list graph, node_map_rev)
          |> NWFLoopDetector.detect res pvar (sorts, sorts_l, sorts_r)
          |> Fn.flip (learn_clauses_to_remove_cycles_for_nwf pos) nwfpvs

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
    Map.of_set_exn @@ Set.Poly.union_list @@
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
  let scaler = 10000.0
  let check_sat_with iters vs _wfpvs map cls =
    let open Or_error.Monad_infix in
    (*Set.Poly.iter cls ~f:(fun cl -> Debug.print @@ lazy ("checking: " ^ ExClause.str_of cl));*)
    let constr = abstract map cls in
    (*Debug.print @@ lazy ("checking: " ^ PropLogic.Formula.str_of constr);*)
    let rec aux iters strategy =
      sat_solver >>= fun (module SatSolver : SATSolver.Solver.SolverType) ->
      match strategy with
      | Config.SAT ->
        SatSolver.solve (SAT.Problem.of_prop_formula constr)
        >>= (function
            | SAT.Problem.Unsat -> Ok None
            | SAT.Problem.Sat sol -> Ok (Some (of_assignment map sol, true)))
      | Config.ORACLE_SAT s -> begin
          match VersionSpace.oracle_of vs with
          | None -> aux iters s
          | Some oracle ->
            constr ::
            List.filter_map (Map.Poly.to_alist map) ~f:(fun (atom, prop) ->
                let open Option in
                ExAtom.pvar_of atom >>= fun pvar ->
                let qdep = VersionSpace.qdeps_of pvar vs in
                Map.Poly.find (Map.of_set_exn @@ snd oracle) pvar >>= fun pred ->
                match ExAtom.eval_pred ~id (VersionSpace.fenv_of vs) qdep pred atom with
                | Some true -> Some prop
                | Some false -> Some (PropLogic.Formula.mk_neg prop)
                | None -> assert false)
            |> PropLogic.Formula.and_of
            |> SAT.Problem.of_prop_formula
            |> SatSolver.solve
            >>= (function
                | SAT.Problem.Unsat -> Ok None
                | SAT.Problem.Sat sol -> Ok (Some (of_assignment map sol, true)))
        end
      | Config.POS_BIASED_SAT | Config.NEG_BIASED_SAT ->
        let pos_bias = Stdlib.(strategy = Config.POS_BIASED_SAT) in
        constr ::
        List.filter_map (Map.Poly.to_alist map) ~f:(fun (atm, prop) ->
            match ExAtom.pvar_of atm, prop with
            | Some _, PropLogic.Formula.Atom (_, _) ->
              if pos_bias then Some prop else Some (PropLogic.Formula.mk_neg prop)
            | _ -> None)
        |> PropLogic.Formula.and_of
        |> SAT.Problem.of_prop_formula
        |> SatSolver.solve
        >>= (function
            | SAT.Problem.Unsat ->
              Debug.print @@ lazy "biased labeling not found";
              SatSolver.solve (SAT.Problem.of_prop_formula constr)
              >>= (function
                  | SAT.Problem.Unsat -> Ok None
                  | SAT.Problem.Sat sol -> Ok (Some (of_assignment map sol, true)))
            | SAT.Problem.Sat sol ->
              Debug.print @@ lazy "biased labeling found";
              Ok (Some (of_assignment map sol, true)))
      | RAND_MAX_SAT (cut_off_lb, _cut_off_ub) ->
        let soft =
          assert Float.(cut_off_lb >= 0.);
          List.filter_map (Map.Poly.to_alist map) ~f:(fun (atom, prop) ->
              let heat = Random.float_range (-1.) 1. in
              Debug.print @@ lazy (Format.sprintf "%s has value %f" (ExAtom.str_of atom) heat);
              let scaled_heat = int_of_float @@ scaler *. heat in
              let scaled_cut_off_lb = int_of_float @@ scaler *. cut_off_lb in
              if scaled_heat > scaled_cut_off_lb then
                Some (SAT.Problem.of_prop_formula prop, scaled_heat)
              else if scaled_heat < -scaled_cut_off_lb then
                Some (SAT.Problem.of_prop_formula (PropLogic.Formula.mk_neg prop), -scaled_heat)
              else None)
        in
        SatSolver.opt_solve soft (SAT.Problem.of_prop_formula constr)
        >>= (function
            | SAT.Problem.Unsat -> Ok None
            | SAT.Problem.Sat sol -> Ok (Some (of_assignment map sol, true)))
      | BMI_MAX_SAT (num, bound, ratio, perturbation, cut_off_lb, _cut_off_ub, enc_bool_to_float, ignore_bool_args_variance) ->
        let soft =
          assert Float.(cut_off_lb >= 0.);
          Debug.print @@ lazy ">>> heat map generation";
          let tm = Timer.make () in
          let exs1 =
            let dw = 1.0(* default weight for counterexamples *) in
            VersionSpace.examples_of vs |> Set.Poly.map ~f:(fun cl -> cl, dw) |> Set.Poly.to_list
          in
          let exs2 =
            let clauses = Set.Poly.elements @@ PCSP.Problem.clauses_of APCSP.problem in
            let rand_samp =
              List.init num ~f:(fun _ ->
                  let clause = List.nth_exn clauses (Random.int (List.length clauses)) in
                  let sub = Map.Poly.mapi (Clause.sort_env_of clause) ~f:(fun ~key:_ ~data ->
                      match data with
                      | Logic.IntTerm.SInt ->
                        Logic.ExtTerm.mk_int (Z.of_int @@ Random.int (2 * bound + 1) - bound)
                      | Logic.RealTerm.SReal ->
                        let fb = float_of_int bound in
                        Logic.ExtTerm.mk_real (Q.of_float @@ Random.float_range (-.fb) fb)
                      | Logic.BoolTerm.SBool ->
                        Logic.BoolTerm.mk_bool @@ Random.bool ()
                      | _(*ToDo*) -> Logic.ExtTerm.mk_dummy data) in
                  Clause.reduce_sort_map @@ Clause.subst (PCSP.Problem.senv_of APCSP.problem) sub clause)
            in
            let weight =
              if num = 0 then 0.0 else
                ratio *. (float_of_int @@ List.length exs1) /. (float_of_int num) in
            List.filter_map rand_samp ~f:(fun cl ->
                let (uni_senv, pos_atms, neg_atms, phi) = Clause.to_old_clause (PCSP.Problem.senv_of APCSP.problem) cl in
                assert (Map.Poly.is_empty uni_senv);
                match ExClause.make (PCSP.Problem.senv_of APCSP.problem) pos_atms neg_atms phi with
                | None -> None
                | Some cl -> Some (ExClause.normalize_params cl, weight))
          in
          VersionSpace.update_heat_map ~enc_bool_to_float ~ignore_bool_args_variance (PCSP.Problem.senv_of APCSP.problem) (exs1 @ exs2) vs;
          Debug.print @@ lazy (Format.sprintf "<<< heat map generation: %f" (tm ()));
          (*Out_channel.print_endline @@ string_of_int iters_mod;*)
          List.filter_map (Map.Poly.to_alist map) ~f:(fun (atom, prop) ->
              let heat = VersionSpace.get_heat vs atom in
              let heat =
                match perturbation with
                | None -> heat
                | Trans max_iters ->
                  let alpha = float_of_int (min iters max_iters) /. float_of_int max_iters in
                  (1.0 -. alpha) *. heat +. alpha *. Random.float_range (-1.) 1.
                | Uniform bound ->
                  heat +. (Random.float_range (-.bound) bound) *. float_of_int iters
                | Gaussian sigma ->
                  Float.rand_gaussian heat (sigma *. float_of_int iters)
              in
              Debug.print @@ lazy (Format.sprintf "%s has value %f" (ExAtom.str_of atom) heat);
              let scaled_heat = int_of_float @@ scaler *. heat in
              let scaled_cut_off_lb = int_of_float @@ scaler *. cut_off_lb in
              if scaled_heat > scaled_cut_off_lb then
                Some (SAT.Problem.of_prop_formula prop, scaled_heat)
              else if scaled_heat < -scaled_cut_off_lb then
                Some (SAT.Problem.of_prop_formula (PropLogic.Formula.mk_neg prop), -scaled_heat)
              else None)
        in
        SatSolver.opt_solve soft (SAT.Problem.of_prop_formula constr)
        >>= (function
            | SAT.Problem.Unsat -> Ok None
            | SAT.Problem.Sat sol -> Ok (Some (of_assignment map sol, true)))
      | Config.ORACLE_MAX_SAT s -> begin
          match VersionSpace.oracle_of vs with
          | None -> aux iters s
          | Some oracle ->
            let soft =
              List.filter_map (Map.Poly.to_alist map) ~f:(fun (atom, prop) ->
                  let open Option in
                  ExAtom.pvar_of atom >>= fun pvar ->
                  Map.Poly.find (Map.of_set_exn @@ snd oracle) pvar >>= fun pred ->
                  match ExAtom.eval_pred ~id (VersionSpace.fenv_of vs) (Map.Poly.empty) pred atom with
                  | Some true ->
                    Some (SAT.Problem.of_prop_formula prop, 1)
                  | Some false ->
                    Some (SAT.Problem.of_prop_formula (PropLogic.Formula.mk_neg prop), 1)
                  | None -> assert false)
            in
            SatSolver.opt_solve soft (SAT.Problem.of_prop_formula constr)
            >>= (function
                | SAT.Problem.Unsat -> Ok None
                | SAT.Problem.Sat sol -> Ok (Some (of_assignment map sol, true)))
        end
      | Config.POS_BIASED_MAX_SAT (strengthen_bias, w) | Config.NEG_BIASED_MAX_SAT (strengthen_bias, w) ->
        let pos_bias = match strategy with Config.POS_BIASED_MAX_SAT _ -> true | _ -> false in
        let weights =
          List.filter_map (Map.Poly.to_alist map) ~f:(fun (atm, prop) ->
              match ExAtom.pvar_of atm, prop with
              | Some _, PropLogic.Formula.Atom (_, _) -> Some (atm, 1.)
              | _ -> None)
        in
        let weights =
          if strengthen_bias then
            Set.Poly.fold ~init:weights cls ~f:(fun weights clause ->
                List.map weights ~f:(fun (atm, weight) ->
                    let size = Set.Poly.length clause.ExClause.positive + Set.Poly.length clause.ExClause.negative in
                    if pos_bias && Set.Poly.mem clause.ExClause.positive atm ||
                       not pos_bias && Set.Poly.mem clause.ExClause.negative atm then
                      (atm, weight +. w /. float_of_int size)
                    else (atm, weight)))
          else weights
        in
        let soft =
          List.map weights ~f:(fun (atm, weight) ->
              let prop = Map.Poly.find_exn map atm in
              if pos_bias then
                SAT.Problem.of_prop_formula prop, int_of_float @@ scaler *. weight
              else
                SAT.Problem.of_prop_formula (PropLogic.Formula.mk_neg prop), int_of_float @@ scaler *. weight)
        in
        SatSolver.opt_solve soft (SAT.Problem.of_prop_formula constr)
        >>= (function
            | SAT.Problem.Unsat -> Ok None
            | SAT.Problem.Sat sol -> Ok (Some (of_assignment map sol, true)))
      | Config.Mixed ss ->
        let strategy, sample_examples = List.nth_exn ss (iters mod List.length ss) in
        aux (iters / List.length ss) strategy >>= (function
            | None -> Ok None
            | Some (labeling, sample_examples') ->
              Ok (Some (labeling, sample_examples && sample_examples')))
      | CBandit | Bandit_BDD -> failwith "not implemented"
    in aux iters
  (** ToDo: extend to support the case where [undecided] contains function variables *)
  let check_sat_main iters vs nwfpvs wfpvs fnpvs pos_atms neg_atms undecided =
    let und_atms = ExClauseSet.exatoms_of undecided in
    let map = mk_labels pos_atms neg_atms und_atms in
    let rec outer_loop ps_ns_list cls n =
      let open Or_error.Monad_infix in
      let rec inner_loop lcls(* learned clauses *) sample =
        let block_prev_assignments = (* constraints to block previous assignments *)
          Set.Poly.map (Set.Poly.of_list ps_ns_list) ~f:(fun (ps, ns, _) ->
              { ExClause.positive = ns; ExClause.negative = ps} )
        in
        check_sat_with iters vs wfpvs map (Set.Poly.union_list [ lcls; sample; block_prev_assignments ]) config.strategy >>= function
        | None ->
          Debug.print @@ lazy ("learned clauses:\n" ^ ExClauseSet.str_of ~max_display:None lcls);
          Debug.print @@ lazy ("example instances:\n" ^ ExClauseSet.str_of ~max_display:None sample);
          Ok None
        | Some ((pos, neg), sample_examples) ->
          let lcls' =
            let papps = Set.Poly.filter_map pos ~f:(function
                | PApp papp -> Some papp
                | _ -> (*ToDo: is it OK to ignore parametric examples?*)None) in
            Set.Poly.union_list
              [(learn_clauses_to_remove_cycles papps Set.Poly.empty wfpvs);
               (learn_clauses_to_remove_cycles_for_nwf papps Set.Poly.empty nwfpvs);
               (learn_clauses_to_remove_nondet_functions papps Set.Poly.empty fnpvs)]
          in
          if Set.Poly.is_empty lcls' then (*sat*) Ok (Some ((pos, neg, sample_examples), lcls))
          else inner_loop (Set.Poly.union lcls lcls') sample
      in
      if n <= 0 then Ok (ps_ns_list, cls)
      else
        inner_loop cls undecided >>= function
        | None -> Ok (ps_ns_list, cls)
        | Some ((pos, neg, sample_examples), lcls) ->
          outer_loop ((pos, neg, sample_examples) :: ps_ns_list) (Set.Poly.union cls lcls) (n - 1)
    in
    assert (config.num_labelings > 0);
    outer_loop [] Set.Poly.empty config.num_labelings

  let str_of_conflicts conflicts =
    "********* conflicts *********\n"
    ^ String.concat_set ~sep:", " @@ Set.Poly.map ~f:ExAtom.str_of conflicts

  let check_sat iters vs () =
    let (dpos, dneg, undecided) = VersionSpace.pos_neg_und_examples_of vs in
    (*Debug.print @@ lazy ("undecided:\n" ^ ExClauseSet.str_of ~max_display:None undecided);*)
    Debug.print @@ lazy ("*** labeling with " ^ Config.str_of_strategy config.strategy);
    let wfpvs =
      PCSP.Problem.wfpvs_senv_of APCSP.problem |> Map.Poly.to_alist
      |> List.map ~f:(fun (Ident.Tvar n, sort) ->
          Ident.Pvar n,
          Logic.Sort.args_of sort |> List.map ~f:Logic.ExtTerm.to_old_sort)
    in
    let fnpvs =
      PCSP.Problem.fnpvs_senv_of APCSP.problem |> Map.Poly.to_alist
      |> List.map ~f:(fun (Ident.Tvar n, sort) ->
          Ident.Pvar n,
          Logic.Sort.args_of sort |> List.map ~f:Logic.ExtTerm.to_old_sort)
    in
    let nwfpvs =
      PCSP.Problem.nwfpvs_senv_of APCSP.problem
      |> Map.Poly.to_alist
      |> List.map ~f:(fun (Ident.Tvar n, (_, sorts, _, sorts_x, _, sorts_y)) ->
          Ident.Pvar n,
          List.map ~f:Logic.ExtTerm.to_old_sort sorts,
          List.map ~f:Logic.ExtTerm.to_old_sort sorts_x,
          List.map ~f:Logic.ExtTerm.to_old_sort sorts_y)
    in
    let open Or_error in
    let pos_atms, neg_atms, undecided_inst =
      (*ToDo: extend satisfiability checker to support parametric examples*)
      ExClauseSet.exatoms_of_uclauses @@ (*ExClauseSet.normalize @@*) ExClauseSet.instantiate dpos,
      ExClauseSet.exatoms_of_uclauses @@ (*ExClauseSet.normalize @@*) ExClauseSet.instantiate dneg,
      (*ExClauseSet.normalize @@*) ExClauseSet.instantiate undecided
    in
    let conflicts = Set.Poly.inter pos_atms neg_atms in
    if Fn.non Set.Poly.is_empty conflicts then begin
      Debug.print @@ lazy (str_of_conflicts conflicts);
      Ok State.Unsat
    end else
      check_sat_main iters vs nwfpvs wfpvs fnpvs pos_atms neg_atms undecided_inst >>= function
      | [], _ -> Ok State.Unsat
      | pos_neg_list, loop_cls ->
        let new_undecided = Set.Poly.diff loop_cls undecided in
        let vs' = vs in
        VersionSpace.add_examples vs' @@
        Set.Poly.map new_undecided ~f:(fun ex -> (ex, [ClauseGraph.Dummy, false])); (*TODO: add sources for new_undecided *)
        let labeling_list = List.map pos_neg_list ~f:(fun (pos, neg, sample_examples) ->
            let labeling =
              Set.Poly.fold pos ~init:Map.Poly.empty ~f:(fun l atm ->
                  VersionSpace.set_label ~id vs' TruthTable.label_pos l (ExAtom.normalize_params atm))
            in
            let labeling =
              Set.Poly.fold neg ~init:labeling ~f:(fun l atm ->
                  VersionSpace.set_label ~id vs' TruthTable.label_neg l (ExAtom.normalize_params atm))
            in
            labeling, sample_examples) in
        let vs' = VersionSpace.set_labelings labeling_list vs' in
        Ok (State.Continue ((vs', ())))

  let unit_propagation vs () =
    Debug.print @@ lazy ">>> unit propagation";
    let (dpos, dneg, undecided) = VersionSpace.pos_neg_und_examples_of vs in
    let undecided = Set.Poly.map undecided ~f:(ExClause.simplify_nepvs (PCSP.Problem.nepvs_of APCSP.problem)) in
    let dpos = Set.Poly.map dpos ~f:(fun ex -> (ex, [ex])) in
    let dneg = Set.Poly.map dneg ~f:(fun ex -> (ex, [ex])) in
    let undecided = Set.Poly.map undecided ~f:(fun ex -> (ex, [ex])) in
    let res = ExClauseSet.unit_propagation (Map.key_set @@ PCSP.Problem.senv_of APCSP.problem) dpos dneg undecided in
    Debug.print @@ lazy "<<< unit propagation";
    match res with
    | `Unsat conflicts ->
      Debug.print @@ lazy (str_of_conflicts conflicts);
      Ok State.Unsat
    | `Result (dpos', dneg', undecided') ->
      Debug.print @@ lazy (VersionSpace.str_of_examples (Set.Poly.map ~f:fst dpos', Set.Poly.map ~f:fst dneg', Set.Poly.map ~f:fst undecided'));
      let new_examples =
        Set.Poly.union_list [dpos'; dneg'; undecided']
        |> Set.Poly.map ~f:(fun (ex, srcs) ->
            (ex, List.map srcs ~f:(fun e -> ClauseGraph.Example e, true))) in
      Ok (State.of_examples vs new_examples)

  let run_phase iters e =
    Debug.print @@ lazy "**** labeler";
    let open State.Monad_infix in
    Ok e >>=? unit_propagation >>=? check_sat iters
  let run_phase iters e =
    if RLCfg.config.enable then begin
      if RLCfg.config.show_elapsed_time then Out_channel.print_endline "begin labeler";
      let tm = Timer.make () in
      let res = run_phase iters e in
      if RLCfg.config.show_elapsed_time then Out_channel.print_endline (Format.sprintf "end labeler: %f" (tm ()));
      res
    end else run_phase iters e
end

let make rl_config config pcsp =
  (module Make
       (struct let config = rl_config end)
       (struct let config = config end)
       (struct let problem = pcsp end) : ClassifierType)
