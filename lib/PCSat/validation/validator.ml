(** Validator *)

open Core
open Common
open Common.Util
open PCSatCommon

module type ValidatorType = sig
  val run_phase : State.s -> State.u Or_error.t
end

(** configuration of validator *)
module Config = struct
  type t = {
    verbose: bool;
    num_of_examples: int option;
    parametric_candidates: bool;
    parametric_examples: bool;
    strategy_synthesis: bool;
    rl: bool;
    smt_timeout: int option
  } [@@deriving yojson]
  module type ConfigType = sig val config : t end

  let instantiate_ext_files cfg = Ok cfg

  let load_ext_file = function
    | ExtFile.Filename filename ->
      begin
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename)
        >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x ->
          instantiate_ext_files x >>= fun x ->
          Ok (ExtFile.Instance x)
        | Error msg ->
          error_string
          @@ Printf.sprintf
            "Invalid Validator Configuration (%s): %s" filename msg
      end
    | Instance x -> Ok (Instance x)
end

module Make (Cfg: Config.ConfigType) (APCSP: PCSP.Problem.ProblemType)
  : ValidatorType = struct
  let config = Cfg.config

  module Debug =
    Debug.Make (val Debug.Config.(if config.verbose then enable else disable))

  open Debug

  let validate vs (candidates : Ast.CandSol.t list) =
    let (pos, neg, und) = VersionSpace.examples_of vs in
    let fenv = VersionSpace.fenv_of vs in
    print @@ lazy "**** Validator";
    print @@ lazy (Ast.CandSol.str_of_list candidates);
    match config.num_of_examples with
    | None ->
      (** generate a (possibly parametric) counterexample for each (possibly parametric) candidate solution for each clause *)
      let rec iter examples = function
        | [] ->
          print @@ lazy "*************************************";
          print @@ lazy "*** There was no genuine solution ***";
          print @@ lazy "*************************************\n";
          print @@ lazy "*** Counterexamples to the Candidate Solutions:";
          print @@ lazy
            (String.concat ~sep:";\n"
             @@ Set.Poly.to_list 
             @@ (Set.Poly.map ~f:ExClause.str_of examples));
          print @@ lazy "";
          Ok (State.of_examples vs (pos, neg, Set.Poly.union und examples))
        | cand :: candidates ->
          let cexs =
            Cex.of_cand ~smt_timeout:config.smt_timeout
              config.parametric_candidates config.parametric_examples config.strategy_synthesis
              APCSP.problem fenv cand
          in
          if config.rl then begin
            let total = Set.Poly.length @@ PCSP.Problem.clauses_of APCSP.problem in
            let num_unsat = Set.Poly.length cexs in
            let num_sat = total - num_unsat in
            Out_channel.print_endline ("reward: " ^ string_of_int num_sat ^ "/" ^ string_of_int total);
            Out_channel.flush Out_channel.stdout
          end;
          if Set.Poly.is_empty cexs then begin
            print @@ lazy "*** a genuine solution is found: ";
            print @@ lazy (Ast.CandSol.str_of cand);
            Ok (State.Sat cand)
          end else
            let examples' =
              Set.Poly.union examples (Set.Poly.map ~f:ExClause.normalize_params @@ ExClauseSet.normalize cexs)
            in
            iter examples' candidates
      in
      iter Set.Poly.empty candidates
    | Some num_of_examples -> begin
        (** assume candidates are non-parametric *)
        (** generate a maximal counterexample for each clause that are not satisfied by as much candidate solutions as possible *)
        (*let candidates = List.map ~f:CandSol.to_old candidates in*)
        let examples, spurious_cands =
          let exi_senv = PCSP.Problem.senv_of APCSP.problem in
          Set.Poly.fold ~init:(Set.Poly.empty, Set.Poly.empty)
            ~f:(fun (examples, spurious_cands) clause ->
                let (examples', spurious_cands') =
                  Cex.common_cex_of_clause fenv num_of_examples exi_senv candidates clause in
                Set.Poly.union examples examples',
                Set.Poly.union spurious_cands spurious_cands') @@
          PCSP.Problem.clauses_of APCSP.problem
        in
        let is_genuine_solution cand = not (Set.Poly.mem spurious_cands cand) in
        match List.find candidates ~f:is_genuine_solution with
        | Some cand ->
          print @@ lazy "*** a genuine solution is found: ";
          print @@ lazy (Ast.CandSol.str_of cand);
          Ok (State.Sat cand)
        | None -> 
          print @@ lazy "*************************************";
          print @@ lazy "*** There was no genuine solution ***";
          print @@ lazy "*************************************\n";
          print @@ lazy "*** Counterexamples to the Candidate Solutions:";
          print @@ lazy
            (String.concat ~sep:";\n"
             @@ Set.Poly.to_list
             @@ (Set.Poly.map ~f:ExClause.str_of examples));
          print @@ lazy "";
          Ok (State.of_examples vs (pos, neg, Set.Poly.union und examples))
      end

  let run_phase (e : State.s) : State.u Or_error.t = State.Monad_infix.(Ok e >>=? validate)
end

let make config pcsp =
  (module Make (struct let config = config end)
       (struct let problem = pcsp end) : ValidatorType)
