open Core
open Common
open Common.Ext
open Common.Util
open Ast
open PCSatCommon
open Classification

module Config = struct
  type t = {
    verbose : bool;
    classifier : Classifier.Config.t ext_file;
    wf_classifier : WFClassifier.Config.t ext_file;
    fn_classifier : FNClassifier.Config.t ext_file; (*with_lb: bool*)
  }
  [@@deriving yojson]

  let instantiate_ext_files cfg =
    let open Or_error in
    Classifier.Config.load_ext_file cfg.classifier >>= fun classifier ->
    WFClassifier.Config.load_ext_file cfg.wf_classifier >>= fun wf_classifier ->
    FNClassifier.Config.load_ext_file cfg.fn_classifier >>= fun fn_classifier ->
    Ok { cfg with classifier; wf_classifier; fn_classifier }

  module type ConfigType = sig
    val config : t
  end
end

module Make (Cfg : Config.ConfigType) (APCSP : PCSP.Problem.ProblemType) =
struct
  let config = Cfg.config
  let id = PCSP.Problem.id_of APCSP.problem

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_id id
  let init () = () (*ToDo*)

  let classifier =
    let open Or_error in
    ExtFile.unwrap config.classifier >>= fun cfg ->
    Ok
      (module Classifier.Make
                (struct
                  let config = cfg
                end)
                (APCSP) : Classifier.ClassifierType)

  let wf_classifier =
    let open Or_error in
    ExtFile.unwrap config.wf_classifier >>= fun cfg ->
    Ok
      (module WFClassifier.Make
                (struct
                  let config = cfg
                end)
                (APCSP) : WFClassifier.WFClassifierType)

  let fn_classifier =
    let open Or_error in
    ExtFile.unwrap config.fn_classifier >>= fun cfg ->
    Ok
      (module FNClassifier.Make
                (struct
                  let config = cfg
                end)
                (APCSP) : FNClassifier.FNClassifierType)

  let mk_candidate vs labeling (tvar, sort) =
    let wf = PCSP.Problem.is_wf_pred APCSP.problem tvar in
    let fn = PCSP.Problem.is_fn_pred APCSP.problem tvar in
    let name = Ident.name_of_tvar tvar in
    let pvar = Ident.Pvar name in
    let table = VersionSpace.truth_table_of vs in
    let labeling =
      match Map.Poly.find labeling pvar with
      | None -> Map.Poly.empty
      | Some labeling -> labeling
    in
    let examples = VersionSpace.example_graph_of vs in
    let senv =
      Logic.to_old_sort_env_map
      @@ PCSP.Problem.senv_of APCSP.problem
    in
    Debug.print
    @@ lazy
         (sprintf
            (if wf then "  synthesizing a well-founded predicate for [%s]:"
             else if fn then "  synthesizing a functional predicate for [%s]:"
             else "  synthesizing a predicate for [%s]:")
            name);
    let params =
      Logic.Sort.args_of sort
      |> List.map ~f:Logic.ExtTerm.to_old_sort
      |> LogicOld.sort_env_list_of_sorts
    in
    let open Or_error in
    if wf then
      wf_classifier
      >>= fun (module WFClassifier : WFClassifier.WFClassifierType) ->
      WFClassifier.mk_classifier pvar params table labeling (senv, examples)
    else if fn then
      fn_classifier
      >>= fun (module FNClassifier : FNClassifier.FNClassifierType) ->
      FNClassifier.mk_classifier pvar params table labeling (senv, examples)
    else
      classifier >>= fun (module Classifier : Classifier.ClassifierType) ->
      Classifier.mk_classifier pvar params table labeling (senv, examples)

  let run_phase _iters e =
    let open State.Monad_infix in
    Ok (State.lift e) >>=? fun vs _ ->
    let labelings = VersionSpace.labelings_of vs in
    let open Debug in
    print @@ lazy "********************************************";
    print @@ lazy "***** Classification Based Synthesizer *****";
    print @@ lazy "********************************************";
    let open Or_error in
    List.mapi labelings ~f:(fun i (labeling, sample_examples) ->
        print
        @@ lazy
             (sprintf "Classification for the %s Labeling:"
             @@ Ordinal.string_of @@ Ordinal.make i);
        PCSP.Problem.senv_of APCSP.problem
        |> Map.Poly.to_alist
        |> List.map ~f:(mk_candidate (State.version_space_of e) labeling)
        |> Result.all
        >>= fun res ->
        Ok
          (List.n_cartesian_product res
          |> List.map ~f:(fun res ->
                 let paramss, cand = List.unzip res in
                 let cand =
                   CandSol.of_old
                     (Map.force_merge_list paramss, Set.Poly.of_list cand)
                 in
                 print @@ lazy "  Learned Classifier:";
                 print @@ lazy (CandSol.str_of cand);
                 print @@ lazy "********************************************";
                 (cand, CandSol.Total sample_examples))))
    |> Result.all
    (* ToDo: errors can be tolerated *) >>= fun candss ->
    Ok (State.Continue (vs, List.concat candss))
end
