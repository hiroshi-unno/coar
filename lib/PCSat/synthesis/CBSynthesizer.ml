(* The classification-based synthesis phase of PCSat's CEGIS loop: for every
   labelling the labeling phase produced, learn one classifier per unknown
   -- the well-founded, functional or ordinary classifier according to its
   kind -- from the truth table and that labelling, and combine them into
   candidates (the product of each unknown's classifiers).  A candidate
   holds on the labelled examples by construction, not on the clauses;
   validation decides that.  Any classifier's error fails the whole phase. *)
open Core
open Common
open Common.Ext
open Common.Util
open Ast
open PCSatCommon
open Classification

module Config = struct
  type t = {
    verbose : bool; [@default false]
    classifier : Classifier.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/pcsat/classifier/bfsb_nn.json"]
    wf_classifier : WFClassifier.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/pcsat/classifier/wf_dt.json"]
    fn_classifier : FNClassifier.Config.t ext_file; [@default Common.Util.ExtFile.Filename "./config/pcsat/classifier/fn_tb.json"] (*with_lb: bool*)
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

(* A kind is discharged by building candidates only from a family whose every
   member has it, and validation checks the clauses alone, never the kind.
   This synthesizer has such a family for [WF] (the well-founded classifier)
   and [FN] (the functional classifier) only; every other predicate unknown
   gets the ordinary classifier, whose candidates satisfy the labelled
   examples and nothing more.  So for any other kind that is an obligation of
   the problem, a candidate the validator accepts solves the clauses and may
   break the kind: a predicate declared total over its first argument and
   occurring only negatively, [P(x,y) => x < y < x+1] over the integers, got
   the candidate [false], which satisfies the clause and is not total,
   although no total [P] exists.
   [guarantees_kind k]: every candidate this synthesizer builds for an
   unknown of kind [k] has the kind, or [k] states no obligation beyond the
   clauses.  True of [Ord], [WF], [FN]; of a [Uniq] the clauses entail or the
   least model gives (it restricts the search and adds no obligation, so a
   solution of the clauses is a solution of the problem); and of the function
   kinds, which state no condition on a predicate.  False of [Tot]
   (non-emptiness included), a declared [Uniq], [DWF], [NWF], [Parity],
   [Adm] and [Integ].  A [sat] whose solution gives such an unknown a body
   must have that body's kind re-checked before it is reported.
   [kind_checkable k]: the obligation of [k] can be asked of a given body
   (as a first-order validity question, or against a ranking certificate);
   false of [Adm] and [Integ], for which no question exists. *)
let guarantees_kind = function
  | Kind.Ord | Kind.FN | Kind.WF
  | Kind.Uniq (_, (Kind.Entailed | Kind.LeastModel))
  | Kind.IntFun | Kind.RealFun | Kind.RegEx ->
      true
  | Kind.Tot _ | Kind.Uniq (_, Kind.Declared) | Kind.DWF | Kind.NWF _
  | Kind.Parity _ | Kind.Adm _ | Kind.Integ ->
      false

let kind_checkable = function Kind.Adm _ | Kind.Integ -> false | _ -> true

module Make (Cfg : Config.ConfigType) (APCSP : PCSP.Problem.ProblemType) =
struct
  let config = Cfg.config
  let id = PCSP.Problem.id_of APCSP.problem

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_id id

  (* Refuses, as an unsupported input that the solver reports as [unknown],
     a problem with an unknown whose kind this synthesizer does not guarantee
     and no checker can re-verify ([guarantees_kind], [kind_checkable]): its
     candidate's kind could be wrong and nothing would notice.  It is called
     when the first candidate is to be built, not when this module is built,
     since the stages before the first synthesis round can already decide the
     problem and their answers do not depend on this synthesizer.
     Assumes: [APCSP.problem] is the problem the loop solves.  Guarantees:
     after it returns, every unknown of [APCSP.problem] either has a kind
     every candidate of this synthesizer has, or one whose obligation the
     solver re-checks on a [sat] before reporting it. *)
  let refuse_unhonoured_kinds () =
    let unhonoured =
      Map.Poly.fold (PCSP.Problem.senv_of APCSP.problem) ~init:[]
        ~f:(fun ~key ~data:_ acc ->
          let kind = PCSP.Problem.kind_of APCSP.problem key in
          if guarantees_kind kind || kind_checkable kind then acc
          else (key, kind) :: acc)
    in
    if not (List.is_empty unhonoured) then
      raise
        (PCSP.Problem.NoTemplate
           (sprintf
              "the classification-based synthesizer builds candidates of no \
               kind but ordinary, well-founded and functional, and no checker \
               re-verifies %s; use a template-based PCSat configuration"
              (String.concat_map_list ~sep:", " (List.rev unhonoured)
                 ~f:(fun (v, k) ->
                   sprintf "%s (%s)" (Ident.name_of_tvar v) (Kind.str_of k)))))

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
    let table = vs.VersionSpace.truth_table in
    let labeling =
      match Map.Poly.find labeling pvar with
      | None -> Map.Poly.empty
      | Some labeling -> labeling
    in
    let examples = vs.examples in
    let senv =
      Logic.to_old_sort_env_map @@ PCSP.Problem.senv_of APCSP.problem
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
    refuse_unhonoured_kinds ();
    let open State.Monad_infix in
    Ok (State.lift e) >>=? fun vs _ ->
    let labelings = vs.labelings in
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
