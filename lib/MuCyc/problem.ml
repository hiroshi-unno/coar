open Core
open Common.Ext
open Ast
open Ast.LogicOld
open Config

type t = {
  env : sort_env_map;
  lemmas : Lemma.t Set.Poly.t;
  defs : MuCLP.Pred.t list;
  goals : (Sequent.t * int option * bool (*whether it is a hard goal *)) list;
}

type solver = t -> MuCLP.Problem.solution * ProofTree.t list

(** {6 Constructors} *)

let make env lemmas defs goals = { env; lemmas; defs; goals }

let of_muclp muclp =
  let exi_senv = Term.pred_to_sort_env_map @@ MuCLP.Problem.penv_of muclp in
  let senv, query =
    LogicOld.Formula.rm_quant ~forall:true @@ Formula.aconv_tvar muclp.query
  in
  {
    env = Map.of_set_exn senv;
    lemmas = Set.Poly.empty;
    defs = muclp.preds;
    goals =
      List.map ~f:(fun g -> (g, None, true))
      @@ Set.to_list
      @@ Sequent.of_formula exi_senv
      @@ query;
  }

(** {6 Destructors} *)

let let_ problem = (problem.env, problem.lemmas, problem.defs, problem.goals)

let to_muclp defs sequents =
  MuCLP.Problem.make defs @@ Formula.and_of
  @@ List.map ~f:Sequent.to_formula sequents

let to_formula defs sequents =
  Formula.and_of
  @@ List.map ~f:MuCLP.Pred.to_formula defs
  @ List.map ~f:Sequent.to_formula sequents

(** {6 Inspectors} *)

(*let pvs problem =
  let_ problem |> fun (_env,lemmas,defs,goals) ->
  HCCS.pvs defs @
  (List.concat_map Sequent.pvs sequents) @
  (List.concat_map ~f:(fun elem -> Sequent.pvs elem.sequent) lemmas)

  let ufuns problem =
  let_ problem |> fun (_env,_lemmas,defs,_goals) ->
  HCCS.ufuns defs*)

(** {6 Operators} *)

let subst tsub problem =
  {
    problem with
    lemmas = Set.Poly.map ~f:(Lemma.subst tsub) problem.lemmas;
    defs = List.map ~f:(MuCLP.Pred.subst tsub) problem.defs;
    goals =
      List.map ~f:(fun (g, t, h) -> (Sequent.subst tsub g, t, h)) problem.goals;
  }

let apply_as_muclp f problem =
  let muclp =
    f @@ to_muclp problem.defs @@ List.map problem.goals ~f:(fun (g, _, _) -> g)
    (*ToDo*)
  in
  let exi_senv = Term.pred_to_sort_env_map @@ MuCLP.Problem.penv_of muclp in
  {
    problem with
    defs = MuCLP.Problem.preds_of muclp;
    goals =
      List.map ~f:(fun g -> (g, None (*ToDo*), true (*ToDo*)))
      @@ Set.to_list
      @@ Sequent.of_formula exi_senv
      @@ MuCLP.Problem.query_of muclp;
  }

let simplify problem =
  {
    problem with
    defs = MuCLP.Pred.map_list Evaluator.simplify problem.defs;
    goals =
      List.map ~f:(fun (g, t, h) -> (Sequent.simplify g, t, h)) problem.goals;
  }

(*let tenv, dcs = HCCS.infer problem.env problem.dcs in
  let dcs =
  dcs
  |> HCCS.simplify_light []
  |> HCCS.simplify_full ~tenv []
  |> HCCS.simplify_lv2 ~tenv
  in
  {problem with dcs = dcs}*)
let reduce problem = problem (*ToDo*)

(*try apply_on_hcs (HCSSolver.Reduce.reduce (fun _ -> false)) problem with Failure _ -> problem*)
let slice_forward problem = problem (*ToDo*)

(*try apply_on_hcs HCSSolver.SliceForward.slice problem with Failure _ -> problem*)
let slice_backward problem = problem
(*ToDo*)
(*try apply_on_hcs HCSSolver.SliceBackward.slice problem with Failure _ -> problem*)

(** {6 Lemma/Conjecture Generators} *)

let gen_lemmas ~print problem =
  let lemmas = Lemma.generate_from_preds problem.defs in
  print
  @@ lazy
       (Format.asprintf
          "@.:: Extracting lemmas from the definition of predicates...done@.  \
           %a@.@."
          (Lemma.pr_list ~wo_guard:true)
          (Set.to_list lemmas));
  { problem with lemmas = Set.union lemmas problem.lemmas }

let gen_determ_conjs ~print ~config problem =
  let conjs = Sequent.generate_determinacy_conjecture problem.defs in
  print
  @@ lazy
       (Format.asprintf
          "@.:: Extracting conjectures from the definite clause...done@.  \
           %a@.@."
          (List.pr Sequent.pr ",@;") conjs);
  {
    problem with
    goals =
      List.map
        ~f:(fun g -> (g, Some config.timeout_prove_each_conj, false))
        conjs
      @ problem.goals;
  }

(** {6 Printers} *)

let pr ppf problem =
  Format.fprintf ppf
    "@[<v 2>Lemmas:@;%a@]@;@[<v 2>Predicates:@;%a@]@;@[<v 2>Sequents:@;%a@]@;"
    (Lemma.pr_list ~wo_guard:true)
    (Set.to_list problem.lemmas)
    MuCLP.Pred.pr_list problem.defs (List.pr Sequent.pr "@,")
    (List.map ~f:(fun (g, _, _) -> g) problem.goals)

(*
(** {6 Type Inference Algorithm} *)

let infer problem =
  let_ problem |> fun (env,lemmas,defs,goals) ->
  let tenv =
    (List.concat_map Sequent.fvs sequents |> TypEnv.of_vars) @
    env @ (* HCCS.ktenv dcs @ *) (pvs problem |> TypEnv.of_vars) @ (ufuns problem |> TypEnv.of_vars)
  in
  let constr1, lemmas' = List.map (Lemma.cgen_elem tenv) lemmas |> List.split in
  let constr2, defs' = HCCS.cgen tenv defs in
  let constr3, goals' = List.map (Sequent.cgen tenv) goals |> List.split in
  let tsub =
    try
      Type.unify @@
      (List.flatten constr1) @ constr2 @ (List.flatten constr3)
    with AbsTerm.CannotUnify ->
      sprintf "unification error:@.  %a@.  %a@." TypEnv.pr tenv pr problem;
      assert false
  in
  let tenv' = TypEnv.subst tsub tenv in
  tenv', subst tsub @@ make tenv' lemmas' defs' goals'
*)
