open Core
open Common.Ext
open Ast
open Ast.LogicOld
open Config

type t = {
  env : sort_env_map;
  lemmas : EntailmentLemma.t Set.Poly.t;
  defs : MuCLP.Pred.t list;
  goals : (Sequent.t * int option * bool (*whether it is a hard goal *)) list;
  dtenv : (string, Datatype.t) Map.Poly.t;
}

type solver = t -> Common.Verdict.t * EntailmentProofTree.t list

(** {6 Constructors} *)

let make ?(dtenv = Map.Poly.empty) env lemmas defs goals =
  { env; lemmas; defs; goals; dtenv }

let of_muclp ?(dtenv = Map.Poly.empty) muclp =
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
    dtenv;
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
    lemmas = Set.Poly.map ~f:(EntailmentLemma.subst tsub) problem.lemmas;
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
    defs = muclp.preds;
    goals =
      List.map ~f:(fun g -> (g, None (*ToDo*), true (*ToDo*)))
      @@ Set.to_list
      @@ Sequent.of_formula exi_senv
      @@ muclp.query;
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
  let lemmas = EntailmentLemma.generate_from_preds problem.defs in
  print
  @@ lazy
       (Format.asprintf
          "@.:: Extracting lemmas from the definition of predicates...done@.  \
           %a@.@."
          (EntailmentLemma.pr_list ~wo_guard:true)
          (Set.to_list lemmas));
  { problem with lemmas = Set.union lemmas problem.lemmas }

(** [add_user_lemmas ~timeout lemmas problem]: [problem] with each lemma a
    user stated -- a closed formula over [problem]'s predicates, such as
    [forall x y r. mult(x, y, r) => mult(x - 1, y, r - y)] -- added as a
    {e conjecture}: a soft goal, tried with [timeout] seconds before the
    problem's own goals, in the order given.  Nothing here assumes a lemma.
    The search ([InductiveEntailmentSearch.solve]) adds a soft goal to the
    lemmas the later goals may apply only when its proof tree is valid, that
    is when the lemma has been proved of the least fixpoint by the same rules,
    using only the lemmas proved before it; an unproved one is dropped and
    changes no verdict.  So a false lemma costs time and never an answer.

    A lemma is refused (returned in the second component, with the reason)
    when it mentions a predicate [problem] does not define with the same
    argument sorts: the preprocessing before this point may have eliminated
    or reshaped the predicate it names, and such a lemma would be a claim
    about nothing the search unfolds.  Guarantee: the goals of the result are
    those of [problem] preceded by one soft goal per sequent of each accepted
    lemma (a lemma whose conclusion is a conjunction becomes several). *)
let add_user_lemmas ~timeout lemmas problem =
  let penv =
    Map.Poly.of_alist_reduce ~f:(fun a _ -> a)
    @@ List.map problem.defs ~f:(fun (p : MuCLP.Pred.t) ->
        (p.name, List.map ~f:snd p.args))
  in
  let accepted, refused =
    List.partition_map lemmas ~f:(fun phi ->
        let missing =
          Set.to_list
          @@ Set.filter (Formula.pred_sort_env_of phi) ~f:(fun (pvar, sorts) ->
              match Map.Poly.find penv pvar with
              | Some sorts' -> not (List.equal Stdlib.( = ) sorts sorts')
              | None -> true)
        in
        if List.is_empty missing then First phi
        else
          Second
            ( phi,
              sprintf "no predicate %s with these argument sorts is defined"
              @@ String.concat_map_list ~sep:", " missing ~f:(fun (pvar, _) ->
                  Ident.name_of_pvar pvar) ))
  in
  let exi_senv = Term.pred_to_sort_env_map penv in
  let conjs =
    List.concat_map accepted ~f:(fun phi ->
        List.map ~f:(fun seq -> (seq, Some timeout, false))
        @@ Set.to_list
        @@ Sequent.of_formula exi_senv
        @@ Formula.aconv_tvar phi)
  in
  ({ problem with goals = conjs @ problem.goals }, refused)

(** [containment_of phi]: [Some (k, w)] when the formula [phi] is, up to
    its universal prefix, a containment [k(x~) => w(x~)] (or
    [not k(x~) \/ w(x~)]) of two distinct predicates over one list of
    pairwise distinct variables, and [None] otherwise. *)
let containment_of phi =
  let _, phi = Formula.rm_quant ~forall:true phi in
  let atoms =
    match phi with
    | Formula.BinaryOp (Formula.Imply, Formula.Atom (k, _), Formula.Atom (w, _), _)
    | Formula.BinaryOp
        ( Formula.Or,
          Formula.UnaryOp (Formula.Not, Formula.Atom (k, _), _),
          Formula.Atom (w, _),
          _ ) ->
        Some (k, w)
    | _ -> None
  in
  Option.bind atoms ~f:(fun (k, w) ->
      if not (Atom.is_pvar_app k && Atom.is_pvar_app w) then None
      else
        let kp, _, kargs, _ = Atom.let_pvar_app k in
        let wp, _, wargs, _ = Atom.let_pvar_app w in
        let vars ts =
          Option.all
          @@ List.map ts ~f:(function
            | Term.Var (x, _, _) -> Some x
            | _ -> None)
        in
        match (vars kargs, vars wargs) with
        | Some xs, Some ys
          when Stdlib.(kp <> wp)
               && List.equal Ident.tvar_equal xs ys
               && not (List.contains_dup ~compare:Ident.tvar_compare xs) ->
            Some (kp, wp)
        | _ -> None)

(** [generalise_goals_by_containment ~timeout lemmas problem]: [problem]
    with one more conjecture per hard goal [S] whose left side has an atom
    on a predicate [K] for which a containment lemma [K(x~) => W(x~)] is
    among [lemmas] ([containment_of]): [S] with every such left atom renamed
    to [W] (the first containment given for [K]), tried with [timeout]
    seconds after the soft goals already there and before the hard goals.

    Contract.  Write [S'] for the renamed sequent.  If [K ⊆ W] in the least
    model and [S'] holds there, so does [S]: a valuation satisfying [S]'s
    left side satisfies [S']'s, since each renamed atom is a premise and
    [K(t~)] gives [W(t~)], and the two sequents have the same right side.
    [S'] can be false where [S] holds ([W] larger than [K] admits more
    premises), which is why it is only a conjecture: the search uses it as
    a lemma only once it has proved it, so it changes no verdict, and with
    the containments proved too, Apply adds the [W] atoms to the goal and
    then [S']'s conclusion.  Nothing is assumed and no rule of the search
    changes.

    Why it is wanted.  A goal about [K] proved by induction on a [K] atom
    gets induction hypotheses about [K]; a lemma about [W] reaches a [K]
    atom only through the containment, so it concludes [W] atoms, and no
    hypothesis about [K] matches them.  [S'] is proved by induction on [W],
    where the lemma's conclusions and the hypotheses speak about one
    predicate.  (A frontend that copies a function's predicates per call
    site and states a lemma about the function's whole graph [W], with the
    containments of the copies, produces exactly this shape.) *)
let generalise_goals_by_containment ~timeout lemmas problem =
  let rename =
    Map.Poly.of_alist_reduce ~f:(fun a _ -> a)
    @@ List.filter_map lemmas ~f:containment_of
  in
  if Map.Poly.is_empty rename then problem
  else
    let renamed (atm, _) =
      Atom.is_pvar_app atm
      &&
      let p, _, _, _ = Atom.let_pvar_app atm in
      Map.Poly.mem rename p
    in
    let generalised =
      List.filter_map problem.goals ~f:(fun ((seq : Sequent.t), _, is_hard) ->
          if is_hard && List.exists seq.left_atms ~f:renamed then
            Some
              ( {
                  seq with
                  left_atms =
                    Sequent.map_atm ~f:(Atom.rename_pvars rename) seq.left_atms;
                },
                Some timeout,
                false )
          else None)
    in
    let soft, rest =
      List.split_while problem.goals ~f:(fun (_, _, is_hard) -> not is_hard)
    in
    { problem with goals = soft @ generalised @ rest }

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
    (EntailmentLemma.pr_list ~wo_guard:true)
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
  let constr1, lemmas' = List.map (EntailmentLemma.cgen_elem tenv) lemmas |> List.split in
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
