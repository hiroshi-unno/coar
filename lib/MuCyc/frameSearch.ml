(* The frame-based proof search of Takeshi Tsukada and Hiroshi Unno,
   "Inductive Approach to Spacer", PLDI 2024 (doi:10.1145/3656457): a
   Spacer-style search whose frames over-approximate the least fixpoint,
   refined by interpolation.  Selected by [proof_search: Frame_search]. *)

open Core
open Config
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld
open Effect.Shallow
open Interpolation.SpacerBlocking

(* A refinement step that finds no interpolant leaves the search undecided,
   which is an answer ([Verdict.Unknown]) and not an internal error: the
   interpolation it asks for is incomplete (array MBP in particular), and the
   search it belongs to was never promised to conclude. *)
exception Search_undecided of string

(* Raised under [config.query_reuse_refute] when a re-posed query returns a
   counterexample, and turned into [Refuted] by the root [refine], which also
   decides whether the shortcut is sound for the problem at hand. *)
exception Reposed_query_refuted

(* With [COAR_MUCYC_PHASE_TIME] set, the run keeps the wall-clock account of
   [Common.PhaseTime] (printed on stderr at exit or on SIGTERM), so that the
   time outside interpolation can be split among the search's phases and the
   preparation before it without a profiler.  A computation wrapped in a phase
   must not perform the search's [Yield] effect, or the phase would be charged
   for the time it is suspended.  Off, each phase is one boolean test.
   Observation only. *)
let () =
  if Option.is_some (Sys.getenv "COAR_MUCYC_PHASE_TIME") then
    Common.PhaseTime.enable ()

let phase_time = Common.PhaseTime.with_phase

let args_of penv pvar = List.Assoc.find_exn ~equal:Stdlib.( = ) penv pvar

let str_of_head = function
  | None -> "root"
  | Some pvar -> Ident.name_of_pvar pvar

let str_of_head_with_args penv =
  Option.value_map ~default:"root" ~f:(fun pvar ->
      Atom.str_of
      @@ Atom.mk_pvar_app pvar
           (List.map ~f:snd @@ args_of penv pvar)
           (Term.of_sort_env @@ args_of penv pvar))

let def_of penv defs pvar =
  match MuCLP.Pred.lookup defs pvar with
  | Some (Mu, args, body) ->
      Formula.rename (ren_of_sort_env_list args (args_of penv pvar)) body
  | _ -> failwith "FrameSearch.def_of"

exception No_clausal_form of Ident.pvar * string

(* [seq_map_of penv problem]: the goals' sequents and, for each predicate,
   the sequents of [body => head].  [Error] when a definition has no clausal
   form -- a body with a universal over a predicate occurrence, as in
   [Main z =mu forall a. ... \/ Q a], is a non-Horn clause body that the
   clausal form refuses -- naming the predicate; the frame search is not
   attempted on such a problem. *)
let seq_map_of penv (problem : Problem.t) =
  let exi_senv =
    Term.pred_to_sort_env_map @@ Map.Poly.of_alist_exn
    @@ List.map penv ~f:(fun (pvar, args) -> (pvar, List.map ~f:snd args))
  in
  let def_seqs pvar =
    match
      Sequent.of_formula exi_senv
      @@ Formula.mk_imply
           (def_of penv problem.defs pvar)
           (Formula.mk_atom @@ Atom.pvar_app_of_senv pvar @@ args_of penv pvar)
    with
    | exception Failure msg -> raise (No_clausal_form (pvar, msg))
    | seqs -> seqs
  in
  match
    Map.Poly.of_alist_exn
    @@ ( None,
         List.sort_by (fun seq -> List.length seq.Sequent.left_atms)
         @@ List.map problem.goals ~f:(fst3 >> Sequent.normalize_body) )
       :: List.map penv ~f:(fun (pvar, _) ->
           ( Some pvar,
             List.sort_by (fun seq -> List.length seq.Sequent.left_atms)
             @@ List.map ~f:Sequent.normalize_body
             @@ Set.to_list @@ def_seqs pvar ))
  with
  | exception No_clausal_form (pvar, msg) ->
      Or_error.error_string
      @@ sprintf
           "MuCyc cannot handle the definition of %s: it has no clausal form \
            (%s); use MuVal or MuStrat"
           (Ident.name_of_pvar pvar) msg
  | seq_map -> Ok seq_map

let formula_of seq_map pvar_opt =
  Formula.or_of
  @@ List.map ~f:(fun seq ->
      Formula.negate @@ Sequent.to_formula { seq with Sequent.right_atms = [] })
  @@ Map.Poly.find_exn seq_map pvar_opt

(* The variables of [senv] that Z3's model [model] leaves without a value:
   absent from it, or listed without one.  Z3's SMT core builds its model
   from the terms relevant to the satisfied formula (an atom is relevant when
   the Boolean structure above it needs its value), so these variables are
   ones the satisfying assignment does not depend on; [convert_model] then
   gives them a default value. *)
let absent_of senv model =
  let valued =
    List.filter_map model ~f:(function
      | (x, _), Some _ -> Some x
      | _, None -> None)
    |> Set.Poly.of_list
  in
  Set.Poly.filter_map senv ~f:(fun (x, _) ->
      if Set.mem valued x then None else Some x)

let qelim ~config phi =
  let res =
    phase_time "qelim" @@ fun () ->
    (*Normalizer.normalize @@*)
    Evaluator.simplify
    @@ Z3Smt.Z3interface.qelim ~id:None ~fenv:(LogicOld.get_fenv ()) phi
  in
  assert ((not config.check_validity) || Formula.is_quantifier_free res);
  res

let qelim_except ~config ?(exists = true) args phi =
  let res = qelim ~config @@ snd @@ Formula.quantify_except ~exists args phi in
  assert (
    (not config.check_validity) || Set.is_subset (Formula.fvs_of res) ~of_:args);
  res

(* The muCLP problem in the form of PPDP 2009's unwinding: each [Mu]
   definition [P(x) =mu G] as the clause [P(x) <= G], and each goal sequent
   as its clause formula.  Pre: every predicate of [penv] has a [Mu]
   definition (the solver refuses any other kind before the search). *)
let unwinding_system_of penv (problem : Problem.t) : Interpolation.Unwinding.system =
  {
    preds =
      List.map penv ~f:(fun (pvar, _) ->
          match MuCLP.Pred.lookup problem.defs pvar with
          | Some (Predicate.Mu, args, body) -> (pvar, args, body)
          | _ -> failwith "[FrameSearch.expand]");
    goals = List.map problem.goals ~f:(fun (seq, _, _) -> Sequent.to_formula seq);
  }

(* What one refinement step yields: [Interpolation.Unwinding.step].  The three
   cases are NOT two: [Refuted] is a genuine refutation of the sub-problem --
   the constraint solver proved there is no counterexample, and the caller may
   conclude the property fails -- while [Undecided] is the constraint solver
   failing to decide, which the caller must not read the same way.
   Collapsing them, by giving an undecided sub-query the same "no
   counterexample" answer a refutation gets, turns "we could not tell" into a
   definite verdict. *)
type 'a step = 'a Interpolation.Unwinding.step =
  | Refined of 'a
  | Refuted
  | Undecided of Common.Verdict.t

(* The [Solve] strategy: the uniform-depth expansion of the problem to the
   trace's depth solved by [solve_chc] ([Interpolation.Unwinding.solve_frames]),
   its solutions becoming the new frames. *)
let solve ~config penv solve_chc problem (trace1, trace2) =
  match
    Interpolation.Unwinding.solve_frames ~qelim:(qelim ~config)
      ~dtenv:problem.Problem.dtenv
      (unwinding_system_of penv problem)
      solve_chc trace2
  with
  | Refined trace2 -> Refined ((trace1, trace2), Map.Poly.empty)
  | Refuted -> Refuted
  | Undecided verdict -> Undecided verdict

(* Model-based projection with the two choices for conditionals and let-bound
   definitions inside terms; see [Interpolation.MbpProject.get_mbp_with]. *)
let get_mbp_with = Interpolation.MbpProject.get_mbp_with

let get_mbp ~config ~print model senv phi =
  phase_time "mbp" @@ fun () ->
  get_mbp_with ~conditionals:config.Config.projection_conditionals
    ~lets:config.Config.projection_lets
    ~bv_reuse_unchanged_prepass:config.Config.bv_reuse_unchanged_prepass
    ~bv_normalize_once:config.Config.bv_normalize_once
    ~bv_joint_alias_in_projection:config.Config.bv_joint_alias_in_projection
    ~check_validity:config.Config.check_validity ~print model senv phi

(* What the [MBP] counterexample strategy projects at [model] (over [senv]):
   [phi] itself, or with [mbp_implicant] an implicant of [phi] at [model]
   ([implicant] after [bit2bool], every conjunct and one true disjunct, the
   way Spacer takes the implicant of a rule's body before projecting it).  An
   implicant implies [phi] and is true at [model], so a projection of it
   (true at the model, implying its existential closure over the eliminated
   variables) is a projection of [phi] too.  The [let] variables the
   implicant names come back in the returned model and environment, to be
   eliminated with the rest: each comes with its defining equality, so
   closing over it changes nothing.  With [mbp_implicant_lift_ite] the
   implicant also lifts conditional terms by the model (see [implicant]),
   still an implicant; with [mbp_implicant_partial] it prefers the
   disjuncts forced by the variables outside [absent] (those to which the
   solver's model gives no value; [model] fills them with defaults).  When
   no implicant can be taken (a quantifier, a variable the model leaves
   out) [phi] is returned whole. *)
let mbp_input ?(absent = Set.Poly.empty) ~config ~print ~eliminated model senv
    phi =
  if not config.Config.mbp_implicant then (model, senv, phi)
  else
    (* With COAR_MUCYC_PHASE_TIME set, a census of where the implicant and its
       two sub-switches act: [imp-call] counts the bodies reaching it,
       [imp-fallback] those projected whole because no implicant was found,
       [imp-opened] those whose literals the one-bit opening changes,
       [imp-sliced] those losing a definition to [slice_defs], and
       [imp-folded] those in which [fold_lets] finds a [let] variable fixed to
       a numeral.  Observation only. *)
    try
      Common.PhaseTime.event "imp-call";
      let lets = ref Map.Poly.empty in
      let env = Map.Poly.map model ~f:Evaluator.eval_term in
      let dtenv = get_dtenv () in
      let absent =
        if config.Config.mbp_implicant_partial then absent else Set.Poly.empty
      in
      let lift_late =
        config.Config.mbp_implicant_lift_ite
        && config.Config.mbp_implicant_lift_after_slice
        && config.Config.mbp_implicant_slice_defs
      in
      let lift_ite = config.Config.mbp_implicant_lift_ite && not lift_late in
      let one_bit t =
        (not (T_bv.is_bvnum t))
        && match Term.sort_of t with
           | T_bv.SBV size -> T_bv.bits_of size = 1
           | _ -> false
      in
      let opened t1 t2 ~equal =
        let env = Map.force_merge env !lets in
        match Term.of_value dtenv @@ Evaluator.eval_term ~env t1 with
        | Term.FunApp (T_bv.BVNum (_, k), [], _) ->
            let num k = T_bv.mk_bvnum ~size:(Some 1) k in
            Some
              ( env,
                Formula.nnf_of @@ bit2bool
                @@ Formula.mk_and
                     (Formula.eq t1 (num k))
                     (Formula.eq t2 (num (if equal then k else Z.(one - k))))
              )
        | _ -> None
      in
      (* a one-bit equality [t1 = t2] of two non-numerals, true at the model
         with [t1] at [k], is replaced by the implicant of [t1 = k /\ t2 = k]
         after [bit2bool] (a disequality likewise, by [t2 = 1-k]): stronger,
         true at the model, and it opens a circuit defining a variable, which
         [bit2bool] alone leaves inside its equality *)
      let rec open_defs lits =
        List.concat_map lits ~f:(fun l ->
            let split t1 t2 ~equal =
              if one_bit t1 && one_bit t2 then
                match opened t1 t2 ~equal with
                | Some (env, phi) ->
                    open_defs @@ implicant ~lift_ite ~absent ~lets env phi
                | None -> [ l ]
              else [ l ]
            in
            match l with
            | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _)
              ->
                split t1 t2 ~equal:true
            | Formula.Atom
                (Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _), _)
            | Formula.UnaryOp
                ( Formula.Not,
                  Formula.Atom
                    (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _),
                  _ ) ->
                split t1 t2 ~equal:false
            | _ -> [ l ])
      in
      let lits =
        implicant ~lift_ite ~absent ~lets env @@ Formula.nnf_of @@ bit2bool phi
      in
      (* with [mbp_implicant_slice_defs]: drop each unused definition
         [y = t] of an eliminated variable (see the field's comment); a
         [let] variable is always eliminated.  Dropping one may leave the
         variables of [t] unused in turn, so a variable whose count of
         mentioning literals falls to one is looked at again *)
      let slice ~what lits =
        if not config.Config.mbp_implicant_slice_defs then lits
        else
          let lits = Array.of_list lits in
          let alive = Array.map lits ~f:(fun _ -> true) in
          let fvs = Array.map lits ~f:Formula.tvs_of in
          let occ = Hashtbl.Poly.create () in
          Array.iteri fvs ~f:(fun i xs ->
              Set.iter xs ~f:(fun x -> Hashtbl.add_multi occ ~key:x ~data:i));
          let count = Hashtbl.Poly.create () in
          Hashtbl.iteri occ ~f:(fun ~key ~data ->
              Hashtbl.set count ~key ~data:(List.length data));
          let elim x = Map.Poly.mem !lets x || eliminated x in
          let once x =
            match Hashtbl.find count x with Some 1 -> true | _ -> false
          in
          let definition i =
            match lits.(i) with
            | Formula.Atom
                ( Atom.App
                    ( Predicate.Psym T_bool.Eq,
                      [ (Term.Var (y, _, _) as v); t ],
                      _ ),
                  _ ) ->
                let def y t =
                  elim y
                  && once y
                  && not (Set.mem (Term.tvs_of t) y)
                in
                def y t
                || (match t with
                   | Term.Var (z, _, _) -> def z v
                   | _ -> false)
            | Formula.Atom
                ( Atom.App
                    (Predicate.Psym T_bool.Eq, [ t; Term.Var (y, _, _) ], _),
                  _ ) ->
                elim y
                && once y
                && not (Set.mem (Term.tvs_of t) y)
            | _ -> false
          in
          let rec visit = function
            | [] -> ()
            | x :: rest ->
                let todo =
                  match Hashtbl.find occ x with
                  | None -> []
                  | Some is -> (
                      match List.filter is ~f:(fun i -> alive.(i)) with
                      | [ i ] when definition i ->
                          alive.(i) <- false;
                          Set.to_list fvs.(i)
                          |> List.filter ~f:(fun z ->
                              Hashtbl.change count z
                                ~f:(Option.map ~f:(fun n -> n - 1));
                              once z)
                      | _ -> [])
                in
                visit (todo @ rest)
          in
          visit
          @@ Hashtbl.fold count ~init:[] ~f:(fun ~key ~data acc ->
              if data = 1 then key :: acc else acc);
          let kept = List.filteri (Array.to_list lits) ~f:(fun i _ -> alive.(i)) in
          print
          @@ lazy
               (sprintf "      sliced %d of %d %s literals"
                  (Array.length lits - List.length kept)
                  (Array.length lits) what);
          if List.length kept < Array.length lits then
            Common.PhaseTime.event "imp-sliced";
          kept
      in
      let lits = slice ~what:"implicant" lits in
      let lits =
        let opened = open_defs lits in
        (* [open_defs] returns a literal it does not split as the same
           physical value, so a physical comparison tells whether any was
           split.  Comparing the printed lists instead costs seconds on large
           bodies, and only in the runs that measure where time goes *)
        if
          !Common.PhaseTime.on
          && not (List.equal phys_equal opened lits)
        then Common.PhaseTime.event "imp-opened";
        opened
      in
      (* with [mbp_implicant_lift_after_slice]: the conditional terms of the
         literals the slice kept, with their one-bit definitions opened, are
         lifted now; each literal is true at the model, so its lifted
         literals are an implicant of it.  Lifting a one-bit circuit before
         it is opened would lift the conditional terms of every operand of
         its [or1], not only of the operand the opening takes.  Lifting drops
         the untaken branches, whose variables may then be read by nothing,
         hence the second slice *)
      let lits =
        if not lift_late then lits
        else
          let env = Map.force_merge env !lets in
          slice ~what:"lifted"
          @@ List.concat_map lits
               ~f:(implicant ~lift_ite:true ~absent ~lets env)
      in
      (* with [mbp_implicant_fold_lets]: a [let] variable that a literal
         fixes to a bit-vector numeral ([x = k], typically left by opening a
         one-bit definition [x = ite (c, 1, 0)] above) is replaced by [k] in
         every other literal, which is then simplified and dropped when it
         becomes [true].  [x = k /\ A[x]] is [x = k /\ A[k]], so the
         conjunction is unchanged.  The [let] variables are removed by the
         projection, and every compound subterm over one of them becomes a
         definition the projection has to remove, each by its own
         substitution and pass over all literals: a [let] variable repeated
         by [concat] into a mask of width [w] makes [w] of them *)
      let lits =
        if not config.Config.mbp_implicant_fold_lets then lits
        else
          let fixed x t =
            if Map.Poly.mem !lets x && T_bv.is_bvnum t then Some (x, t)
            else None
          in
          let fixing = function
            | Formula.Atom
                ( Atom.App
                    (Predicate.Psym T_bool.Eq, [ Term.Var (x, _, _); t ], _),
                  _ ) ->
                fixed x t
            | Formula.Atom
                ( Atom.App
                    (Predicate.Psym T_bool.Eq, [ t; Term.Var (x, _, _) ], _),
                  _ ) ->
                fixed x t
            | _ -> None
          in
          let sub =
            Map.Poly.of_alist_reduce (List.filter_map lits ~f:fixing)
              ~f:(fun t _ -> t)
          in
          if Map.Poly.is_empty sub then lits
          else (
            Common.PhaseTime.event "imp-folded";
            List.filter_map lits ~f:(fun l ->
                if Option.is_some (fixing l) then Some l
                else
                  let l' = Evaluator.simplify @@ Formula.subst sub l in
                  if Formula.is_true l' then None else Some l'))
      in
      let imp = Formula.and_of lits in
      ( Map.force_merge model @@ Map.Poly.map !lets ~f:(Term.of_value dtenv),
        Set.union senv @@ Formula.term_sort_env_of imp,
        imp )
    with e when not (Common.Timer.is_async e) ->
      Common.PhaseTime.event "imp-fallback";
      print @@ lazy (sprintf "      no implicant to project (%s)" (Exn.to_string e));
      (model, senv, phi)

(* the antecedents built for kept solvers, by predicate name and the frame
   substituted into its clause bodies, for the clause map they were built
   from; domain-local.  Contract: an entry is the value the builder returned
   for the same clause map and predicate environment (physically), predicate
   and frame (structurally; [None] for no frame), so a hit returns what a
   rebuild would return provided the builder is a function of these; the
   positional naming of the kept-solver path makes it one.  Emptied past
   [left_memo_cap] entries *)
let left_memo :
    ((Obj.t * Obj.t)
    * (string * Formula.t list option, Formula.t) Hashtbl.t)
    option
    ref
    Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> ref None)

let left_memo_cap = 256

let left_memo_find_or_add seq_map penv key ~build =
  let memo = Stdlib.Domain.DLS.get left_memo in
  let table =
    match !memo with
    | Some ((m, p), table)
      when Stdlib.( == ) m (Obj.repr seq_map) && Stdlib.( == ) p (Obj.repr penv)
      ->
        table
    | _ ->
        let table = Common.Ext.Hashtbl.PolyDeep.create () in
        memo := Some ((Obj.repr seq_map, Obj.repr penv), table);
        table
  in
  match Hashtbl.find table key with
  | Some left -> left
  | None ->
      let left = build () in
      if Hashtbl.length table >= left_memo_cap then Hashtbl.clear table;
      Hashtbl.set table ~key ~data:left;
      left

(* the blocking loop's bit-level checker: [BitFrame] over minisat, which
   the interpolation library must not depend on *)
module Bits : BIT_CHECKER = struct
  include BitFrame

  type lit = Minisat.Lit.t
  type model = (string * int, Z.t) Hashtbl.t

  let lit_equal = Minisat.Lit.equal
end

(* The blocking loop's options for a search under [config]: the switches of
   [config.persistent_frames] the loop reads, and the bit-level checker
   [Bits] with [bit_level] *)
let blocking_options ~config =
  match config.Config.persistent_frames with
  | None -> Interpolation.SpacerBlocking.default_options
  | Some pf ->
      {
        kept_solvers = pf.level_solvers;
        bit_checker =
          (if pf.bit_level then Some (module Bits : BIT_CHECKER) else None);
        lazy_nonlinear = pf.lazy_nonlinear;
        definition_templates = pf.definition_templates;
        lazy_nonlinear_relevant = pf.lazy_nonlinear_relevant;
        leaf_contexts = pf.leaf_contexts;
        leaf_templates = pf.leaf_templates;
        kept_bit_models = pf.kept_bit_models;
        incremental_exit = pf.incremental_exit;
        exit_simple = pf.exit_simple_solver;
        bit_domain = pf.bit_domain;
        bit_domain_pin = pf.bit_domain_pin;
      }

(* An interpolant of [phi1] and [phi2] over [args] by
   [Interpolation.Interpolant.binary] with [config]'s search, leaves and
   post-processing, the CHC solver [solve_chc] and this module's projection
   and quantifier elimination passed in; [session] and [at] are the blocking
   loop's kept state and this call's place in the search.  [None] when there
   is none: the loop or a leaf refuted the query, or every leaf declined and
   a projection was asked for (a quantifier survived elimination).  When
   every leaf declined and no projection was asked for, the failure is
   reported by raising.  [route] is set to the name of the route that
   answered ("blocking <rounds> ...", or "leaves <leaf>" naming the leaf of
   [interpolant_leaves] that answered, "leaves" alone when none did),
   for the timing line of [interpolate].  Without [session] (a call outside
   [search], e.g. the query weakening of [Yield (true, _)]) a fresh one is
   made so that the loop still reads [config]'s options; without [at] it
   keeps no state. *)
let interpolate_untimed ?(route = ref "") ?session ?at ~config ~print solve_chc
    args phi1 phi2 =
  (* writes the query to a file only when COAR_INTERP_DUMP_DIR is set *)
  Interpolation.QueryDump.record args phi1 phi2;
  let session =
    match session with
    | Some _ -> session
    | None ->
        Some
          (Interpolation.SpacerBlocking.create_session
             ~options:(blocking_options ~config) ())
  in
  let leaves = config.interpolant_leaves in
  let observe = function
    | `Leaves ->
        route := "leaves";
        if interp_stage then prerr_endline "interp-stage: leaves route"
    | `Leaf leaf ->
        route := "leaves " ^ Interpolation.Interpolant.leaf_name leaf
    | `Blocking (s : Interpolation.SpacerBlocking.stats) ->
        let phi1_bounds =
          match config.interpolant_search with
          | Spacer_blocking blk -> blk.phi1_bounds
          | Leaves -> false
        in
        let kept_bit_models =
          match config.persistent_frames with
          | Some pf -> pf.kept_bit_models
          | None -> false
        in
        route :=
          (if s.cache_used then
             sprintf
               "blocking %d reused %d of %d in %.3f s exit %.3f s block %.3f \
                s cube %.3f s checks %d skipped %d refuted %d setup %.3f s gc \
                %.3f s call %.3f s"
               s.rounds s.reused s.cached s.seed_secs s.exit_secs s.block_secs
               s.cube_secs s.checks s.skipped s.refuted s.setup_secs s.gc_secs
               s.call_secs
           else
             sprintf
               "blocking %d exit %.3f s block %.3f s cube %.3f s checks %d \
                setup %.3f s gc %.3f s call %.3f s"
               s.rounds s.exit_secs s.block_secs s.cube_secs s.checks
               s.setup_secs s.gc_secs s.call_secs)
          ^ (match s.level with
            | Some j ->
                sprintf " level %d seeded %d pushed %d" j s.level_seeded
                  s.pushed
            | None -> "")
          ^ (match s.solver_level with
            | Some j -> sprintf " kept-solver level %d hit %d" j s.kept_hits
            | None -> "")
          ^ sprintf " first check %.3f s all checks %.3f s sat %d %.3f s"
              s.first_check_secs s.check_secs s.sat_checks s.sat_check_secs
          ^ (if phi1_bounds then sprintf " sat-models %d" s.sat_model_hits
             else "")
          ^
          if kept_bit_models then sprintf " bit-models %d" s.model_answers
          else ""
  in
  match
    Interpolation.Interpolant.binary ~search:config.interpolant_search
      ?session ?at ~project:(get_mbp ~config ~print) ~print ~observe ~leaves
      ~post:config.interpolant_post ~solve_chc ~qelim:(qelim ~config) args
      phi1 phi2
  with
  | Interpolant phi -> Some phi
  | No_interpolant -> None
  | Declined ->
      if List.exists leaves ~f:Interpolation.Interpolant.is_projection then None
      else
        failwith
        @@ sprintf "no interpolant for %s and %s" (Formula.str_of phi1)
             (Formula.str_of phi2)

(* With [COAR_MUCYC_INTERP_TIME] in the environment, each interpolation prints
   an [interp-start: at <s> s phi1 <d> phi2 <d> args <d> digest <s> s] line
   (8-digit MD5 prefixes of the printed formulas and argument names, and the
   seconds spent computing them, which the call's time excludes) and, when it returns, one
   [interp-time: <s> s <outcome> heap <MB> route <route> at <s> s] line on stderr
   (wall clock; the route that answered, see [interpolate_untimed], with the
   number of blocked cubes and the seconds and checks of its stages on the
   blocking route, see [blocking_interpolant]; the OCaml major heap after
   the call, which excludes memory held by Z3), so that a run's time can be split between
   interpolation and the rest, and its memory between OCaml and the solvers,
   without a profiler.  Off, it is one boolean test per call. *)
let interp_time = Option.is_some (Sys.getenv "COAR_MUCYC_INTERP_TIME")

(* [COAR_MUCYC_INTERP_TIME=noz3] keeps the timing and digest lines but drops
   the [interp-overlap:] probe: its own Z3 calls change the solver state the
   search later reads (models, cores), so two runs compared call by call must
   not make them *)
let interp_overlap =
  interp_time
  && not
       (Stdlib.( = ) (Sys.getenv "COAR_MUCYC_INTERP_TIME") (Some "noz3"))

(* seconds since this module was initialised, about the start of the run *)
let interp_time_origin = Common.Clock.now_float ()

let since_origin () =
  Time_float.Span.to_sec
    (Time_float.diff (Common.Clock.now_float ()) interp_time_origin)

let interpolate ?session ?at ~config ~print solve_chc args
    phi1 phi2 =
  phase_time "interp" @@ fun () ->
  if not interp_time then
    interpolate_untimed ?session ?at ~config ~print solve_chc args phi1 phi2
  else
    (* a call still open when the run is killed shows as a start line
       without its [interp-time] line *)
    (* digests of the two sides and the arguments, to tell how often the
       same query is asked again; printing large frames takes a sizeable
       part of a call, so the start line reports those seconds and the
       call's clock starts after them *)
    let digest s = String.prefix (Md5.to_hex (Md5.digest_string s)) 8 in
    let digest_from = Common.Clock.now_float () in
    let digests =
      sprintf "phi1 %s phi2 %s args %s"
        (digest (Formula.str_of phi1))
        (digest (Formula.str_of phi2))
        (digest
           (String.concat ~sep:","
              (List.map args ~f:(fst >> Ident.name_of_tvar))))
    in
    let started = Common.Clock.now_float () in
    prerr_endline
      (sprintf "interp-start: at %.3f s %s digest %.3f s" (since_origin ())
         digests
         (Time_float.Span.to_sec (Time_float.diff started digest_from)));
    let route = ref "" in
    (* [result] is a digest of the interpolant returned, so that two runs
       can be compared call by call *)
    let report ?(result = "-") outcome =
      (* COAR_DIAG_GC_AFTER_INTERP: Z3's estimated allocation before and
         after a full major collection (which runs the finalisers that
         release Z3 objects the OCaml side no longer holds), to tell memory
         Z3 still needs from memory only awaiting the collector.  A
         diagnostic: a collection changes no result *)
      if Option.is_some (Sys.getenv "COAR_DIAG_GC_AFTER_INTERP") then (
        let z3mem_mb () =
          Int64.to_int_exn (Z3.Statistics.get_estimated_alloc_size ())
          / 1_000_000
        in
        let before = z3mem_mb () in
        let t = Common.Clock.now_float () in
        Gc.full_major ();
        prerr_endline
          (sprintf "interp-gc: z3mem %d MB -> %d MB heap %d MB in %.3f s"
             before (z3mem_mb ())
             ((Gc.quick_stat ()).heap_words * (Stdlib.Sys.word_size / 8)
             / 1_000_000)
             (Time_float.Span.to_sec
                (Time_float.diff (Common.Clock.now_float ()) t))));
      prerr_endline
        (sprintf "interp-time: %.3f s %s heap %d MB route %s at %.3f s result %s"
           (Time_float.Span.to_sec
              (Time_float.diff (Common.Clock.now_float ()) started))
           outcome
           ((Gc.quick_stat ()).heap_words * (Stdlib.Sys.word_size / 8) / 1_000_000)
           !route (since_origin ()) result)
    in
    match
      interpolate_untimed ~route ?session ?at ~config ~print solve_chc args phi1
        phi2
    with
    | res ->
        (match res with
        | Some phi -> report ~result:(digest (Formula.str_of phi)) "some"
        | None -> report "none");
        res
    | exception exn ->
        report "raised";
        raise exn

(* [project_counterexample ~config ~print ~mbp ~model_values]: the first answer
   of the steps of [config.counterexample_projections], in order; [mbp] runs the
   model-based projection, [model_values] the site's substitution of model
   values.
   Assumes: both thunks compute a formula implied by the site's counterexample
   condition and true in its model, eliminating what the site eliminates.
   Guarantees: [Mbp] declines by raising a synchronous exception, and the next
   step is then tried; [Model_values] never declines.  When every step
   declined, the last failure is raised (a failure naming the list when it was
   empty).  A timeout or other asynchronous exception is never taken for a
   declined step: without that guard a timeout became a successful projection
   over the model's values.  An exception raised by [model_values]
   propagates. *)
let project_counterexample ~config ~print ~mbp ~model_values =
  let rec go failure = function
    | [] -> (
        match failure with
        | Some e -> raise e
        | None -> failwith "MuCyc: the counterexample projection list is empty")
    | Config.Mbp :: rest -> (
        try mbp () with e when not (Common.Timer.is_async e) -> go (Some e) rest)
    | Config.Model_values :: _ ->
        print
        @@ lazy
             (match failure with
             | Some e ->
                 sprintf
                   "      MBP failed (%s); falling back to the model's values"
                   (Exn.to_string e)
             | None -> "      projecting by the model's values");
        model_values ()
  in
  go None config.Config.counterexample_projections

type frame = Formula.t list
type trace = frame list * frame list
type query = Formula.t
type cex = Formula.t
type induct = (Ident.pvar, Formula.t Set.Poly.t) Map.Poly.t
(* Shared counterexamples, keyed by predicate and, under [Level] sharing, by the
   level of the node that computed them: the number of frames from that node to
   the bottom of the trace, which a trace extension (a new root on top) does not
   change. [None] is the [Global] key. *)
type gcexs = (Ident.pvar * int option, Formula.t Set.Poly.t) Map.Poly.t

type state = {
  trace : trace;
  query : query;
  cex_acc : cex;
  induct : induct;
  gcexs : gcexs;
}

type result_yld = trace * cex * induct * gcexs
type result_ret = trace * cex * induct * gcexs
type _ Effect.t += Yield : state * cex -> state Effect.t

type status =
  | Init
  | Paused of (trace * query * gcexs -> (result_yld, result_ret) Either.t)
  | Done

let empty_trace = ([], [])

let next_trace_of = function
  | _, [] -> failwith "[next_trace_of]"
  | trace1, frame :: trace2 -> (frame :: trace1, trace2)

let prev_trace_of = function
  | [], _ -> failwith "[prev_trace_of]"
  | frame :: trace1, trace2 -> (trace1, frame :: trace2)

let psub_of penv = function
  | _, [] ->
      Map.Poly.of_alist_exn
      @@ List.map penv ~f:(fun (pvar, args) ->
          (pvar, (args, Formula.mk_false () (*ToDo*))))
  | _, frame :: _ ->
      Map.Poly.of_alist_exn
      @@ List.map2_exn penv frame ~f:(fun (pvar, args) phi ->
          (pvar, (args, phi)))

let get_frame = List.hd_exn

let get_formula penv state pvar =
  let frame = get_frame @@ snd @@ state.trace in
  List.find_map_exn (List.zip_exn penv frame) ~f:(fun ((pvar', _), phi) ->
      if Stdlib.(pvar = pvar') then Some phi else None)

let set_formula_to_frame penv frame pvar phi =
  List.map2_exn penv frame ~f:(fun (pvar', _) phi' ->
      if Stdlib.(pvar = pvar') then phi else phi')

let add_formula_to_frame penv frame pvar phi =
  List.map2_exn penv frame ~f:(fun (pvar', _) phi' ->
      if Stdlib.(pvar = pvar') then Formula.and_of [ phi; phi' ] else phi')

let set_formula penv state pvar phi =
  match state.trace with
  | _, [] -> failwith "[set_formula]"
  | trace1, frame :: trace2 ->
      {
        state with
        trace = (trace1, set_formula_to_frame penv frame pvar phi :: trace2);
      }

let add_formula penv state pvar phi =
  set_formula penv state pvar
    (Formula.and_of [ get_formula penv state pvar; phi ])

let propagate_formula penv (trace1, trace2) pvar phi =
  ( trace1,
    List.map trace2 ~f:(fun frame -> add_formula_to_frame penv frame pvar phi)
  )

let empty_induct = Map.Poly.empty

let merge_induct =
  Map.Poly.merge ~f:(fun ~key:_ -> function
    | `Left s | `Right s -> Some s
    | `Both (s1, s2) -> Some (Set.union s1 s2))

(* A Z3 solver and the conversion into its context, for [apply_induct_rule];
   a caller applying the rule many times in a row builds it once *)
let induct_z3 () =
  let cfg = [ ("model", "true") ] in
  let ctx = Z3.mk_context cfg in
  let solver = Z3.Solver.mk_solver ctx None in
  let z3dtenv =
    Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx (LogicOld.get_dtenv ())
  in
  let z3fenv =
    Z3Smt.Z3interface.z3_fenv_of ~id:None ctx [] [] (LogicOld.get_fenv ())
      z3dtenv
  in
  ( solver,
    Z3Smt.Z3interface.of_formula_with_z3fenv ~id:None ctx [] [] z3fenv z3dtenv
  )

(* [relative] (the default) also accepts a candidate [c] of [pvar] that only
   follows from the frame below together with [c] assumed of [pvar]'s own body
   atoms; that second check presumes [c] holds of [pvar] one level down, which
   a caller offering facts the frame below does not carry must not presume *)
let apply_induct_rule ?z3 ?(relative = true) ~print seq_map penv trace induct =
  if Map.Poly.is_empty induct then (trace, induct)
  else
    phase_time "induct" @@ fun () ->
    let solver, convert =
      match z3 with Some z3 -> z3 | None -> induct_z3 ()
    in
    let psub = psub_of penv @@ next_trace_of trace in
    let induct =
      Map.Poly.filter_mapi induct ~f:(fun ~key:pvar ~data ->
          let left = formula_of seq_map (Some pvar) in
          Z3Smt.Z3interface.z3_solver_reset solver;
          Z3Smt.Z3interface.z3_solver_add solver
            [ convert @@ Formula.subst_preds psub left ];
          let phis =
            Set.filter data ~f:(fun right ->
                Z3.Solver.push solver;
                Z3Smt.Z3interface.z3_solver_add solver
                  [ convert @@ Evaluator.simplify_neg right ];
                match Z3Smt.Z3interface.z3_check solver [] with
                | Z3.Solver.UNSATISFIABLE ->
                    Z3.Solver.pop solver 1;
                    true
                | _ when not relative ->
                    Z3.Solver.pop solver 1;
                    false
                | _ -> (
                    (*let psub = Map.Poly.singleton pvar (args_of penv pvar, right) in*)
                    let psub =
                      Map.Poly.mapi psub ~f:(fun ~key ~data:(senv, phi) ->
                          if Ident.pvar_equal key pvar then (senv, right)
                          else (senv, phi))
                    in
                    Z3Smt.Z3interface.z3_solver_add solver
                      [ convert @@ Formula.subst_preds psub left ];
                    match Z3Smt.Z3interface.z3_check solver [] with
                    | Z3.Solver.UNSATISFIABLE ->
                        Z3.Solver.pop solver 1;
                        true
                    | _ ->
                        Z3.Solver.pop solver 1;
                        false))
          in
          if Set.is_empty phis then None else Some phis)
    in
    ( (match trace with
      | _, [] -> failwith "apply_induct_rule"
      | trace1, frame :: trace2 ->
          ( trace1,
            List.map2_exn penv frame ~f:(fun (pvar, _) phi ->
                match Map.Poly.find induct pvar with
                | None -> phi
                | Some phis ->
                    print
                    @@ lazy
                         ("inductive facts for " ^ Ident.name_of_pvar pvar
                        ^ ": "
                         ^ String.concat_map_set ~sep:" /\\ " ~f:Formula.str_of
                             phis);
                    Formula.and_of (phi :: Set.to_list phis))
            :: trace2 )),
      induct )

let add_to_induct induct pvar phis =
  Map.Poly.set induct ~key:pvar
    ~data:
      (match Map.Poly.find induct pvar with
      | Some phis' -> Set.union phis' phis
      | None -> phis)

(* A body atom's argument [t] of a normalized sequent (a fresh variable, see
   [Sequent.normalize_body]) as a term over [params], read off an equation
   among the top-level conjuncts of the sequent's pure part: [t = e], or an
   integer equation solvable for [t] with coefficient 1 or -1.  [t] itself
   when there is none; the caller then drops what still mentions it *)
let resolve_arg params seq t =
  match t with
  | Term.Var (v, sort, _) -> (
      let over_params e = Set.is_subset (Term.tvs_of e) ~of_:params in
      let is_v = function
        | Term.Var (x, _, _) -> Stdlib.(x = v)
        | _ -> false
      in
      let sol phi =
        if not (Formula.is_eq phi) then None
        else
          let l, r, _ = Formula.let_eq phi in
          if is_v l && over_params r then Some r
          else if is_v r && over_params l then Some l
          else if Stdlib.(sort = T_int.SInt) then
            Option.filter (ArrayPointwise.solve_for v l r) ~f:over_params
          else None
      in
      match
        List.find_map (Formula.conjuncts_list_of seq.Sequent.left_phi) ~f:sol
      with
      | Some e -> e
      | None -> t)
  | _ -> t

(* Candidates for [apply_induct_rule] at a frame whose frame below is [lower]:
   for each predicate [q], the conjuncts of [lower]'s formula of [p], for each
   atom [p(ts)] in the body of a clause defining [q], with [p]'s parameters
   replaced by [ts], kept when every free variable is a parameter of [q] (a
   body variable not among them would be read as a different, universally
   quantified one) and when the conjunct is not already one of [frame]'s.
   The rule's check decides; the candidates only choose what it is asked. *)
let premise_candidates seq_map penv frame lower =
  let psub = psub_of penv ([], [ lower ]) in
  Map.Poly.of_alist_exn
  @@ List.filter_map (List.zip_exn penv frame) ~f:(fun ((pvar, args), phi) ->
      let params = Set.Poly.of_list @@ List.map args ~f:fst in
      let present = Set.Poly.of_list @@ Formula.conjuncts_list_of phi in
      let cands =
        Set.Poly.of_list
        @@ List.concat_map (Map.Poly.find_exn seq_map (Some pvar))
             ~f:(fun seq ->
               List.concat_map seq.Sequent.left_atms ~f:(fun (atm, _) ->
                   match atm with
                   | Atom.App (Predicate.Var (p, _), ts, _) -> (
                       match Map.Poly.find psub p with
                       | None -> []
                       | Some (pargs, pphi) ->
                           let sub =
                             Map.Poly.of_alist_exn
                             @@ List.zip_exn (List.map pargs ~f:fst)
                             @@ List.map ts ~f:(resolve_arg params seq)
                           in
                           List.filter_map (Formula.conjuncts_list_of pphi)
                             ~f:(fun c ->
                               let c =
                                 Evaluator.simplify (Formula.subst sub c)
                               in
                               if
                                 Formula.is_true c
                                 || Set.mem present c
                                 || not
                                      (Set.is_subset (Formula.tvs_of c)
                                         ~of_:params)
                               then None
                               else Some c))
                   | _ -> []))
      in
      if Set.is_empty cands then None else Some (pvar, cands))

(* [config.premise_push]: [premise_candidates] tried at every frame, from the
   bottom one up, so that a frame's new facts are offered to the frame above.
   Each added fact follows from the frame below through every clause defining
   its predicate ([apply_induct_rule] without its relative step), so every
   frame still over-approximates its level.  A fact is kept only if it lies
   in the largest set of its predicate's facts at that frame that is
   inductive relative to the rest of the frame; this filter only withholds
   facts, so it does not bear on soundness.  [old] is the previous
   call's result (frames newest first, aligned at the bottom); a frame that is
   physically the same as there and whose frame below is too was already
   offered every candidate it can be offered, and is skipped.
   [memo] keeps the rule's answer for a candidate of a predicate [q] under the
   formulas the frame below gives the predicates in the bodies of [q]'s
   defining clauses, the only part of the trace the check reads: a candidate
   asked again under the same formulas (on another level, or after a
   refinement replaced the frame that had received it) is answered from
   [memo] without Z3 *)
let push_premise_facts ~print ~memo seq_map penv ~old (trace1, trace2) =
  phase_time "premise-push" @@ fun () ->
  let z3 = lazy (induct_z3 ()) in
  let same f f' = List.for_all2_exn f f' ~f:phys_equal in
  (* the candidates of [cands] the rule admits at a frame [frame] whose frame
     below is [lower], per predicate; answered from [memo] where it can be *)
  let admit lower frame cands =
    let lower_of =
      Map.Poly.of_alist_exn
      @@ List.zip_exn (List.map penv ~f:fst) lower
    in
    let key pvar =
      let bodies =
        List.dedup_and_sort ~compare:Ident.pvar_compare
        @@ List.concat_map (Map.Poly.find_exn seq_map (Some pvar))
             ~f:(fun seq ->
               List.filter_map seq.Sequent.left_atms
                 ~f:(fun (atm, _) ->
                   match atm with
                   | Atom.App (Predicate.Var (p, _), _, _) -> Some p
                   | _ -> None))
      in
      let lowers =
        List.map bodies ~f:(fun p ->
            (p, Map.Poly.find_exn lower_of p))
      in
      fun c -> (pvar, c, lowers)
    in
    let known, unknown =
      let split =
        Map.Poly.mapi cands ~f:(fun ~key:pvar ~data ->
            let key = key pvar in
            List.partition_map (Set.to_list data) ~f:(fun c ->
                match Hashtbl.find memo (key c) with
                | Some passed ->
                    phase_time
                      (if passed then "premise-push-memo-pass"
                       else "premise-push-memo-fail")
                      Fn.id;
                    First (c, passed)
                | None -> Second c))
      in
      ( Map.Poly.map split ~f:(fun (k, _) ->
            Set.Poly.of_list
            @@ List.filter_map k ~f:(fun (c, passed) ->
                if passed then Some c else None)),
        Map.Poly.filter_map split ~f:(fun (_, u) ->
            if List.is_empty u then None
            else Some (Set.Poly.of_list u)) )
    in
    let _, passed =
      apply_induct_rule ~z3:(Lazy.force z3) ~relative:false ~print
        seq_map penv
        ([], [ frame; lower ])
        unknown
    in
    Map.Poly.iteri unknown ~f:(fun ~key:pvar ~data ->
        let key = key pvar in
        let passed =
          Option.value ~default:Set.Poly.empty
          @@ Map.Poly.find passed pvar
        in
        Set.iter data ~f:(fun c ->
            Hashtbl.set memo ~key:(key c) ~data:(Set.mem passed c)));
    Map.Poly.merge known passed ~f:(fun ~key:_ -> function
        | `Both (a, b) -> Some (Set.union a b)
        | `Left a | `Right a -> Some a)
  in
  let conj frame passed =
    List.map2_exn penv frame ~f:(fun (pvar, _) phi ->
        match Map.Poly.find passed pvar with
        | Some cs when not (Set.is_empty cs) ->
            Formula.and_of (phi :: Set.to_list cs)
        | _ -> phi)
  in
  (* per predicate [q] of [passed], the facts of [passed] in the largest
     subset [s] of [q]'s conjuncts in [frame1] whose members each follow,
     through every clause defining [q], from [frame1] with [q] read as [s]
     (Houdini's fixpoint, Flanagan and Leino, FME 2001, restricted to one
     predicate) *)
  let stable frame1 passed =
    Map.Poly.mapi passed ~f:(fun ~key:q ~data ->
        let with_q s =
          List.map2_exn penv frame1 ~f:(fun (pvar, _) phi ->
              if Ident.pvar_equal pvar q then Formula.and_of (Set.to_list s)
              else phi)
        in
        let rec fix s =
          let lower = with_q s in
          let s' =
            Option.value ~default:Set.Poly.empty
            @@ Map.Poly.find
                 (admit lower lower (Map.Poly.singleton q s))
                 q
          in
          if Set.length s' = Set.length s then s else fix s'
        in
        let s0 =
          Set.Poly.of_list @@ Formula.conjuncts_list_of
          @@ List.Assoc.find_exn ~equal:Ident.pvar_equal
               (List.zip_exn (List.map penv ~f:fst) frame1)
               q
        in
        Set.inter data (fix s0))
  in
  (* [frames] and [olds] bottom first; returns the frames bottom first *)
  let rec go lower lower_same acc frames olds =
    match frames with
    | [] -> acc
    | frame :: frames ->
        let old, olds =
          match olds with [] -> (None, []) | o :: os -> (Some o, os)
        in
        let skip =
          lower_same
          && match old with Some o -> same frame o | None -> false
        in
        let frame' =
          match lower with
          | None -> frame
          | Some _ when skip -> frame
          | Some lower ->
              let passed =
                admit lower frame (premise_candidates seq_map penv frame lower)
              in
              (* a fact tied to the level (a bound on a counter whose constant
                 grows with the depth) follows from the frame below, but frames
                 carrying such facts never cover each other; it belongs to no
                 set of facts of its predicate that holds of the next level
                 whenever it holds of one, so only the facts in the largest
                 such subset of the predicate's conjuncts and admitted
                 candidates are kept, the other predicates read as the frame
                 with their admitted candidates *)
              let frame1 = conj frame passed in
              conj frame (stable frame1 passed)
        in
        let frame_same =
          match old with Some o -> same frame' o | None -> false
        in
        go (Some frame') frame_same (frame' :: acc) frames olds
  in
  (trace1, go None true [] (List.rev trace2) (List.rev old))

let empty_gcexs = Map.Poly.empty

(* [Level] sharing keeps one cumulative union per level, as the original Spacer
   (Komuravelli et al., SAT 2014 / FMSD 2016) does; [Global] keeps one per
   predicate across levels (Komuravelli et al., CAV 2015). Per-level unions keep
   the counterexamples a refinement call can return finite in variety, the fact
   the termination argument of the return-based refinement rests on; the
   cross-level union does not (Tsukada and Unno, PLDI 2024, Sec. 5.3). *)
let gcex_key ~config (trace : trace Lazy.t) pvar =
  match config.Config.counterexample_sharing with
  | Some Config.Level -> (pvar, Some (List.length (snd (Lazy.force trace))))
  | _ -> (pvar, None)

(* [trace] is the trace the counterexamples [cexs] for [pvar] were computed on. *)
let add_to_gcexs ~config gcexs trace pvar cexs =
  let key = gcex_key ~config (lazy trace) pvar in
  Map.Poly.set gcexs ~key
    ~data:
      (match Map.Poly.find gcexs key with
      | Some cexs' -> Set.union cexs' cexs
      | None -> cexs)

(* The shared counterexamples for a body atom [pvar] of the clause refined at
   [state], i.e. those computed one level below [state]'s node. A missing key is
   an internal error, not an empty union: reading it as [false] would hide
   reachable states and could license a wrong [sat]. *)
let get_gcex ~config state pvar =
  Evaluator.simplify @@ Formula.or_of @@ Set.to_list
  @@ Map.Poly.find_exn state.gcexs
  @@ gcex_key ~config (lazy (next_trace_of state.trace)) pvar

let pr_trace ppf (penv, (trace : trace)) =
  let pr_pred ppf ((pvar, args), phi) =
    Format.fprintf ppf "%s(%s) = %s" (Ident.name_of_pvar pvar)
      (String.concat_map_list ~sep:"," args ~f:(fst >> Ident.name_of_tvar))
      (Formula.str_of phi)
  in
  List.pr
    (fun ppf frame -> List.pr pr_pred ", " ppf (List.zip_exn penv frame))
    "@," ppf
  @@ snd trace

let generate ~config ~print
    (iterator : trace * query * gcexs -> (state * cex -> state) -> result_ret) =
  let yield (s, c) = Effect.perform (Yield (s, c)) in
  let status = ref Init in
  let rec handler =
    {
      retc =
        (fun result ->
          status := Done;
          Second result);
      exnc = (fun e -> raise e);
      effc =
        (fun (type b) (eff : b Effect.t) ->
          match eff with
          | Yield (state, cex) ->
              Some
                (fun (k : (b, result_ret) continuation) ->
                  match config.refinement_strategy with
                  | Refine (_, Or) ->
                      (* pass the control to the callee immediately with the state updated with the counterexample *)
                      let state' =
                        {
                          state with
                          cex_acc = Formula.or_of [ state.cex_acc; cex ];
                        }
                      in
                      continue_with k state' handler
                  | Refine (_, Return _) ->
                      (* pass the counterexample to the caller by discarding the delimited continuation of the callee *)
                      status := Done;
                      Second (state.trace, cex, state.induct, state.gcexs)
                  | Refine (_, Yield (_, share_trace_among_coroutines)) ->
                      (* pass the counterexample to the caller after saving the delimited continuation of the callee *)
                      status :=
                        Paused
                          (fun (trace_yield, query_yield, gcexs) ->
                            let state' =
                              {
                                trace =
                                  (if share_trace_among_coroutines then
                                     trace_yield
                                   else state.trace);
                                query = query_yield;
                                cex_acc = state.cex_acc;
                                induct = empty_induct;
                                gcexs;
                              }
                            in
                            print
                            @@ lazy
                                 (sprintf
                                    "  resume with the refined query: %s\n"
                                    (Formula.str_of query_yield));
                            continue_with k state' handler);
                      First (state.trace, cex, state.induct, state.gcexs)
                  | Solve -> assert false)
          | _ -> None);
    }
  in
  fun (trace, query, gcexs) ->
    match !status with
    | Init ->
        continue_with
          (fiber (Fn.flip iterator yield))
          (trace, query, gcexs) handler
    | Paused k -> k (trace, query, gcexs)
    | Done -> failwith "[generate] already done"

let psub_right_of penv pvar_opt current_state =
  match pvar_opt with
  | None -> Map.Poly.empty
  | Some pvar -> Map.Poly.singleton pvar (args_of penv pvar, current_state.query)

(* [check_sat_within_budget phi]: Z3's satisfiability answer for [phi], asked
   within what is left of the run's armed budget ([Z3interface.armed_budget_ms];
   unbounded, as before, when none is armed), and [`Unknown] without asking
   when [phi]'s shape is one Z3's own budget does not hold over
   ([Z3interface.may_not_return]).

   Why: the frames and queries these questions are built from can carry
   quantifiers (a projection that could not eliminate a variable keeps it
   existentially bound), and a quantified question Z3 does not decide runs
   in native code where the budget's alarm cannot raise, holding the run
   past its budget.  Every caller reads [`Timeout] and [`Unknown] as "not
   decided" and never as [`Unsat] or [`Sat]: the refinement either stops with
   no answer or does the extra work an undecided question leaves. *)
let check_sat_within_budget phi =
  if Z3Smt.Z3interface.may_not_return phi then
    `Unknown "a quantified sort Z3's budget does not hold over"
  else
    Z3Smt.Z3interface.check_sat
      ~timeout:(Z3Smt.Z3interface.armed_budget_ms ())
      ~id:None (FunEnv.mk_empty ()) [ phi ]

(* The countermodel sessions of one search, for [countermodel_body_session].
   [bodies] maps each clause constraint of the sequent map (by physical
   identity: the map is built once per problem) to the one alpha-renamed,
   existential-free copy every refinement of that clause then uses, instead of
   a fresh renaming per refinement; [sessions] maps such a copy to its
   simplified form and a solver holding it at its root, or [None] when the
   session refused it.  One table per call of [solve]; not for concurrent
   use. *)
type cex_sessions = {
  mutable bodies : (Formula.t * Formula.t) list;
  mutable sessions :
    (Formula.t * (Formula.t * Z3Smt.Z3interface.base_session) option) list;
  mutable checks : int;  (** session checks made, for the probe below *)
}

(* With [COAR_MUCYC_INTERP_TIME] in the environment, each new session prints a
   [cex-session-new: at <s> s sessions <n> ok <bool> z3mem <MB> -> <MB> heap
   <MB>] line and each session check a [cex-session-check: at <s> s sessions
   <n> checks <n> answer <a> z3mem <MB> heap <MB>] line on stderr: Z3's
   estimate of its own allocation (process-wide, every context) before and
   after a base is set, and the OCaml major heap, so that memory a run gains
   under [countermodel_body_session] can be split between the bases the
   sessions hold, what the checks add over time, and the OCaml side.
   Observation only. *)
let cex_session_probe kind fields =
  if interp_time then
    prerr_endline
      (sprintf "cex-session-%s: at %.3f s %s heap %d MB" kind (since_origin ())
         fields
         ((Gc.quick_stat ()).heap_words * (Stdlib.Sys.word_size / 8) / 1_000_000))

let z3mem_mb () =
  Int64.to_int_exn (Z3.Statistics.get_estimated_alloc_size ()) / 1_000_000

(* the clause constraint a refinement of [left_phi] works on: a fresh
   alpha-renaming with the existentials removed, made once per clause under
   [countermodel_body_session].  Sharing the copy between refinements of one
   clause is safe because nothing over a refinement's own local variables
   leaves it: a counterexample, a query and a frame passed between
   refinements are over the predicates' parameters (the head's free
   variables, which no renaming touches anyway) *)
let clause_body ~config ~(cexs : cex_sessions) left_phi =
  let renamed () =
    snd @@ Formula.rm_quant ~forall:false @@ Formula.aconv_tvar left_phi
  in
  if not config.Config.countermodel_body_session then renamed ()
  else
    match List.Assoc.find cexs.bodies left_phi ~equal:phys_equal with
    | Some body -> body
    | None ->
        let body = renamed () in
        cexs.bodies <- (left_phi, body) :: cexs.bodies;
        body

let cex_session_of ~config ~(cexs : cex_sessions) left_phi =
  match List.Assoc.find cexs.sessions left_phi ~equal:phys_equal with
  | Some s -> s
  | None ->
      let mem0 = if interp_time then z3mem_mb () else 0 in
      let s =
        phase_time "cex-session-set" @@ fun () ->
        let base = Evaluator.simplify left_phi in
        if Z3Smt.Z3interface.may_not_return base then None
        else
          let session =
            Z3Smt.Z3interface.base_session_create
              ~memo:config.Config.countermodel_session_memo ~id:None ()
          in
          if
            Z3Smt.Z3interface.base_session_set ~id:None session
              (FunEnv.mk_empty ()) [ base ]
          then Some (base, session)
          else None
      in
      Common.PhaseTime.event_here "cex-session-new";
      if interp_time then
        cex_session_probe "new"
          (sprintf "sessions %d ok %b z3mem %d MB -> %d MB"
             (List.length cexs.sessions + 1)
             (Option.is_some s) mem0 (z3mem_mb ()));
      cexs.sessions <- (left_phi, s) :: cexs.sessions;
      s

(* [cond] is [left /\ not right]: a model of it is a countermodel of the
   clause under the next trace and the current query.  With
   [countermodel_body_session] the clause constraint [seq.left_phi] is held by
   the clause's session and only the rest, [not (rest => right)], is
   converted and asserted per check; the conjunction asked is the same, so an
   [`Unsat] or [`Sat] answer is one for [cond], which is then returned as the
   conjunction of the two parts.  Anything else from the session says nothing
   and the whole [cond] is asked as without the option. *)
let find_countermodel ~config ~cexs penv pvar_opt seq cexs_left_phis atms_right
    state =
  let rest =
    let psub = psub_of penv @@ next_trace_of state.trace in
    cexs_left_phis @ List.map atms_right ~f:(Atom.subst_preds psub)
  in
  let right =
    let psub_right = psub_right_of penv pvar_opt state in
    Formula.or_of
      [ (Sequent.subst_preds_right psub_right seq).right_phi; state.cex_acc ]
  in
  let whole () =
    let cond =
      Evaluator.simplify_neg
      @@ Formula.mk_imply (Formula.and_of (seq.Sequent.left_phi :: rest)) right
    in
    (*print @@ lazy (Format.asprintf "seq: %a" (Sequent.pr ~wo_guard:true) seq);
      print @@ lazy (sprintf "cond: %s" (Formula.str_of cond));*)
    ( cond,
      phase_time "cex-check" @@ fun () ->
      check_sat_within_budget cond )
  in
  (* With COAR_MUCYC_PHASE_TIME set, a census of where the session acts:
     [cex-session-answered] counts the questions the session answers and
     [cex-session-whole] those asked whole although the option is on (no
     session for the clause, or a rest that may not return; an unknown from
     the session is counted by [cex-session-unknown] as well).  Observation
     only. *)
  let whole_on () =
    Common.PhaseTime.event "cex-session-whole";
    whole ()
  in
  if not config.Config.countermodel_body_session then whole ()
  else
    match cex_session_of ~config ~cexs seq.Sequent.left_phi with
    | None -> whole_on ()
    | Some (base, session) -> (
        let ext =
          Evaluator.simplify_neg @@ Formula.mk_imply (Formula.and_of rest) right
        in
        if Z3Smt.Z3interface.may_not_return ext then whole_on ()
        else
          let answer =
            phase_time "cex-check" @@ fun () ->
            Z3Smt.Z3interface.base_session_check ~id:None session
              ~timeout:None (FunEnv.mk_empty ()) ext
          in
          cexs.checks <- cexs.checks + 1;
          if interp_time then
            cex_session_probe "check"
              (sprintf "sessions %d checks %d answer %s z3mem %d MB"
                 (List.length cexs.sessions) cexs.checks
                 (match answer with
                 | `Unsat -> "unsat"
                 | `Sat _ -> "sat"
                 | `Unknown -> "unknown")
                 (z3mem_mb ()));
          match answer with
          | `Unsat ->
              Common.PhaseTime.event "cex-session-answered";
              (Formula.and_of [ base; ext ], `Unsat)
          | `Sat model ->
              Common.PhaseTime.event "cex-session-answered";
              (Formula.and_of [ base; ext ], `Sat model)
          | `Unknown ->
              Common.PhaseTime.event_here "cex-session-unknown";
              whole_on ())

let cex_of_countermodel ~config ~print penv seq cexs_left_phis cond model pvar
    args = function
  | QE ->
      let cex = qelim_except ~config ~exists:true args cond in
      print
      @@ lazy
           (sprintf "      a counterexample for %s by QE: %s"
              (Ident.name_of_pvar pvar) (Formula.str_of cex));
      (cex, true)
  | Model ->
      let senv = Formula.term_sort_env_of cond in
      let model' = convert_model false senv model in
      let cex =
        Formula.and_of
        @@ List.filter_map (args_of penv pvar) ~f:(fun (x, s) ->
            match Map.Poly.find model' x with
            | None -> None
            | Some t -> Some (Formula.eq (Term.mk_var x s) t))
      in
      print
      @@ lazy
           (sprintf "      a counterexample for %s from the model: %s"
              (Ident.name_of_pvar pvar) (Formula.str_of cex));
      (cex, false)
  | MBP _ ->
      let senv = Formula.term_sort_env_of cond in
      let absent =
        if config.Config.mbp_implicant_partial then absent_of senv model
        else Set.Poly.empty
      in
      let model' = convert_model true senv model in
      let non_arg = Set.mem args >> not in
      let cex =
        project_counterexample ~config ~print
          ~mbp:(fun () ->
            let body =
              Evaluator.simplify_neg
              @@ Formula.mk_imply
                   (Formula.and_of (seq.Sequent.left_phi :: cexs_left_phis))
                   (Formula.mk_false ())
            in
            let model', senv, body =
              mbp_input ~absent ~config ~print ~eliminated:non_arg model' senv
                body
            in
            (* [cex-image]: the projection onto the head's arguments, i.e. a
               forward image of the body atoms' counterexamples.  Observation
               phase only. *)
            phase_time "cex-image" @@ fun () ->
            get_mbp ~config ~print model' (Set.filter senv ~f:(fst >> non_arg))
            @@ body)
          ~model_values:(fun () ->
            (* qelim_except ~config ~exists:true args cond *)
            let model' = convert_model false senv model in
            Formula.and_of
            @@ List.filter_map (args_of penv pvar) ~f:(fun (x, s) ->
                match Map.Poly.find model' x with
                | None -> None
                | Some t -> Some (Formula.eq (Term.mk_var x s) t)))
      in
      print
      @@ lazy
           (sprintf "      a counterexample for %s by MBP: %s"
              (Ident.name_of_pvar pvar) (Formula.str_of cex));
      (cex, false)

let rec yield_all_cexs ~config ~print ~cexs seq_map penv pvar_opt yield seq cexs_left
    state : state =
  let cexs_left_phis =
    List.map cexs_left ~f:(function
      | First (pvar, ftoa) -> Formula.rename ftoa @@ get_gcex ~config state pvar
      | Second cex -> cex)
  in
  match
    find_countermodel ~config ~cexs penv pvar_opt seq cexs_left_phis [] state
  with
  | _cond, `Unsat ->
      print @@ lazy "      no more countermodel";
      state
  | cond, `Sat model -> (
      print
      @@ lazy
           (sprintf "      found a countermodel %s"
              (LogicOld.str_of_model model));
      match pvar_opt with
      | None ->
          print
          @@ lazy (sprintf "      a counterexample for a goal clause: true");
          yield (state, Formula.mk_true () (*ToDo*))
      | Some pvar -> (
          let args = Set.Poly.of_list @@ List.map ~f:fst @@ args_of penv pvar in
          match config.refinement_strategy with
          | Refine (cex_typ, _) ->
              let state =
                let trace, induct =
                  match config.induction with
                  | Some (Config.Normal _) when config.induction_at_countermodels ->
                      apply_induct_rule ~print seq_map penv state.trace
                        state.induct
                  | _ -> (state.trace, state.induct)
                in
                { state with trace; induct }
              in
              let cex, all =
                cex_of_countermodel ~config ~print penv seq cexs_left_phis cond
                  model pvar args cex_typ
              in
              (* [cex] should be satisfiable *)
              yield (state, cex)
              |>
              if all then Fn.id
              else
                yield_all_cexs ~config ~print ~cexs seq_map penv pvar_opt yield seq
                  cexs_left
          | Solve -> assert false))
  (* the solver could not decide whether another countermodel exists: the
     search is undecided, not broken *)
  | cond, _ ->
      raise
      @@ Search_undecided
           (sprintf "Z3 timeout/unknown in model enumeration for: %s"
              (Formula.str_of cond))

let query_of_countermodel ~config ~print penv pvar_opt seq cexs_left
    cexs_left_phis aargs aargs_set atof atms_right state_saved_inv state_saved
    state (senv, model) =
  let non_arg = Set.mem aargs_set >> not in
  match config.refinement_strategy with
  | Refine (QE, _) ->
      print @@ lazy "      a query by QE";
      let ub =
        let psub = psub_of penv @@ next_trace_of state.trace in
        let psub_right = psub_right_of penv pvar_opt state in
        Evaluator.simplify
        @@ Formula.mk_imply
             (Formula.and_of
             @@ (seq.Sequent.left_phi :: cexs_left_phis)
             @ List.map atms_right ~f:(Atom.subst_preds psub))
             (Sequent.subst_preds_right psub_right seq).right_phi
      in
      Formula.rename atof @@ qelim_except ~config ~exists:false aargs_set ub
  | Refine (Model, _) ->
      print @@ lazy "      a query from the countermodel";
      let model' = convert_model false senv model in
      Evaluator.simplify_neg @@ Formula.rename atof @@ Formula.and_of
      @@ List.filter_map aargs ~f:(fun (x, s) ->
          match Map.Poly.find model' x with
          | None -> None
          | Some t -> Some (Formula.eq (Term.mk_var x s) t))
  | Refine (MBP use_saved (* use an invariant state for image finiteness *), _)
    ->
      print
      @@ lazy
           ("      a query by MBP"
           ^
           match use_saved with
           | 0 -> ""
           | 1 -> " using a saved state"
           | 2 -> " using a saved state that is a loop invariant"
           | _ -> failwith "not supported");
      let ub =
        let state =
          match use_saved with
          | 0 -> state
          | 1 -> state_saved
          | 2 -> state_saved_inv
          | _ -> failwith "not supported"
        in
        let cexs_left_phis =
          if use_saved = 0 then cexs_left_phis
          else
            List.map cexs_left ~f:(function
              | First (pvar, ftoa) -> Formula.rename ftoa @@ get_gcex ~config state pvar
              | Second cex -> cex)
        in
        let psub = psub_of penv @@ next_trace_of state.trace in
        let psub_right = psub_right_of penv pvar_opt state in
        Evaluator.simplify
        @@ Formula.mk_imply
             (Formula.and_of
             @@ (seq.left_phi :: cexs_left_phis)
             @ List.map atms_right ~f:(Atom.subst_preds psub))
             (Sequent.subst_preds_right psub_right seq).right_phi
      in
      let eliminated = Set.filter senv ~f:(fst >> non_arg) in
      let mbp =
        let absent =
          if config.Config.mbp_implicant_partial then absent_of senv model
          else Set.Poly.empty
        in
        let model' = convert_model true senv model in
        project_counterexample ~config ~print
          ~mbp:(fun () ->
            let model', senv', body =
              mbp_input ~absent ~config ~print ~eliminated:non_arg model' senv
              @@ Evaluator.simplify_neg ub
            in
            (* [query-preimage]: the projection onto a body atom's arguments
               of the step into the head's complement, i.e. a predecessor.
               Observation phase only. *)
            phase_time "query-preimage" @@ fun () ->
            get_mbp ~config ~print model'
              (Set.filter senv' ~f:(fst >> non_arg))
              body)
          ~model_values:(fun () ->
            (* The projection's contract is that its result no longer mentions
               what was eliminated.  This branch discharges those variables by
               substituting the model's value for each, which covers exactly the
               ones the model has an entry for -- every variable of the
               environment the model was converted against, since that
               conversion supplies a dummy for anything the solver left out, but
               not a variable that reaches this formula from elsewhere.  The
               quantifier-elimination call that would be correct by construction
               is written below and not taken: it goes to a tactic that is
               incomplete over arrays and can hand back a formula that still has
               quantifiers, and it carries no budget of its own.  So the
               substitution stands and the contract is checked instead, in the
               mode that checks the projection's other obligations. *)
            (* qelim_except ~config ~exists:true aargs ub *)
            let res =
              if true then
                Formula.subst
                  (Map.Poly.filter_keys model' ~f:non_arg)
                  seq.left_phi
              else
                let model' = convert_model false senv model in
                Formula.and_of
                @@ List.filter_map aargs ~f:(fun (x, s) ->
                    match Map.Poly.find model' x with
                    | None -> None
                    | Some t -> Some (Formula.eq (Term.mk_var x s) t))
            in
            if config.check_validity then (
              let leftover =
                Set.inter (Formula.fvs_of res)
                @@ Set.Poly.map ~f:fst eliminated
              in
              if Fn.non Set.is_empty leftover then
                failwith
                @@ sprintf
                     "the fallback for a failed projection still mentions %s, \
                      which it was asked to eliminate"
                     (String.concat_map_set ~sep:", " ~f:Ident.name_of_tvar
                        leftover));
            res)
      in
      (*print @@ lazy ("      ub: " ^ Formula.str_of ub);
        print @@ lazy ("      senv: " ^ str_of_sort_env_list Term.str_of_sort @@ Set.to_list @@ Set.filter senv ~f:(fst >> non_arg));*)
      print @@ lazy ("      MBP: " ^ Formula.str_of mbp);
      Formula.rename atof @@ Evaluator.simplify_neg mbp
  | _ -> assert false

let weaken_query ~config ~print solve_chc penv pvar_opt seq cexs_left cex_f
    (pvar, aargs, fargs, atof, _ftoa) atms_right next_query state =
  let right =
    let cexs_left_phis =
      List.map cexs_left ~f:(function
        | First (pvar, ftoa) -> Formula.rename ftoa @@ get_gcex ~config state pvar
        | Second cex -> cex)
    in
    let psub = psub_of penv @@ next_trace_of state.trace in
    let psub_right = psub_right_of penv pvar_opt state in
    Formula.rename atof @@ snd
    @@ Formula.refresh_except aargs
    @@ Evaluator.simplify
    @@ Formula.mk_imply
         (Formula.and_of
         @@ (seq.Sequent.left_phi :: cexs_left_phis)
         @ List.map atms_right ~f:(Atom.subst_preds psub))
         (Sequent.subst_preds_right psub_right seq).right_phi
  in
  if Formula.is_true @@ Evaluator.simplify right then (
    (* for maximal conservativity *)
    print @@ lazy "        query is weakened to true";
    (Formula.mk_true (), state))
  else
    match config.refinement_strategy with
    | Refine (_, Yield (true, _)) -> (
        print
        @@ lazy
             (sprintf "        query weakening by interpolating %s => %s"
                (Formula.str_of cex_f) (Formula.str_of right));
        match interpolate ~config ~print solve_chc fargs cex_f right with
        | Some interp ->
            let interp = qelim ~config interp in
            print
            @@ lazy
                 (sprintf "        interpolant for %s: %s"
                    (Ident.name_of_pvar pvar) (Formula.str_of interp));
            ( Normalizer.normalize @@ Evaluator.simplify
              @@ Formula.or_of [ next_query; interp ],
              state )
        | None ->
            (* as for the frame's interpolant: an incomplete interpolation
               leaves the search undecided *)
            raise
            @@ Search_undecided
                 (sprintf
                    "[FrameSearch.refine] interpolant for %s and %s not found"
                    (Formula.str_of cex_f) (Formula.str_of right)))
    | _ ->
        let next_query' =
          Normalizer.normalize @@ Evaluator.simplify
          @@ Formula.or_of [ next_query; cex_f ]
        in
        print
        @@ lazy
             (sprintf "        weakened query for %s: %s" (str_of_head pvar_opt)
                (Formula.str_of next_query'));
        (next_query', state)

let resolve_query ~config ~print solve_chc penv pvar_opt seq refine
    refine_clause cexs_left pvar aargs fargs atof ftoa atms_right query0 state0
    =
  print @@ lazy (sprintf "      begin query for %s" (Ident.name_of_pvar pvar));
  let next_cex =
    generate ~config ~print (fun (trace, query, gcexs) ->
        refine (Some pvar)
          {
            trace;
            query;
            cex_acc = Formula.mk_false ();
            induct = empty_induct;
            gcexs;
          })
  in
  let rec each_cex updated (next_query, state1) =
    (*print @@ lazy (sprintf "        current query: %s" (Formula.str_of next_query));*)
    match next_cex (next_trace_of state1.trace, next_query, state1.gcexs) with
    | Second (trace, cex_f, induct, gcexs) ->
        (* counterexample enumeration is completed or a counterexample is returned *)
        let cex_a = Formula.rename ftoa cex_f in
        print
        @@ lazy
             (sprintf "\n      end query for %s with a counterexample: %s"
                (Ident.name_of_pvar pvar) (Formula.str_of cex_f));
        let state2 =
          {
            state1 with
            trace = prev_trace_of trace;
            induct = merge_induct state1.induct induct;
            gcexs = add_to_gcexs ~config gcexs trace pvar (Set.Poly.singleton cex_f);
          }
        in
        (*print @@ lazy (Format.asprintf "refined trace: %a" pr_trace (penv, state2.trace));*)
        ( cex_f,
          let updated', state3 =
            if Formula.is_false cex_f then (false, state2)
            else
              let cexs_left =
                (match config.counterexample_sharing with
                | None -> Second cex_a
                | Some _ -> First (pvar, ftoa))
                :: cexs_left
              in
              refine_clause cexs_left atms_right state2
          in
          ( updated || updated',
            if
              config.query_reuse
              && not
                   (config.query_reuse_resolved_only
                  && not (Formula.is_false cex_f))
            then
              (* share the child's query with the current frame *)
              let next_cex =
                generate ~config ~print (fun (trace, query, gcexs) ->
                    refine (Some pvar)
                      {
                        trace;
                        query;
                        cex_acc = Formula.mk_false ();
                        induct = empty_induct;
                        gcexs;
                      })
              in
              Common.PhaseTime.event "reuse-pose";
              (* observation only: where the re-posing happens, as the
                 number of frames above the parent's level ([d], 0 at the
                 top frame of the round) and below it ([r]) *)
              Common.PhaseTime.event
                (sprintf "reuse-pose-d%d-r%d"
                   (List.length (fst state3.trace))
                   (List.length (snd state3.trace)));
              let rec loop state4 next_query =
                let trace =
                  match config.refinement_strategy with
                  | Refine (_, Yield (_, share_trace_among_coroutines))
                    when share_trace_among_coroutines ->
                      state4.trace
                  | _ -> state3.trace
                in
                match next_cex (trace, next_query, state4.gcexs) with
                | Second (trace, cex_f, _induct, _gcexs) ->
                    if
                      config.query_reuse_refute
                      && not (Formula.is_false cex_f)
                    then (
                      Common.PhaseTime.event "reuse-refute";
                      Common.PhaseTime.event
                        (sprintf "reuse-refute-d%d-r%d"
                           (List.length (fst state3.trace))
                           (List.length (snd state3.trace)));
                      print
                      @@ lazy
                           (sprintf
                              "      re-posed query for %s refuted: %s"
                              (Ident.name_of_pvar pvar)
                              (Formula.str_of cex_f));
                      raise Reposed_query_refuted);
                    { state3 with trace }
                | First (trace, cex_f, induct, gcexs) ->
                    loop
                      {
                        state4 with
                        trace;
                        induct = merge_induct state4.induct induct;
                        gcexs =
                          add_to_gcexs ~config gcexs trace pvar
                            (Set.Poly.singleton cex_f);
                      }
                    @@ Normalizer.normalize @@ Evaluator.simplify
                    @@ Formula.or_of [ next_query; cex_f ]
              in
              loop state3 query0
            else state3 ) )
    | First (trace, cex_f, induct, gcexs) ->
        let cex_a = Formula.rename ftoa cex_f in
        print
        @@ lazy
             (sprintf "\n  yield with the counterexample from %s: %s"
                (Ident.name_of_pvar pvar) (Formula.str_of cex_a));
        let state2 =
          {
            state1 with
            trace = prev_trace_of trace;
            induct = merge_induct state1.induct induct;
            gcexs = add_to_gcexs ~config gcexs trace pvar (Set.Poly.singleton cex_f);
          }
        in
        let updated', state3 =
          let cexs_left =
            (match config.counterexample_sharing with
            | None -> Second cex_a
            | Some _ -> First (pvar, ftoa))
            :: cexs_left
          in
          refine_clause cexs_left atms_right state2
        in
        state3
        |> weaken_query ~config ~print solve_chc penv pvar_opt seq cexs_left
             cex_f
             (pvar, aargs, fargs, atof, ftoa)
             atms_right next_query
        |> each_cex (updated || updated')
  in
  each_cex false (query0, state0)

let refine_atom ~config ~print ~cexs solve_chc penv pvar_opt seq refine refine_clause
    cexs_left atm atms_right (state0 : state) =
  let pvar, aargs, fargs, atof, ftoa =
    let pvar, _, aargs, _ = Atom.let_pvar_app atm in
    let aargs =
      (* [aargs] are assumed to be distinct variables *)
      List.map aargs ~f:(Term.let_var >> fst)
    in
    let fargs = args_of penv pvar in
    ( pvar,
      aargs,
      fargs,
      ren_of_sort_env_list aargs fargs,
      ren_of_sort_env_list fargs aargs )
  in
  let aargs_set = Set.Poly.of_list @@ List.map ~f:fst aargs in
  (* [cexs_left] is empty exactly at the first body atom of the clause: each
     later atom is refined under the counterexamples of the earlier ones *)
  let accumulate =
    match config.refinement_strategy with
    | Refine (_, Return true) ->
        (not config.return_accumulate_first_atom_only)
        || List.is_empty cexs_left
    | _ -> false
  in
  let rec each_countermodel updated local_cex_acc state0_5 state1 =
    let cexs_left_phis =
      List.map cexs_left ~f:(function
        | First (pvar, ftoa) -> Formula.rename ftoa @@ get_gcex ~config state1 pvar
        | Second cex -> cex)
    in
    match
      find_countermodel ~config ~cexs penv pvar_opt seq cexs_left_phis
        (atm :: atms_right)
        state1
    with
    | _cond, `Unsat ->
        print @@ lazy "      no more countermodel";
        (updated, state1)
    | cond, `Sat model ->
        let senv = Formula.term_sort_env_of cond in
        print
        @@ lazy
             (sprintf "      found a countermodel %s"
                (LogicOld.str_of_model model));
        let next_query =
          let next_query =
            query_of_countermodel ~config ~print penv pvar_opt seq cexs_left
              cexs_left_phis aargs aargs_set atof atms_right state0 state0_5
              state1 (senv, model)
          in
          if accumulate then Formula.or_of [ next_query; local_cex_acc ]
          else next_query
        in
        let cex, (updated, state2) =
          resolve_query ~config ~print solve_chc penv pvar_opt seq refine
            refine_clause cexs_left pvar aargs_set fargs atof ftoa atms_right
            next_query state1
        in
        print @@ lazy "      countermodel resolved\n";
        let local_cex_acc' =
          if accumulate then Formula.or_of [ local_cex_acc; cex ]
          else local_cex_acc
        in
        let state0_5' = if updated then state2 else state0_5 in
        each_countermodel true local_cex_acc' state0_5' state2
    (* an undecided countermodel query leaves the search undecided *)
    | cond, `Unknown reason ->
        raise
        @@ Search_undecided
             (sprintf "Z3 unknown (%s) in countermodel generation for: %s"
                reason (Formula.str_of cond))
    | cond, `Timeout ->
        raise
        @@ Search_undecided
             (sprintf "Z3 timeout in countermodel generation for: %s"
                (Formula.str_of cond))
  in
  each_countermodel false (Formula.mk_false ()) state0 state0

let rec refine_clause ~config ~print ~cexs solve_chc seq_map penv pvar_opt yield seq
    refine cexs_left atms_right (state0 : state) =
  match atms_right with
  | [] ->
      (* enumerate new counterexamples *)
      print
      @@ lazy
           (sprintf
              "    no more atom for refinement and so enumerate and yield all \
               counterexamples for %s if any"
              (str_of_head pvar_opt));
      let cexs_left =
        List.map cexs_left ~f:(fun cex ->
            match (cex, config.counterexample_sharing) with
            | First (pvar, ftoa), Some (Config.Global true (* use saved *)) ->
                Second (Formula.rename ftoa @@ get_gcex ~config state0 pvar)
            | cex, _ -> cex)
      in
      ( false,
        yield_all_cexs ~config ~print ~cexs seq_map penv pvar_opt yield seq cexs_left
          state0 )
  | atm :: atms_right' ->
      print
      @@ lazy (sprintf "    begin refinement for atom: %s" (Atom.str_of atm));
      let res =
        let refine_clause =
          refine_clause ~config ~print ~cexs solve_chc seq_map penv pvar_opt yield seq
            refine
        in
        refine_atom ~config ~print ~cexs solve_chc penv pvar_opt seq refine
          refine_clause cexs_left atm atms_right' state0
      in
      print @@ lazy (sprintf "    end refinement for atom");
      res

(* the level store of [config.persistent_frames] is used: its seeds rest on
   every write to a frame strengthening it, which holds along one search
   thread; [Yield] without trace sharing resumes a coroutine with the trace
   it saved, and the caller then adopts that trace, dropping the writes made
   meanwhile, so it declines there; with sharing the trace is threaded as
   under [Or], but the store has not been run there, so it declines too *)
let level_store_on ~config =
  match (config.Config.persistent_frames, config.refinement_strategy) with
  | Some { seed_by_level = true; _ }, Refine (_, (Or | Return _)) ->
      not config.top_down_search
  | _ -> false

(* the kept solvers of [config.persistent_frames] are used; they need no
   property of the frames (each antecedent has a selector of its own), and
   are restricted as the level store only to be measured with it *)
let level_solvers_on ~config =
  match (config.Config.persistent_frames, config.refinement_strategy) with
  | Some { level_solvers; _ }, Refine (_, (Or | Return _)) ->
      level_solvers > 0 && not config.top_down_search
  | _ -> false

(* Interpolant from a relative-induction query (Bradley, "SAT-Based Model
   Checking without Unrolling", VMCAI 2011).  [refine] asks for X with
   [left => X] and [X => right], where [left] is the clauses of [pvar] with the
   frame below substituted and [right] is the current frame [frame] conjoined
   with [cube] (the query and the accumulated counterexamples).  That query
   has X only as a conclusion, so a solver's inductive generalisation has no
   rule to generalise against and may return the image of [left] bit by bit.
   Here the clauses of [pvar] ([body]) are instead given with every
   occurrence of [pvar] in a body replaced by [lower /\ X] (so base clauses
   keep their initial condition and recursive ones become
   [X /\ lower /\ T => X']), with [X => cube] as the goal.

   Contract.  An answer R of that query need not contain the image of
   [left], so it is used only when [left /\ ~(R /\ frame)] is answered
   [Unsat] within [timeout] milliseconds; then [R /\ frame] implies
   [frame /\ cube], i.e. [right], and is an interpolant of [left => right]
   in the sense of [interpolate].  [R => cube] is taken from the solver's
   answer, as the CHC leaf of [interpolate] takes its answer.  Any other
   outcome (unsat, unknown, timeout of the CHC solver or of the check)
   returns [None] and the caller asks [interpolate] as usual; [unsat] here
   says nothing about the original query, whose X need not be inductive. *)
let relative_induction_interpolant ~print solve_chc args ~timeout ~lower pvar
    ~body ~frame ~cube left =
  (* the unknown's name must not be one [body], [cube] or [lower] spells *)
  let taken =
    Set.Poly.union_list
      [
        Formula.names_spelled_in body;
        Formula.names_spelled_in cube;
        Formula.names_spelled_in frame;
        Set.Poly.of_list (List.map args ~f:fst);
        Set.Poly.map ~f:(fun (Ident.Pvar n) -> Ident.Tvar n)
        @@ Map.key_set lower;
        Map.key_set (LogicOld.get_fenv ());
      ]
  in
  let rec choose index =
    let name =
      if index = 0 then "relind" else "relind_" ^ Int.to_string index
    in
    if Set.mem taken (Ident.Tvar name) then choose (index + 1) else name
  in
  let name = choose 0 in
  let pvapp = Formula.mk_atom @@ Atom.pvar_app_of_senv (Ident.Pvar name) args in
  let psub =
    Map.Poly.change lower pvar
      ~f:
        (Option.map ~f:(fun (senv, phi) ->
             ( senv,
               Formula.and_of
                 [
                   phi;
                   Formula.mk_atom @@ Atom.pvar_app_of_senv (Ident.Pvar name) senv;
                 ] )))
  in
  let left_rec = Evaluator.simplify @@ Formula.subst_preds psub body in
  let chcs =
    let params =
      PCSP.Params.make
      @@ Map.Poly.singleton (Ident.Tvar name)
      @@ Logic.Sort.mk_fun
      @@ List.map args ~f:(snd >> Logic.ExtTerm.of_old_sort)
      @ [ Logic.BoolTerm.SBool ]
    in
    let senv = Map.Poly.of_alist_exn args in
    let senv_of phi =
      Map.force_merge senv @@ Map.of_set_exn @@ Formula.term_sort_env_of phi
    in
    PCSP.Problem.of_old_formulas ~params
    @@ Set.Poly.of_list
         [
           (senv_of left_rec, Formula.mk_imply left_rec pvapp);
           (senv_of cube, Formula.mk_imply pvapp cube);
         ]
  in
  match solve_chc ~bpvs:(Set.Poly.singleton (Ident.Tvar name)) chcs with
  | Result.Ok (PCSP.Problem.Sat sol, _) -> (
      let psub' = Map.of_set_exn @@ snd @@ CandSolOld.of_subst sol in
      let r = Evaluator.simplify @@ Formula.subst_preds psub' pvapp in
      let cand = Formula.and_of [ r; frame ] in
      match
        Z3Smt.Z3interface.check_sat ~timeout:(Some timeout) ~id:None
          (FunEnv.mk_empty ())
          [ left; Formula.negate cand ]
      with
      | `Unsat ->
          print
          @@ lazy
               (sprintf "  relative induction: accepted %s" (Formula.str_of r));
          Some (Evaluator.simplify cand)
      | _ ->
          print @@ lazy "  relative induction: not implied by the clauses";
          None)
  | Result.Ok (sol, _) ->
      print
      @@ lazy
           (sprintf "  relative induction: %s"
              (PCSP.Problem.str_of_solution sol));
      None
  | Result.Error _ ->
      print @@ lazy "  relative induction: error";
      None

let rec refine ~config ~print ~interp_session ~cexs solve_chc seq_map penv pvar_opt
    (state0 : state)
    (yield : state * cex -> state) : result_ret =
  print
  @@ lazy
       (sprintf "\nquery for %s:\n%s"
          (str_of_head_with_args penv pvar_opt)
          (Formula.str_of state0.query));
  (*print @@ lazy (Format.asprintf "trace: %a" pr_trace (penv, state0.trace));*)
  if List.is_empty @@ snd @@ state0.trace then (
    print @@ lazy "returned immediately (frame not available)";
    (state0.trace, state0.cex_acc, state0.induct, state0.gcexs))
  else if
    match pvar_opt with
    | None -> false
    | Some pvar -> (
        let cond =
          Evaluator.simplify_neg
          @@ Formula.mk_imply (get_formula penv state0 pvar) state0.query
        in
        (*print @@ lazy (sprintf "cond: %s" (Formula.str_of cond));*)
        (* undecided: refine, which is the extra work and never wrong *)
        match check_sat_within_budget cond with
        | `Unsat -> true
        | _ -> false)
  then (
    print @@ lazy "returned immediately (refinement not required)";
    (state0.trace, state0.cex_acc, state0.induct, state0.gcexs))
  else
    let state2 =
      Map.Poly.find_exn seq_map pvar_opt
      |> List.fold_left ~init:state0 ~f:(fun state1 (seq : Sequent.t) ->
          (* for each clause *)
          let seq =
            {
              seq with
              left_phi = clause_body ~config ~cexs seq.left_phi;
            }
          in
          print
          @@ lazy
               (sprintf "  begin refinement for clause: %s"
                  (Formula.str_of @@ Sequent.to_formula seq));
          let _updated, state2 =
            let refine =
              refine ~config ~print ~interp_session ~cexs solve_chc seq_map penv
            in
            refine_clause ~config ~print ~cexs solve_chc seq_map penv pvar_opt yield
              seq refine []
              (List.map ~f:fst seq.left_atms)
              state1
          in
          print @@ lazy (sprintf "  end refinement for clause");
          state2)
    in
    (* refinement of the current frame*)
    match pvar_opt with
    | None ->
        print @@ lazy ("done query for " ^ str_of_head pvar_opt);
        (*print @@ lazy (Format.asprintf "trace: %a" pr_trace (penv, state2.trace));*)
        (state2.trace, state2.cex_acc, state2.induct, state2.gcexs)
    | Some pvar ->
        if Formula.is_true @@ Evaluator.simplify state2.query then (
          (* ToDo: reachable? *)
          (* for maximal conservativity *)
          print @@ lazy "  no refinement required";
          (state2.trace, state2.cex_acc, state2.induct, state2.gcexs))
        else
          let interp =
            (* building [right] and [left] are the phases [interp-right]
               and [interp-left] under COAR_MUCYC_PHASE_TIME; observation
               only *)
            let right =
              phase_time "interp-right" @@ fun () ->
              let query = Formula.or_of [ state2.query; state2.cex_acc ] in
              Evaluator.simplify
              @@ Formula.and_of [ get_formula penv state2 pvar; query ]
            in
            let left_with rename =
              Evaluator.simplify
              @@ Formula.subst_preds (psub_of penv @@ next_trace_of state2.trace)
              @@ snd
              @@ Formula.rm_quant ~forall:false
              @@ rename
              @@ formula_of seq_map (Some pvar)
            in
            let left =
              phase_time "interp-left" @@ fun () ->
              if not (level_solvers_on ~config) then
                left_with Formula.aconv_tvar
              else
                (* bound names by position, so that the same frames give the
                   same antecedent for a kept solver.  The names become free
                   once the quantifiers are removed, so they must not occur
                   in [right] (which would then share them); fresh names
                   otherwise.  The renaming is the one-pass one: a frame's
                   clause bodies carry [let] chains thousands long, on which
                   renaming each body at its binder is quadratic *)
                let positional = "#pfv" in
                let left =
                  (* the frame [psub_of] reads from the next trace *)
                  let frame =
                    match snd (next_trace_of state2.trace) with
                    | [] -> None
                    | frame :: _ -> Some frame
                  in
                  left_memo_find_or_add seq_map penv
                    (Ident.name_of_pvar pvar, frame)
                    ~build:(fun () ->
                      (* a miss is the phase [interp-left-build] *)
                      phase_time "interp-left-build" @@ fun () ->
                      let positional_names () =
                        let k = ref 0 in
                        Formula.aconv_tvar_norm_scoped (fun () ->
                            incr k;
                            Ident.Tvar (sprintf "%s%d" positional !k))
                      in
                      left_with (positional_names ()))
                in
                if
                  Set.exists (Formula.tvs_of right) ~f:(fun x ->
                      String.is_prefix (Ident.name_of_tvar x) ~prefix:positional)
                then left_with Formula.aconv_tvar
                else left
            in
            print
            @@ lazy
                 (sprintf "  interpolating %s => %s" (Formula.str_of left)
                    (Formula.str_of right));
            (* With [COAR_MUCYC_INTERP_TIME], one [interp-query:] line per
               frame interpolation: the predicate, the number of frames, the
               sizes of the query, of the accumulated counterexamples and of
               the current frame formula, and digests telling repeated
               queries and frames apart. Observation only. *)
            (* the observation below is the phase [interp-obs] *)
            phase_time "interp-obs" (fun () ->
            if interp_time then (
              let digest phi =
                String.prefix
                  (Md5.to_hex (Md5.digest_string (Formula.str_of phi)))
                  8
              in
              let frame = get_formula penv state2 pvar in
              prerr_endline
                (sprintf
                   "interp-query: %s frames %d query conj %d vars %d disj %d \
                    %s cex_acc disj %d frame conj %d %s"
                   (Ident.name_of_pvar pvar)
                   (List.length (snd state2.trace))
                   (Set.length (Formula.conjuncts_of state2.query))
                   (Set.length (Formula.tvs_of state2.query))
                   (Set.length (Formula.disjuncts_of state2.query))
                   (digest state2.query)
                   (if Formula.is_false state2.cex_acc then 0
                    else Set.length (Formula.disjuncts_of state2.cex_acc))
                   (Set.length (Formula.conjuncts_of frame))
                   (digest frame));
              (* One [interp-overlap:] line
                 telling whether this obligation (query or accumulated
                 counterexamples) lies in the union of the cubes earlier
                 calls blocked for [pvar] at any level, and meets it;
                 bounded checks, observation only
                 (the answers are not used, so an unknown is only
                 printed) *)
              if interp_overlap then
                let cached =
                  List.map
                    (Interpolation.SpacerBlocking.cached_cubes interp_session
                       ~pred:(Ident.name_of_pvar pvar))
                    ~f:Formula.and_of
                in
                let obligation =
                  Formula.or_of [ state2.query; state2.cex_acc ]
                in
                let check phis =
                  try
                    match
                      Z3Smt.Z3interface.check_sat ~timeout:(Some 2000)
                        ~id:None (FunEnv.mk_empty ()) phis
                    with
                    | `Unsat -> "unsat"
                    | `Sat _ -> "sat"
                    | _ -> "unknown"
                  with exn_ when not (Common.Timer.is_async exn_) ->
                    "error"
                in
                let started = Common.Clock.now_float () in
                let union = Formula.or_of cached in
                let contained =
                  check [ obligation; Formula.negate union ]
                in
                let meets = check [ obligation; union ] in
                (* the obligation is a disjunction (of projected
                   counterexamples), so also count its disjuncts lying
                   wholly in the union *)
                let disjuncts = Set.to_list (Formula.disjuncts_of obligation) in
                let disj_in =
                  List.count disjuncts ~f:(fun d ->
                      String.equal "unsat" (check [ d; Formula.negate union ]))
                in
                prerr_endline
                  (sprintf
                     "interp-overlap: %s frames %d cubes %d outside %s meets \
                      %s disjuncts_inside %d of %d %.3f s"
                     (Ident.name_of_pvar pvar)
                     (List.length (snd state2.trace))
                     (List.length cached) contained meets disj_in
                     (List.length disjuncts)
                     (Time_float.Span.to_sec
                        (Time_float.diff (Common.Clock.now_float ()) started)))));
            let by_relative_induction =
              match config.relative_induction_interpolant with
              | None -> None
              | Some timeout ->
                  relative_induction_interpolant ~print solve_chc
                    (args_of penv pvar) ~timeout
                    ~lower:(psub_of penv @@ next_trace_of state2.trace)
                    pvar
                    ~body:
                      (snd
                      @@ Formula.rm_quant ~forall:false
                      @@ Formula.aconv_tvar
                      @@ formula_of seq_map (Some pvar))
                    ~frame:(get_formula penv state2 pvar)
                    ~cube:
                      (Evaluator.simplify
                      @@ Formula.or_of [ state2.query; state2.cex_acc ])
                    left
            in
            match
              match by_relative_induction with
              | Some interp -> Some interp
              | None ->
                  interpolate ~session:interp_session
                    ~at:
                      {
                        pred = Ident.name_of_pvar pvar;
                        (* the frame's level counted from the bottom *)
                        level = List.length (snd state2.trace);
                        frames =
                          (* [left] is a function of the clauses of [pvar]
                             and of these frames, up to the renaming of its
                             existentially quantified variables; it is
                             monotone in them, as [formula_of] keeps only the
                             body atoms ([left_atms]), where the predicates
                             occur positively *)
                          lazy
                            (List.map
                               (Map.Poly.data
                                  (psub_of penv @@ next_trace_of state2.trace))
                               ~f:snd);
                        levels_ok = level_store_on ~config;
                        solvers_ok = level_solvers_on ~config;
                      }
                    ~config ~print solve_chc (args_of penv pvar) left right
            with
            | Some interp ->
                let interp = qelim ~config interp in
                print
                @@ lazy (sprintf "  interpolant: %s" (Formula.str_of interp));
                print
                @@ lazy (sprintf "done query for %s" (str_of_head pvar_opt));
                interp
            | None ->
                raise
                  (Search_undecided
                     "no interpolant separates the frame from the query")
          in
          let state3 = set_formula penv state2 pvar interp in
          let state4 =
            if config.monotone_trace then
              {
                state3 with
                trace =
                  prev_trace_of
                  @@ propagate_formula penv
                       (next_trace_of state3.trace)
                       pvar interp;
              }
            else state3
          in
          let trace, induct =
            match config.induction with
            | Some (Config.Normal _) ->
                apply_induct_rule ~print seq_map penv state4.trace state4.induct
            | _ -> (state4.trace, state4.induct)
          in
          (*print @@ lazy (Format.asprintf "trace: %a" pr_trace (penv, trace));*)
          ( trace,
            state4.cex_acc,
            (match config.induction with
            | Some (Config.Normal disj) ->
                add_to_induct induct pvar
                @@ (if disj then Set.concat_map ~f:Formula.disjuncts_of
                    else Fn.id)
                @@ Formula.conjuncts_of interp
            | _ -> induct),
            state4.gcexs )

(* With [COAR_MUCYC_INTERP_TIME], also one [extend-trace: <frames>] line per
   new frame, so that the interpolation lines can be grouped by frame. *)
let extend_trace ~config penv (trace1, trace2) =
  assert (List.is_empty trace1);
  if interp_time then
    prerr_endline
      (sprintf "extend-trace: %d at %.3f s" (List.length trace2)
         (since_origin ()));
  ( trace1,
    if config.top_down_search then
      trace2 @ [ List.map penv ~f:(fun _ -> Formula.mk_false ()) ]
    else
      List.map penv ~f:(fun _ -> Formula.mk_true ()) :: trace2 )

let drop_frame (trace1, trace2) = (trace1, List.tl_exn trace2)

let refine ~config ~print ~interp_session ~cexs penv solve_chc seq_map problem
    (trace : trace)
    =
  match config.refinement_strategy with
  | Solve ->
      (* [config.top_down_search] doesn't matter *)
      solve ~config penv solve_chc problem trace
  | Refine (_cex_typ, com_typ) -> (
      if config.top_down_search then failwith "not implemented"
      else
        (* the shortcut of [query_reuse_refute] needs one body atom per clause
           (a query's complement then reaches a goal violation) and a thread
           strategy that returns each answer to its caller *)
        let config =
          if
            config.query_reuse_refute
            && not
                 ((match com_typ with
                  | Or | Return _ -> true
                  | Yield _ -> false)
                 && Map.Poly.for_all seq_map
                      ~f:
                        (List.for_all ~f:(fun seq ->
                             List.length seq.Sequent.left_atms <= 1)))
          then { config with query_reuse_refute = false }
          else config
        in
        let next =
          generate ~config ~print (fun (trace, query, gcexs) ->
              refine ~config ~print ~interp_session ~cexs solve_chc seq_map penv None
                {
                  trace;
                  query;
                  cex_acc = Formula.mk_false ();
                  induct = empty_induct;
                  gcexs;
                })
        in
        match
          next
            ( extend_trace ~config penv trace (* for goal clause *),
              Formula.mk_false (),
              empty_gcexs )
        with
        | exception Reposed_query_refuted -> (*UNSAT*) Refuted
        | First (_trace, _cex, _induct, _gcexs) -> (*UNSAT*) Refuted (*ToDo*)
        | Second (trace, cex, induct, _gcexs) ->
            if Formula.is_false cex then (*SAT*)
              Refined (drop_frame trace, induct)
            else (*UNSAT*) Refuted (*ToDo*))

(* PPDP 2009's coverage check on the trace's frames
   ([Interpolation.Unwinding.is_covered]). *)
let is_covered ~print penv =
  let covered = Interpolation.Unwinding.is_covered ~print penv in
  fun (trace : trace) -> phase_time "covered" @@ fun () -> covered (snd trace)

(* The depth loop ([Interpolation.Unwinding.search]) with MuCyc's step: a
   new frame (and, under [induction], the induction rule applied), a
   refinement by the configured strategy (with [premise_push], the premise
   facts pushed forward; [interp_session], [cexs] and [pushes] are this
   search's kept state), the coverage check, and, under [check_validity],
   the covering solution checked against the problem. *)
let search ~config ~print ~interp_session ~cexs ~pushes solve_chc penv
    is_covered seq_map problem trace induct =
  let prepare (trace, induct) =
    let trace' = extend_trace ~config penv trace in
    match config.induction with
    | None -> (trace', induct)
    | Some (Config.Normal _) ->
        assert (not config.top_down_search);
        apply_induct_rule ~print seq_map penv trace' induct
    | Some (Config.Light disj) ->
        assert (not config.top_down_search);
        if List.is_empty @@ snd trace then (trace', induct)
        else
          let linduct =
            Map.Poly.of_alist_exn
            @@ List.map2_exn penv
                 (get_frame @@ snd trace)
                 ~f:(fun (pvar, _args) phi ->
                   ( pvar,
                     (if disj then Set.concat_map ~f:Formula.disjuncts_of
                      else Fn.id)
                     @@ Formula.conjuncts_of phi ))
          in
          (fst @@ apply_induct_rule ~print seq_map penv trace' linduct, induct)
  in
  (* an undecided sub-query is reported as such: it is not a refutation, and
     reading it as one would turn "could not decide" into "the property fails" *)
  let refine (trace, induct) =
    match
      refine ~config ~print ~interp_session ~cexs penv solve_chc seq_map
        problem trace
    with
    | Refuted -> Refuted
    | Undecided verdict -> Undecided verdict
    | Refined (trace', induct') ->
        let trace' =
          if config.premise_push then
            push_premise_facts ~print ~memo:pushes seq_map penv
              ~old:(snd trace) trace'
          else trace'
        in
        print
        @@ lazy (Format.asprintf "Trace: @[<v>%a@]" pr_trace (penv, trace'));
        print @@ lazy "";
        Refined
          ( trace',
            match config.induction with
            | Some (Config.Normal _) -> merge_induct induct induct'
            | _ -> induct )
  in
  let accept sol _ =
    if config.check_validity then
      let vc =
        Formula.subst_preds (Map.Poly.of_alist_exn sol)
        @@ Problem.to_formula problem.defs (List.map ~f:fst3 problem.goals)
      in
      match check_sat_within_budget (Formula.negate vc) with
      | `Unsat -> Common.Verdict.Valid
      | `Sat _ -> (* bug of [solve_chc]? *) failwith "The solution found is not valid"
      | `Timeout | `Unknown _ ->
          (* the check could not decide: the solution is neither confirmed
             nor refuted, so the answer is withheld rather than reported *)
          Common.Verdict.Unknown
    else Common.Verdict.Valid
  in
  ( Interpolation.Unwinding.search ~prepare ~refine
      ~covered:(fun (trace', _) -> is_covered ~print trace')
      ~accept (trace, induct),
    [] )

(* The [Tree] expansion: the problem's [Mu] definitions and goals in clause
   form, unwound by [Interpolation.Unwinding.solve_clauses] along occurrence
   paths, each expansion solved as [expansion_solver] says.  This is
   Appendix A of Unno and Kobayashi, "Dependent Type Inference with
   Interpolants" (PPDP 2009): the tree expansion and its covering check; a
   refuted expansion's counterexample goes to [on_counterexample] when
   [report_counterexample] is set.  (The [Depth] expansion is the frame
   search itself, below, with [expansion_solver] choosing who solves its
   expansions.)
   Post: [Valid] only for a solution checked by Z3 against the clauses;
   [Invalid] only for a refuted expansion (no solution of the clauses
   exists); [Unknown] otherwise, with the reason printed. *)
let solve_by_unwinding ~config ~print ~dtenv ?on_counterexample solve_chc penv
    problem =
  let sys = unwinding_system_of penv problem in
  match Interpolation.Unwinding.clauses_of_system ~dtenv sys with
  | exception Interpolation.Unwinding.Not_chc reason ->
      print @@ lazy (sprintf "[FrameSearch] unwinding declined: %s" reason);
      Common.Verdict.Unknown
  | clauses -> (
      let cfg : Interpolation.Unwinding.Config.t =
        {
          expansion = config.expansion_shape;
          back_end =
            (match config.expansion_solver with
            | Config.Chc_solver -> Interpolation.Unwinding.Config.Chc_solver
            | Config.Interpolation (search, leaves) ->
                Interpolation.Unwinding.Config.Recursion_free (search, leaves));
          max_depth = None;
          verbose = config.verbose;
        }
      in
      match
        Interpolation.Unwinding.solve_clauses ~config:cfg ~solve_chc
          ~qelim:(qelim ~config) ~print ~id:None clauses
      with
      | Interpolation.Unwinding.Solved _ -> Common.Verdict.Valid
      | Interpolation.Unwinding.Refuted (cex, _) ->
          (match (cex, on_counterexample) with
          | Some cex, Some f when config.report_counterexample ->
              f (Interpolation.Unwinding.pcsp_counterexample cex)
          | _ -> ());
          Common.Verdict.Invalid
      | Interpolation.Unwinding.Unknown reason ->
          print @@ lazy (sprintf "[FrameSearch] unwinding: unknown: %s" reason);
          Common.Verdict.Unknown)

(* Whether the [Solve] strategy runs through [solve_by_unwinding] rather than
   the frame search: any of the unwinding options away from its default. *)
let unwinding_route config =
  (match config.refinement_strategy with Solve -> true | Refine _ -> false)
  &&
  match config.expansion_shape with
  | Interpolation.Unwinding.Config.Depth -> false
  | Tree -> true

let solve ~config ~print ?(dtenv = Map.Poly.empty) ?on_counterexample
    pcsp_solver problem =
  let open Or_error.Monad_infix in
  pcsp_solver () >>= fun (module PCSPSolver : PCSPSolver.Solver.SolverType) ->
  print @@ lazy (Format.asprintf "Problem: %a" Problem.pr problem);
  assert (Set.is_empty problem.Problem.lemmas);
  let penv =
    List.map problem.Problem.defs ~f:(fun pred -> (pred.name, pred.args))
  in
  let solve_chc ~bpvs arg =
    PCSPSolver.reset ();
    let arg_with_dt =
      PCSP.Problem.map_params arg ~f:(fun params -> { params with dtenv })
    in
    PCSPSolver.solve ~bpvs arg_with_dt
  in
  (* with [Interpolation], the frame search's expansions are solved by the
     recursion-free search instead of [pcsp_solver], whose solver stays the
     [Spacer_chc] leaf's; the last refutation's counterexample is kept *)
  let last_refutation = ref None in
  let solve_expansion =
    match config.expansion_solver with
    | Config.Chc_solver -> solve_chc
    | Config.Interpolation (search, leaves) ->
        Interpolation.Unwinding.recursion_free_solver ~search ~leaves ~solve_chc
          ~qelim:(qelim ~config) ~print
          ~on_refutation:(fun c -> last_refutation := Some c)
  in
  let report verdict =
    (match (verdict, !last_refutation, on_counterexample) with
    | Common.Verdict.Invalid, Some c, Some f when config.report_counterexample
      ->
        f c
    | _ -> ());
    verdict
  in
  if unwinding_route config then
    Or_error.return
      (if List.is_empty problem.Problem.goals then (Common.Verdict.Valid, [])
       else
         ( solve_by_unwinding ~config ~print ~dtenv ?on_counterexample solve_chc
             penv problem,
           [] ))
  else
    phase_time "pre-seq-map" (fun () -> seq_map_of penv problem)
    >>= fun seq_map ->
    if config.top_down_search then print @@ lazy "Start top-down proof search"
    else print @@ lazy "Start bottom-up proof search";
    Or_error.return
    @@
    if List.is_empty problem.Problem.goals then (Common.Verdict.Valid, [])
    else
      try
        let verdict, rest =
          (* what the blocking loop keeps between the frame interpolations
             of this search (each predicate's blocked cubes and level seeds,
             used on bit-vector queries); one session per call of this
             function *)
          search ~config ~print
            ~interp_session:
              (Interpolation.SpacerBlocking.create_session
                 ~options:(blocking_options ~config) ())
            ~pushes:(Common.Ext.Hashtbl.PolyDeep.create ())
            ~cexs:{ bodies = []; sessions = []; checks = 0 }
            solve_expansion penv (is_covered penv) seq_map problem empty_trace
            empty_induct
        in
        (report verdict, rest)
      with Search_undecided reason ->
        print @@ lazy (sprintf "[FrameSearch] undecided: %s" reason);
        (Common.Verdict.Unknown, [])
