(* Solving a recursive Horn clause system by unwinding it into recursion-free
   ones: the loop of Unno and Kobayashi, "Dependent Type Inference with
   Interpolants", PPDP 2009 (its Fig. 5, SOLVE): expand the system to a
   depth, solve the expansion, and stop when the solutions of the copies,
   conjoined level by level, cover the next level (the conjunction of the
   earlier levels implies the next one), which makes that conjunction a
   solution of the original system; a refuted expansion refutes the system.

   A system is given in PPDP's form: one definition [P(x) <= G_P(x)] per
   predicate, whose body [G_P] may apply any predicate of the system, and
   goal formulas [F], each a clause that must be valid (its predicate
   applications occur negatively).  Copies of a predicate are named
   [j$$$P] for level [j].

   This module holds the uniform-depth expansion of PPDP's section 4.1 (one
   copy of every predicate per level, shared by every occurrence at that
   level, as vhorn's [RHCSSolver.expand] and MuCyc's frame search build it),
   the frame-based solving of an expansion by a CHC solver the caller
   supplies, the coverage check, and the depth loop with hooks for what a
   caller does around each step.

   Moved from MuCyc's frame search ([FrameSearch.expand], the [Solve]
   strategy's [solve], [is_covered] and the depth loop of [search]); the
   code is MuCyc's, with the muCLP definitions replaced by this module's
   [system].  Ported in algorithm from vhorn [eee5708e]
   ([src/hcssolver/RHCSSolver.ml]). *)

open Core
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

(* [preds]: every predicate with its formal parameters and its definition's
   body, a formula over the parameters (and existential locals) that may
   apply predicates of [preds]; [goals]: clause formulas that must be valid.
   Invariant: predicate names distinct. *)
type system = {
  preds : (Ident.pvar * sort_env_list * Formula.t) list;
  goals : Formula.t list;
}

let penv_of sys = List.map sys.preds ~f:(fun (p, params, _) -> (p, params))

(* What one step of a search yields.  [Refuted] is a genuine refutation of
   the sub-problem (the constraint solver proved it has no solution), while
   [Undecided] is the constraint solver failing to decide, which the caller
   must not read the same way; it carries the verdict to report, so that a
   budget exhausted and a query given up on stay distinguishable. *)
type 'a step = Refined of 'a | Refuted | Undecided of Common.Verdict.t

let mk_fresh_pvar idx pvar =
  Ident.Pvar (string_of_int idx ^ "$$$" ^ Ident.name_of_pvar pvar)

(* [expand sys pvs level]: the uniform-depth expansion of [sys] to depth
   [level] (PPDP 2009, Definition 4.1, one copy per predicate per level).
   The goals are over the level-0 copies [0$$$P]; for every [l] in [1 ..
   level], every definition is added with its head renamed to level [l -
   1]'s copy and its body over level [l]'s copies; level [level]'s copies
   are named [pvs] (one per predicate of [sys], in order) and head no
   clause.  Returns the clauses, each with the sorts of its variables, and
   the map from [(l, j)] to the name of level [l]'s copy of the [j]-th
   predicate for every [l < level].  Pre: [level >= 0]. *)
let rec expand sys pvs level =
  let penv = penv_of sys in
  let pvren =
    Map.Poly.of_alist_exn
    @@ List.mapi penv ~f:(fun i (pvar, _) -> (pvar, List.nth_exn pvs i))
  in
  if level = 0 then
    ( Set.Poly.of_list
      @@ List.map sys.goals ~f:(fun goal ->
          let phi = Formula.rename_pvars pvren goal in
          (Map.of_set_exn @@ Formula.term_sort_env_of phi, phi)),
      Map.Poly.empty )
  else if level > 0 then
    let level' = level - 1 in
    let pvs' = List.map penv ~f:(fst >> mk_fresh_pvar level') in
    let chcs, pvmap = expand sys pvs' level' in
    ( Set.union chcs @@ Set.Poly.of_list
      @@ List.mapi sys.preds ~f:(fun i (_, args, body) ->
          let senv, body =
            Formula.rm_quant ~forall:true
            @@ Formula.aconv_tvar
            @@ Formula.mk_imply (Formula.rename_pvars pvren body)
            @@ Formula.mk_atom
            @@ Atom.pvar_app_of_senv (List.nth_exn pvs' i) args
          in
          ( Map.force_merge (Map.of_set_exn senv) (Map.Poly.of_alist_exn args),
            body )),
      Map.force_merge pvmap
        (Map.Poly.of_alist_exn
        @@ List.mapi pvs' ~f:(fun j pvar -> ((level', j), pvar))) )
  else failwith "[Unwinding.expand] level >= 0 is required"

(* [solve_frames ~qelim ~dtenv sys solve_chc frames]: the expansion of [sys]
   to depth [List.length frames - 1] handed to [solve_chc] as one CHC
   problem; on a solution, the frames replaced by the copies' solutions
   (level [i]'s copy of the [j]-th predicate is frame [i]'s [j]-th formula),
   a copy the solution does not mention set to [false] (any solution is
   correct there), each formula renamed to the predicate's parameters and
   passed through [qelim].  Pre: [frames] non-empty.  [Refuted] when the
   solver answers [unsat]; an answer that is not a verdict raises. *)
let solve_frames ~qelim ~dtenv sys solve_chc frames =
  assert (Fn.non List.is_empty frames);
  let penv = penv_of sys in
  let chcs, pvmap =
    let level = List.length frames - 1 in
    let pvs = List.map penv ~f:(fst >> mk_fresh_pvar level) in
    let chcs, pvmap = expand sys pvs level in
    ( chcs,
      Map.force_merge pvmap @@ Map.Poly.of_alist_exn
      @@ List.mapi pvs ~f:(fun j pvar -> ((level, j), pvar)) )
  in
  let chcs =
    let params =
      PCSP.Params.make ~dtenv @@ Logic.of_old_sort_env_map
      @@ Term.pred_to_sort_env_map @@ Map.Poly.of_alist_exn
      @@ List.map (Map.Poly.to_alist pvmap) ~f:(fun ((_, j), pvar) ->
          (pvar, List.map ~f:snd @@ snd @@ List.nth_exn penv j))
    in
    PCSP.Problem.of_old_formulas ~params chcs
  in
  let bpvs =
    Set.Poly.of_list @@ List.map ~f:Ident.pvar_to_tvar @@ Map.Poly.data pvmap
  in
  match solve_chc ~bpvs chcs with
  | Result.Ok (PCSP.Problem.Sat sol, _) ->
      let psub = snd @@ CandSolOld.of_subst sol in
      Refined
        (List.mapi frames ~f:(fun i frame ->
             List.mapi (List.zip_exn penv frame) ~f:(fun j ((_, params0), _) ->
                 let pvar = Map.Poly.find_exn pvmap (i, j) in
                 let params, phi =
                   match Map.Poly.find (Map.of_set_exn psub) pvar with
                   | Some res -> res
                   | None ->
                       (params0, Formula.mk_false () (*any solution is OK*))
                 in
                 qelim @@ Evaluator.simplify
                 @@ Formula.rename (ren_of_sort_env_list params params0) phi)))
  | Result.Ok (PCSP.Problem.Unsat _, _) -> Refuted
  | Result.Ok (PCSP.Problem.Unknown, _) -> Undecided Common.Verdict.Unknown
  | Result.Ok (PCSP.Problem.Timeout, _) -> Undecided Common.Verdict.Timeout
  (* anything left is the solver failing rather than answering, which is an
     internal error and not a verdict *)
  | _ -> failwith "Unwinding.solve_frames"

(** {2 The coverage check} *)

let rec is_covered_aux penv convert pre solvers = function
  | [] -> None
  | frame :: trace ->
      if
        List.for_all2_exn solvers frame ~f:(fun solver phi ->
            Z3.Solver.push solver;
            Z3Smt.Z3interface.z3_solver_add solver
              [ convert @@ Formula.negate phi ];
            let res = Z3Smt.Z3interface.z3_check solver [] in
            Z3.Solver.pop solver 1;
            match res with Z3.Solver.UNSATISFIABLE -> true | _ -> false)
      then
        Some
          (List.map2_exn penv pre ~f:(fun (pvar, args) phi ->
               (pvar, (args, phi))))
      else (
        List.iter2_exn solvers frame ~f:(fun solver phi ->
            Z3Smt.Z3interface.z3_solver_add solver [ convert phi ]);
        is_covered_aux penv convert
          (List.map2_exn pre frame ~f:Formula.mk_and)
          solvers trace)

(* [is_covered ~print penv frames]: PPDP's genuineness check (its Fig. 5,
   lines 7-9; Lemma 4.2), per predicate: for the first [k >= 1] such that
   the conjunction of frames [0 .. k-1] implies frame [k] for every
   predicate of [penv] (asked of Z3, one solver per predicate), [Some sol]
   with [sol] that conjunction; [None] when no [k] has it, or [frames] has
   fewer than two frames.  The frames are the copies' solutions with frame
   0 nearest the goals' side of the order the caller keeps.  A Z3 answer
   other than [unsat] counts as not covered. *)
let is_covered ~print penv =
  let cfg = [ ("model", "true") ] in
  let ctx = Z3.mk_context cfg in
  let solvers = List.map penv ~f:(fun _ -> Z3.Solver.mk_solver ctx None) in
  let z3dtenv =
    Z3Smt.Z3interface.z3_dtenv_of_dtenv ctx (LogicOld.get_dtenv ())
  in
  let z3fenv =
    Z3Smt.Z3interface.z3_fenv_of ~id:None ctx [] [] (LogicOld.get_fenv ())
      z3dtenv
  in
  let convert =
    Z3Smt.Z3interface.of_formula_with_z3fenv ~id:None ctx [] [] z3fenv z3dtenv
  in
  fun (frames : Formula.t list list) ->
    print @@ lazy "begin coverage check";
    match frames with
    | [] | [ _ ] ->
        print @@ lazy "end coverage check";
        None
    | frame :: trace ->
        List.iter2_exn solvers frame ~f:(fun solver phi ->
            Z3Smt.Z3interface.z3_solver_reset solver;
            Z3Smt.Z3interface.z3_solver_add solver [ convert phi ]);
        let res = is_covered_aux penv convert frame solvers trace in
        print @@ lazy "end coverage check";
        res

(** {2 The depth loop} *)

(* [search ~prepare ~refine ~covered ~accept state]: PPDP's loop, with the
   step's parts given by the caller: [prepare] deepens the state by one
   level (and may strengthen it), [refine] solves the deepened state,
   [covered] is the coverage check on a refined state and [accept] turns a
   covering solution into the verdict.  The loop ends with [Invalid] on a
   refutation, the carried verdict on [Undecided], [accept]'s verdict on a
   covered state, and otherwise goes one level deeper.  It is bounded by
   nothing: a caller that wants a bound puts it in [prepare] or [refine]. *)
let rec search ~prepare ~refine ~covered ~accept state =
  match refine (prepare state) with
  | Refuted -> Common.Verdict.Invalid
  | Undecided verdict -> verdict
  | Refined state' -> (
      match covered state' with
      | Some sol -> accept sol state'
      | None -> search ~prepare ~refine ~covered ~accept state')

(** {1 PPDP 2009's procedure over clause-form systems} *)

(* The same loop as above, over [RecursionFreeChc]'s clause form, with the
   two expansions of the paper and either back end:

   - [Depth]: Definition 4.1's uniform-depth expansion [Expand(C, i)], one
     copy [P@Li] of every predicate per level [i], the goals over level 0,
     every clause with its head at level [l - 1] and its body at level [l],
     level [i]'s copies heading nothing; [i] grows by one per round, and a
     round's solution is accepted by Fig. 5's check (lines 7-9; Lemma 4.2):
     the first [k] at which the conjunction of levels [0 .. k-1] implies
     level [k], predicate by predicate ([is_covered]).
   - [Tree]: Appendix A's [Expand(C, Pi)] (Definition A.1) over a
     prefix-closed set [Pi] of occurrence paths, a path being a sequence of
     predicate indices: copies [P_j^pi] for every [pi] in [Pi] and every
     predicate [P_j], the goals over [P_j^eps], and for every [pi . i] in
     [Pi] the clauses of [P_i] with their head at [P_i^pi] and their body
     over the copies at [pi . i].  [Pi] starts as [{eps}] and grows as Fig.
     9's MSOLVE grows it: the inner loop looks for a prefix-closed
     [Pi' <= Pi] on which Lemma A.2's check holds ([theta_Pi'(P_i)], the
     conjunction of [P_i]'s solutions at [Pi' \ Leaves(Pi', i)], implies
     [P_i]'s solution at every leaf), adding to [Pi'] the leaf's child when
     it is in [Pi] and otherwise adding it to [Pi] and expanding again.

   Two copies at one path or level are shared by every occurrence there, so
   an expansion need not be body-disjoint ([RecursionFreeChc]'s search
   takes DAGs).  A refuted expansion refutes the system (Lemmas 4.1/A.1:
   every solution of the system solves every expansion).  An accepted
   solution is checked against the recursive system by Z3 before it is
   returned.  The predicate-abstraction fallback of vhorn's [RHCSSolver] is
   not part of the paper and is not here. *)

module R = RecursionFreeChc

module Config = struct
  type expansion = Depth | Tree [@@deriving yojson]

  type back_end =
    | Chc_solver  (** the expansion handed whole to the caller's CHC solver *)
    | Recursion_free of R.search * Interpolant.leaf list
        (** [RecursionFreeChc.solve] with this search and these leaves *)
  [@@deriving yojson]

  type t = {
    expansion : expansion; [@default Tree]
    back_end : back_end;
        [@default
          Recursion_free
            ( R.Single_refutation,
              [
                Interpolant.Farkas_lia;
                Interpolant.Farkas_lra;
                Interpolant.Spacer_chc;
              ] )]
    max_depth : int option; [@default None]
        (** the deepest level ([Depth]) or the longest path ([Tree]) the loop
            expands to before it answers [Unknown]: a bound on the shape, never
            on a clock *)
    verbose : bool; [@default false]
        (** the caller prints each expansion and the reason for an [Unknown] *)
  }
  [@@deriving yojson]
end

type path = int list

type expansion_shape =
  | Levels of int  (** [Expand(C, i)] *)
  | Paths of path list  (** [Expand(C, Pi)] *)

(* PPDP's counterexample (RCAML_PAPER_COVERAGE's definition is the
   project's; here, what this module produces): the expansion at which the
   system was refuted, the model and derivation of the refutation with every
   clause the original system's, and the refuted formula projected onto the
   vocabulary. *)
type counterexample = {
  expansion : expansion_shape;
  witness : R.witness;
      (** [sigma], the derivation over the original system's clauses (each node
          is physically a clause of the system solved), and the refuted formula
      *)
  vocabulary : sort_env_list;
  condition : Formula.t;
      (** [exists (fv(refuted) \ vocabulary). refuted], quantifier-free when the
          elimination succeeded; [sigma] restricted to the vocabulary satisfies
          it *)
}

type result =
  | Solved of R.solution * int
      (** checked against the system by Z3; the number of expansions solved *)
  | Refuted of counterexample option * int
      (** no solution exists; a counterexample when the back end gives one *)
  | Unknown of string

let str_of_path path =
  String.concat ~sep:"." (List.map path ~f:(fun i -> Int.to_string (i + 1)))

let str_of_shape = function
  | Levels i -> sprintf "depth %d" i
  | Paths pi ->
      "{"
      ^ String.concat ~sep:", "
          (List.map pi ~f:(function [] -> "eps" | p -> str_of_path p))
      ^ "}"

(* An expanded system with, for every copy, its predicate and position, and
   for every expanded clause the clause of [sys] it copies. *)
type expanded = {
  esys : R.system;
  copies : (Ident.pvar * (Ident.pvar * [ `Level of int | `Path of path ])) list;
  origin : (R.clause * R.clause) list;
}

let index_of (sys : R.system) p =
  match List.findi sys.preds ~f:(fun _ (q, _) -> Ident.pvar_equal p q) with
  | Some (i, _) -> i
  | None -> failwith ("[Unwinding] undeclared predicate " ^ Ident.name_of_pvar p)

let copy_name p tag = Ident.Pvar (Ident.name_of_pvar p ^ "@" ^ tag)

let expand_with (sys : R.system) positions ~goal ~defs =
  let tag = function
    | `Level l -> sprintf "L%d" l
    | `Path p -> "P" ^ str_of_path p
  in
  let copies =
    List.concat_map positions ~f:(fun pos ->
        List.map sys.preds ~f:(fun (p, ps) ->
            (copy_name p (tag pos), (p, pos), ps)))
  in
  let at pos (a : R.app) = { a with pred = copy_name a.pred (tag pos) } in
  let origin =
    List.concat_map sys.clauses ~f:(fun (c : R.clause) ->
        match c.head with
        | None -> [ ({ c with body = List.map c.body ~f:(at goal) }, c) ]
        | Some h ->
            List.map
              (defs (index_of sys h.pred))
              ~f:(fun (head_pos, body_pos) ->
                ( {
                    c with
                    head = Some (at head_pos h);
                    body = List.map c.body ~f:(at body_pos);
                  },
                  c )))
  in
  {
    esys =
      {
        preds = List.map copies ~f:(fun (n, _, ps) -> (n, ps));
        clauses = List.map origin ~f:fst;
      };
    copies = List.map copies ~f:(fun (n, o, _) -> (n, o));
    origin;
  }

(* [Expand(C, i)]: levels [0 .. i]; a clause of [P] heads level [l - 1] from
   level [l], for [l] in [1 .. i]. *)
let expand_depth sys i =
  expand_with sys
    (List.init (i + 1) ~f:(fun l -> `Level l))
    ~goal:(`Level 0)
    ~defs:(fun _ -> List.init i ~f:(fun l -> (`Level l, `Level (l + 1))))

(* [Expand(C, Pi)]: a clause of [P_i] heads [P_i^pi] from the copies at
   [pi . i], for every [pi . i] in [Pi]. *)
let expand_tree sys pi =
  expand_with sys
    (List.map pi ~f:(fun p -> `Path p))
    ~goal:(`Path [])
    ~defs:(fun i ->
      List.filter_map pi ~f:(fun p ->
          match List.rev p with
          | j :: rparent when j = i -> Some (`Path (List.rev rparent), `Path p)
          | _ -> None))

(* The expansion handed to the CHC solver as one problem: a solution for
   every copy, a copy the solver leaves out at [false]. *)
let solve_by_chc_solver ~solve_chc (esys : R.system) =
  let atom (a : R.app) =
    Formula.mk_atom
      (Atom.mk_pvar_app a.pred
         (List.map (R.params_of esys a.pred) ~f:snd)
         a.args)
  in
  let chcs =
    Set.Poly.of_list
    @@ List.map esys.clauses ~f:(fun (c : R.clause) ->
        let phi =
          Formula.mk_imply
            (Formula.and_of (c.phi :: List.map c.body ~f:atom))
            (match c.head with Some h -> atom h | None -> Formula.mk_false ())
        in
        (Map.of_set_exn (Formula.term_sort_env_of phi), phi))
  in
  let params =
    PCSP.Params.make @@ Logic.of_old_sort_env_map @@ Term.pred_to_sort_env_map
    @@ Map.Poly.of_alist_exn
    @@ List.map esys.preds ~f:(fun (p, ps) -> (p, List.map ps ~f:snd))
  in
  let bpvs =
    Set.Poly.of_list
    @@ List.map esys.preds ~f:(fun (p, _) -> Ident.pvar_to_tvar p)
  in
  match solve_chc ~bpvs (PCSP.Problem.of_old_formulas ~params chcs) with
  | Result.Ok (PCSP.Problem.Sat sol, _) ->
      let psub = Map.of_set_exn (snd (CandSolOld.of_subst sol)) in
      `Solved
        (List.map esys.preds ~f:(fun (p, params0) ->
             match Map.Poly.find psub p with
             | Some (params, phi) ->
                 (p, Formula.rename (ren_of_sort_env_list params params0) phi)
             | None -> (p, Formula.mk_false ())))
  | Result.Ok (PCSP.Problem.Unsat _, _) -> `Refuted None
  | Result.Ok ((PCSP.Problem.Unknown | PCSP.Problem.Timeout), _) ->
      `Unknown "the CHC solver did not decide the expansion"
  | Result.Ok (_, _) -> `Unknown "the CHC solver gave no verdict"
  | Result.Error e -> `Unknown (Error.to_string_hum e)

let solve_expansion ~config ~solve_chc ~qelim ~id e =
  match config.Config.back_end with
  | Config.Chc_solver -> solve_by_chc_solver ~solve_chc e.esys
  | Config.Recursion_free (search, leaves) -> (
      match R.solve ~search ~leaves ~solve_chc ~qelim ~id e.esys with
      | R.Solved theta -> `Solved theta
      | R.No_solution w -> `Refuted (Some w)
      | R.Declined reason -> `Unknown ("the recursion-free back end: " ^ reason)
      )

(* the witness of an expansion's refutation, every clause replaced by the
   original clause it copies (the variables are the same: an expansion
   renames predicates only) *)
let rec map_derivation origin (d : R.derivation) : R.derivation =
  {
    d with
    clause =
      (match
         List.find origin ~f:(fun (copy, _) -> phys_equal copy d.clause)
       with
      | Some (_, c) -> c
      | None -> failwith "[Unwinding] a derivation clause outside the expansion");
    children = List.map d.children ~f:(map_derivation origin);
  }

(* [ce1 sys cex]: the counterexample's derivation is a derivation of [sys]
   -- rooted at a goal, every node a clause of [sys] (physically), every
   child's clause heading the predicate of the body application it stands
   for -- and every instance holds under [sigma] (evaluation, no solver).
   Then no assignment of relations to the predicates solves [sys]: the
   derivation's instances, all true at [sigma], chain from facts to the
   goal's [false] (PPDP 2009's Lemma A.1, read contrapositively). *)
let ce1 (sys : R.system) cex =
  let rec well_formed (d : R.derivation) =
    List.exists sys.clauses ~f:(phys_equal d.clause)
    && List.length d.clause.body = List.length d.children
    && List.for_all2_exn d.clause.body d.children ~f:(fun b child ->
        match child.clause.head with
        | Some h -> Ident.pvar_equal h.pred b.pred && well_formed child
        | None -> false)
  in
  Option.is_none cex.witness.derivation.clause.head
  && well_formed cex.witness.derivation
  && R.derivation_holds cex.witness

let counterexample ~qelim ?vocabulary sys shape e (w : R.witness) =
  let witness = { w with derivation = map_derivation e.origin w.derivation } in
  let goal_env = Set.to_list (R.clause_env witness.derivation.clause) in
  let vocabulary =
    match vocabulary with
    | None -> goal_env
    | Some vs ->
        List.filter goal_env ~f:(fun (v, _) ->
            List.mem vs v ~equal:Ident.tvar_equal)
  in
  let hidden =
    Set.to_list
      (Set.filter (Formula.term_sort_env_of w.refuted) ~f:(fun (v, _) ->
           not (List.exists vocabulary ~f:(fun (x, _) -> Ident.tvar_equal x v))))
  in
  let condition =
    Evaluator.simplify (qelim (Formula.mk_exists_if_bounded hidden w.refuted))
  in
  ignore sys;
  { expansion = shape; witness; vocabulary; condition }

(* Lemma A.2's search for [Pi' <= Pi] (Fig. 9, lines 8-20): [`Accept theta]
   over the original predicates, or [`Grow path] to add to [Pi]. *)
let tree_check ~id (sys : R.system) pi theta =
  let sol p path =
    let name = copy_name p ("P" ^ str_of_path path) in
    match List.Assoc.find theta name ~equal:Ident.pvar_equal with
    | Some phi -> phi
    | None -> Formula.mk_false ()
  in
  let mem set p = List.mem set p ~equal:(List.equal Int.equal) in
  let valid phi = Z3Smt.Z3interface.is_valid ~id (get_fenv ()) phi in
  let rec inner pi' =
    let theta_of i p =
      Formula.and_of
        (List.filter_map pi' ~f:(fun path ->
             if mem pi' (path @ [ i ]) then Some (sol p path) else None))
    in
    let failing =
      List.find_mapi sys.preds ~f:(fun i (p, _) ->
          let th = theta_of i p in
          List.find_map pi' ~f:(fun path ->
              if mem pi' (path @ [ i ]) then None
              else if valid (Formula.mk_imply th (sol p path)) then None
              else Some (path @ [ i ])))
    in
    match failing with
    | None ->
        `Accept (List.mapi sys.preds ~f:(fun i (p, _) -> (p, theta_of i p)))
    | Some child when mem pi child -> inner (pi' @ [ child ])
    | Some child -> `Grow child
  in
  inner [ [] ]

(* [solve_clauses ~config ~solve_chc ~qelim ?vocabulary ~print ~id sys]:
   PPDP 2009's procedure on [sys] (see the section header).  [solve_chc] is
   the CHC solver of the [Chc_solver] back end and of the [Spacer_chc] leaf;
   [qelim] eliminates quantifiers (the projection leaves and the
   counterexample's condition); [vocabulary] restricts the condition to some
   of the refuted goal's variables (all of them by default).
   Pre: every application's predicate declared with its arity; formula
   parts quantifier-free.
   Post: [Solved (theta, _)] only after [RecursionFreeChc.is_solution sys
   theta]; [Refuted] only when an expansion was refuted, with [ce1] holding
   of the counterexample when there is one; [Unknown] otherwise (a back end
   that did not decide, the depth bound, a candidate that failed the
   check). *)
let solve_clauses ~config ~solve_chc ~qelim ?vocabulary ~print ~id
    (sys : R.system) =
  let within depth =
    match config.Config.max_depth with None -> true | Some d -> depth <= d
  in
  let accept rounds theta =
    if R.is_solution ~id sys theta then Solved (theta, rounds)
    else Unknown "the accepted candidate failed the check against the system"
  in
  let refuted rounds shape e = function
    | None -> Refuted (None, rounds)
    | Some w ->
        let cex = counterexample ~qelim ?vocabulary sys shape e w in
        if ce1 sys cex then Refuted (Some cex, rounds)
        else (
          print (lazy "[Unwinding] a counterexample failed its check; dropped");
          Refuted (None, rounds))
  in
  match config.Config.expansion with
  | Config.Depth ->
      let penv = List.map sys.preds ~f:(fun (p, ps) -> (p, ps)) in
      let covered = is_covered ~print penv in
      let rec loop i =
        if not (within i) then Unknown "the depth bound"
        else
          let e = expand_depth sys i in
          print (lazy (sprintf "[Unwinding] depth %d" i));
          match solve_expansion ~config ~solve_chc ~qelim ~id e with
          | `Unknown reason -> Unknown reason
          | `Refuted w -> refuted (i + 1) (Levels i) e w
          | `Solved theta -> (
              let frames =
                List.init (i + 1) ~f:(fun l ->
                    List.map sys.preds ~f:(fun (p, _) ->
                        match
                          List.Assoc.find theta
                            (copy_name p (sprintf "L%d" l))
                            ~equal:Ident.pvar_equal
                        with
                        | Some phi -> phi
                        | None -> Formula.mk_false ()))
              in
              match covered frames with
              | Some sol ->
                  accept (i + 1)
                    (List.map sol ~f:(fun (p, (_, phi)) -> (p, phi)))
              | None -> loop (i + 1))
      in
      loop 0
  | Config.Tree ->
      let rec loop rounds pi =
        let depth =
          List.fold pi ~init:0 ~f:(fun m p -> Int.max m (List.length p))
        in
        if not (within depth) then Unknown "the depth bound"
        else
          let e = expand_tree sys pi in
          print (lazy (sprintf "[Unwinding] Pi = %s" (str_of_shape (Paths pi))));
          match solve_expansion ~config ~solve_chc ~qelim ~id e with
          | `Unknown reason -> Unknown reason
          | `Refuted w -> refuted (rounds + 1) (Paths pi) e w
          | `Solved theta -> (
              match tree_check ~id sys pi theta with
              | `Accept theta -> accept (rounds + 1) theta
              | `Grow child -> loop (rounds + 1) (pi @ [ child ]))
      in
      loop 0 [ [] ]

(** {1 Conversions} *)

exception Not_chc of string

(* [system_of_pcsp pcsp]: the problem's clauses in [RecursionFreeChc]'s form,
   read off its formulas (each universally closed clause formula's negation
   put in disjunctive normal form, one clause per cube: positive predicate
   applications its body, a negative one its head, the rest its formula
   part), a predicate's parameters named [a0 .. an].  Raises [Not_chc] on an
   unknown that is not an ordinary predicate (a kind other than the ordinary
   one, or a non-Boolean unknown), on an application that is not a
   predicate's, and on a disjunctive head. *)
let system_of_pcsp pcsp : R.system =
  let senv = PCSP.Problem.senv_of pcsp in
  Map.Poly.iter_keys senv ~f:(fun x ->
      if not (PCSP.Problem.is_ord_kind pcsp x) then
        raise
          (Not_chc
             (sprintf "%s is not an ordinary predicate" (Ident.name_of_tvar x))));
  let preds =
    Map.Poly.to_alist senv
    |> List.map ~f:(fun (Ident.Tvar n, srt) ->
        if not (Logic.BoolTerm.is_bool_sort (Logic.Sort.ret_of srt)) then
          raise (Not_chc (sprintf "%s is not a predicate" n));
        ( Ident.Pvar n,
          List.mapi (Logic.Sort.args_of srt) ~f:(fun i s ->
              (Ident.Tvar (sprintf "a%d" i), Logic.ExtTerm.to_old_sort s)) ))
  in
  let is_pred p = List.exists preds ~f:(fun (q, _) -> Ident.pvar_equal p q) in
  (* the negation of a clause formula as a disjunction of cubes of literals
     (an atom and its polarity); a pure literal may be any formula without a
     predicate application, which is kept whole *)
  let rec dnf ~pos phi =
    let product c1 c2 =
      List.concat_map c1 ~f:(fun l1 -> List.map c2 ~f:(fun l2 -> l1 @ l2))
    in
    let has_pred phi = Set.exists (Formula.pvs_of phi) ~f:is_pred in
    match phi with
    | _ when not (has_pred phi) ->
        [ [ `Pure (if pos then phi else Formula.mk_neg phi) ] ]
    | Formula.Atom (Atom.App (Predicate.Var (p, _), args, _), _) ->
        [
          [
            (if pos then `Body { R.pred = p; args }
             else `Head { R.pred = p; args });
          ];
        ]
    | Formula.UnaryOp (Not, p, _) -> dnf ~pos:(not pos) p
    | Formula.BinaryOp (And, p, q, _) ->
        if pos then product (dnf ~pos p) (dnf ~pos q)
        else dnf ~pos p @ dnf ~pos q
    | Formula.BinaryOp (Or, p, q, _) ->
        if pos then dnf ~pos p @ dnf ~pos q
        else product (dnf ~pos p) (dnf ~pos q)
    | Formula.BinaryOp (Imply, p, q, _) ->
        dnf ~pos (Formula.mk_or (Formula.mk_neg p) q)
    | _ ->
        raise
          (Not_chc
             ("a clause outside and, or, not and implication: "
            ^ Formula.str_of phi))
  in
  let clauses =
    Set.to_list (PCSP.Problem.old_formulas_of pcsp)
    |> List.concat_map ~f:(fun phi ->
        let _, phi = Formula.rm_quant ~forall:true (Formula.aconv_tvar phi) in
        List.map (dnf ~pos:false phi) ~f:(fun cube ->
            let heads =
              List.filter_map cube ~f:(function `Head a -> Some a | _ -> None)
            in
            {
              R.head =
                (match heads with
                | [] -> None
                | [ a ] -> Some a
                | _ -> raise (Not_chc "a disjunctive head"));
              body =
                List.filter_map cube ~f:(function
                  | `Body a -> Some a
                  | _ -> None);
              phi =
                Formula.and_of
                  (List.filter_map cube ~f:(function
                    | `Pure f -> Some f
                    | _ -> None));
            }))
  in
  { preds; clauses }

(* [clauses_of_system ~dtenv sys]: the formula-form [sys] -- each definition
   [P(x) <= G_P(x)] and each goal -- in clause form, through [PCSP]'s
   clausal form (a body's disjunction becomes one clause per disjunct).
   Raises [Not_chc] as [system_of_pcsp]. *)
let clauses_of_system ~dtenv (sys : system) : R.system =
  (* every variable the clause formula leaves free, with the bound ones
     [rm_quant] removed, is a universally quantified clause variable *)
  let close phi =
    let senv, phi = Formula.rm_quant ~forall:true (Formula.aconv_tvar phi) in
    (Map.of_set_exn (Set.union senv (Formula.term_sort_env_of phi)), phi)
  in
  let formulas =
    List.map sys.goals ~f:close
    @ List.map sys.preds ~f:(fun (p, args, body) ->
        close
          (Formula.mk_imply body
             (Formula.mk_atom (Atom.pvar_app_of_senv p args))))
  in
  let params =
    PCSP.Params.make ~dtenv @@ Logic.of_old_sort_env_map
    @@ Term.pred_to_sort_env_map @@ Map.Poly.of_alist_exn
    @@ List.map sys.preds ~f:(fun (p, args, _) -> (p, List.map ~f:snd args))
  in
  let r =
    system_of_pcsp
      (PCSP.Problem.of_old_formulas ~params (Set.Poly.of_list formulas))
  in
  (* keep the definitions' own parameter names, which the solutions use *)
  {
    r with
    preds =
      List.map r.preds ~f:(fun (p, ps) ->
          match
            List.find sys.preds ~f:(fun (q, _, _) -> Ident.pvar_equal p q)
          with
          | Some (_, args, _) when List.length args = List.length ps -> (p, args)
          | _ -> (p, ps));
  }

(* [solution_of sys theta]: [theta] as [PCSP]'s solution, one lambda per
   predicate over its parameters. *)
let solution_of (sys : R.system) (theta : R.solution) =
  Map.Poly.of_alist_exn
  @@ List.map theta ~f:(fun (p, phi) ->
      ( Ident.pvar_to_tvar p,
        Logic.ExtTerm.mk_lambda
          (Logic.of_old_sort_env_list (R.params_of sys p))
          (Logic.ExtTerm.of_old_formula phi) ))

(* [pcsp_counterexample cex]: the counterexample as [PCSP]'s refutation: each
   derivation node's applications and formula part under its renaming *)
let pcsp_counterexample (cex : counterexample) : PCSP.Problem.counterexample =
  let rec node (d : R.derivation) : PCSP.Problem.cex_node =
    let st = Term.subst d.renaming in
    let app (a : R.app) = (a.pred, List.map a.args ~f:st) in
    {
      head = Option.map d.clause.head ~f:app;
      body = List.map d.clause.body ~f:app;
      constr = Formula.subst d.renaming d.clause.phi;
      sources = [];
      children = List.map d.children ~f:node;
    }
  in
  {
    condition = cex.condition;
    vocabulary = cex.vocabulary;
    model = cex.witness.sigma;
    derivation = node cex.witness.derivation;
    expansion = str_of_shape cex.expansion;
  }

(* [recursion_free_solver ~search ~leaves ~solve_chc ~qelim ~on_refutation]:
   a CHC solver of [solve_chc]'s type for recursion-free problems, which
   solves each one by [RecursionFreeChc.solve] (top-down interpolation
   against the least solution, through [leaves]) instead of handing it on.
   A solution is checked by [RecursionFreeChc.solve] before it is returned;
   a refutation is [Unsat], with its counterexample (over the expansion's
   copies, the goal's variables as vocabulary) handed to [on_refutation]
   first; a problem it declines, or one outside its clause form, is
   [Unknown].  [solve_chc] remains the [Spacer_chc] leaf's solver.
   Used by MuCyc's frame search in place of Spacer: the frame search's
   uniform-depth unwinding with this solver is the constraint solving of Unno
   and Kobayashi, "Dependent Type Inference with Interpolants", PPDP 2009,
   section 4 (Fig. 5), with its counterexample (section 4.2). *)
let recursion_free_solver ~search ~leaves ~solve_chc ~qelim ~on_refutation
    ~print ~bpvs pcsp =
  ignore bpvs;
  match system_of_pcsp pcsp with
  | exception Not_chc reason ->
      print (lazy ("[Unwinding] not a clause system: " ^ reason));
      Ok (PCSP.Problem.Unknown, -1)
  | sys -> (
      match R.solve ~search ~leaves ~solve_chc ~qelim ~id:None sys with
      | R.Solved theta -> Ok (PCSP.Problem.Sat (solution_of sys theta), -1)
      | R.No_solution w ->
          let depth =
            List.fold sys.preds ~init:0 ~f:(fun m (p, _) ->
                match String.lsplit2 (Ident.name_of_pvar p) ~on:'$' with
                | Some (n, _) -> (
                    match Int.of_string_opt n with
                    | Some n -> Int.max m n
                    | None -> m)
                | None -> m)
          in
          let identity = List.map sys.clauses ~f:(fun c -> (c, c)) in
          on_refutation
            (pcsp_counterexample
               (counterexample ~qelim sys (Levels depth)
                  { esys = sys; copies = []; origin = identity }
                  w));
          Ok (PCSP.Problem.Unsat None, -1)
      | R.Declined reason ->
          print
            (lazy ("[Unwinding] the recursion-free search declined: " ^ reason));
          Ok (PCSP.Problem.Unknown, -1))
