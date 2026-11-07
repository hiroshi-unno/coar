open Core
open Common.Ext
open Common.Util
open Ast
open Ast.Logic

(* the constraint-problem entry point: a declared symbol is an unknown to solve for unless the
   file's [set-logic] says this is an ordinary SMT problem *)
(* [define_true names] replaces each unknown of [envs] named in [names] that
   is Boolean-valued and of the ordinary kind by [true] in [phis], and removes
   it from the signature, as if the input had defined it as [true].  It runs
   BEFORE [Problem.make] on purpose: [make] skolemises an existential (a
   written [exists] in a head, a [forall] in a body) into a functional
   predicate exactly when an unknown occurs under it, so an unknown substituted
   after [make] leaves behind the witness predicates its occurrences caused --
   176 of them on one input, where the same input with the unknown written as
   [true] had none.  The second component is the names replaced. *)
(* the unknowns of [envs] named in [names] that are Boolean-valued and of the
   ordinary kind, with their sorts: the ones [define_true] and
   [define_true_sexps] replace *)
let define_true_targets names (envs : SMT.Problem.envs) =
  Map.Poly.filter_mapi envs.exi_senv ~f:(fun ~key ~data ->
      if
        List.mem names (Ident.name_of_tvar key) ~equal:String.equal
        && Stdlib.( = ) (Ast.LogicOld.Sort.ret_of data) Ast.LogicOld.T_bool.SBool
        && (match Map.Poly.find envs.kind_map key with
           | Some Ast.Kind.Ord | None -> true
           | Some _ -> false)
      then Some data
      else None)

let define_true names phis (envs : SMT.Problem.envs) =
  let targets = define_true_targets names envs in
  if Map.Poly.is_empty targets then (phis, envs, [])
  else
    let psub =
      Map.Poly.of_alist_exn
      @@ List.map (Map.Poly.to_alist targets) ~f:(fun (x, sort) ->
          ( Ident.tvar_to_pvar x,
            ( Ast.LogicOld.mk_fresh_sort_env_list
                (Ast.LogicOld.Sort.args_of sort),
              Ast.LogicOld.Formula.mk_true () ) ))
    in
    let keep = Fn.non (Map.Poly.mem targets) in
    ( List.map phis ~f:(Ast.LogicOld.Formula.subst_preds psub),
      {
        envs with
        exi_senv = Map.Poly.filter_keys envs.exi_senv ~f:keep;
        kind_map = Map.Poly.filter_keys envs.kind_map ~f:keep;
        dep_map = Map.Poly.filter_keys envs.dep_map ~f:keep;
      },
      Map.Poly.keys targets )

(* [forced_true_unknowns ~valid phis envs]: the unknowns of the ordinary kind
   that every solution makes [true] everywhere, by one syntactic rule, iterated
   to a fixpoint; [valid] decides the validity of a formula with no unknown
   (the caller's solver), and anything it does not prove decides nothing.

   An assertion is read as [forall x. D1 \/ ... \/ Dk] (its negation normal
   form below the outer universals).  It FORCES a disjunct [Di] when every other
   disjunct is either

   - [not q] for a nullary unknown [q] already known forced, or
   - free of unknowns (pure), and
   - [exists x. /\ (not Dj)] over the pure ones is VALID.

   Then in every model of the theory and every solution, at that [x] every
   other disjunct is false, so [Di] holds.  A forced [Di] that is a nullary
   unknown [q] makes [q] forced; a forced [Di] that is, or is a conjunction
   with a conjunct, [forall y. P(y)] with [y] exactly [P]'s arguments as
   distinct bound variables makes [P] true at every argument -- in every
   solution, so defining [P] as [true] keeps exactly the solutions (minus
   [P]'s, which is [true] in each), and the problem with [P] defined is
   EQUIVALENT to the input: [sat] and [unsat] both transfer.  The point of
   defining it at read time is that the input's body universals over [P] are
   then never skolemised into witnesses.

   Only the formula structure is walked; an unknown inside a term is not
   seen, which can only make the rule fire less. *)
let forced_true_unknowns ~valid phis (envs : SMT.Problem.envs) =
  let open Ast.LogicOld in
  let unknown pv = Map.Poly.mem envs.exi_senv (Ident.pvar_to_tvar pv) in
  let unknown_var x = Map.Poly.mem envs.exi_senv x in
  (* a nullary unknown is read either as a predicate applied to nothing or as
     a Boolean variable compared with a Boolean constant *)
  let lit_of = function
    | Formula.Atom (Atom.App (Predicate.Var (pv, []), [], _), _) when unknown pv
      ->
        Some (pv, true)
    | Formula.Atom
        ( Atom.App
            ( Predicate.Psym ((T_bool.Eq | T_bool.Neq) as op),
              [ Term.Var (x, _, _); Term.FunApp (T_bool.Formula b, [], _) ],
              _ ),
          _ )
      when unknown_var x && (Formula.is_true b || Formula.is_false b) ->
        let eq = match op with T_bool.Eq -> true | _ -> false in
        Some (Ident.tvar_to_pvar x, Bool.equal eq (Formula.is_true b))
    | _ -> None
  in
  let rec lit = function
    | Formula.UnaryOp (Formula.Not, phi, _) ->
        Option.map (lit phi) ~f:(fun (pv, b) -> (pv, not b))
    | phi -> lit_of phi
  in
  let nullary_app phi =
    match lit phi with Some (pv, true) -> Some pv | _ -> None
  in
  let neg_nullary phi =
    match lit phi with Some (pv, false) -> Some pv | _ -> None
  in
  (* [forall y. P(y)], y distinct bound variables, exactly P's arguments *)
  let universal_app = function
    | Formula.Bind (Formula.Forall, bounds, Formula.Atom (Atom.App (Predicate.Var (pv, _), args, _), _), _)
      when unknown pv ->
        let vars =
          List.map args ~f:(function Term.Var (x, _, _) -> Some x | _ -> None)
          |> Option.all
        in
        (match vars with
        | Some xs
          when List.length xs = List.length bounds
               && (not (List.contains_dup xs ~compare:Ident.tvar_compare))
               && List.for_all xs ~f:(fun x ->
                      List.exists bounds ~f:(fun (b, _) -> Ident.tvar_equal x b))
          ->
            Some pv
        | _ -> None)
    | _ -> None
  in
  let rec strip = function
    | Formula.Bind (Formula.Forall, bounds, body, _) ->
        let bs, body = strip body in
        (bounds @ bs, body)
    | phi -> ([], phi)
  in
  let shapes =
    List.map phis ~f:(fun phi ->
        let bounds, body = strip (Formula.nnf_of phi) in
        (bounds, Formula.disjuncts_list_of body))
  in
  let forced0 = ref Set.Poly.empty and forced_p = ref Set.Poly.empty in
  let pure d =
    Set.is_empty (Set.filter (Formula.pvs_of d) ~f:unknown)
    && Set.is_empty (Set.filter (Formula.fvs_of d) ~f:unknown_var)
  in
  let changed = ref true in
  let cache = Hashtbl.Poly.create () in
  while !changed do
    changed := false;
    List.iter shapes ~f:(fun (bounds, ds) ->
        List.iteri ds ~f:(fun i di ->
            let others = List.filteri ds ~f:(fun j _ -> j <> i) in
            let targets_nullary =
              Option.to_list (nullary_app di)
              |> List.filter ~f:(fun q -> not (Set.mem !forced0 q))
            in
            let targets_p =
              List.filter_map (Formula.conjuncts_list_of di) ~f:universal_app
              |> List.filter ~f:(fun p -> not (Set.mem !forced_p p))
            in
            if
              (not (List.is_empty targets_nullary && List.is_empty targets_p))
              && List.for_all others ~f:(fun d ->
                     match neg_nullary d with
                     | Some q -> Set.mem !forced0 q
                     | None -> pure d)
            then
              let pures =
                List.filter others ~f:(fun d -> Option.is_none (neg_nullary d))
              in
              let q =
                Formula.exists bounds
                  (Formula.and_of (List.map pures ~f:Formula.mk_neg))
              in
              let ok =
                match Hashtbl.Poly.find cache q with
                | Some b -> b
                | None ->
                    let b =
                      try valid q
                      with exn_ when not (Common.Timer.is_async exn_) -> false
                    in
                    Hashtbl.Poly.set cache ~key:q ~data:b;
                    b
              in
              if ok then (
                List.iter targets_nullary ~f:(fun q ->
                    forced0 := Set.add !forced0 q;
                    changed := true);
                List.iter targets_p ~f:(fun p ->
                    forced_p := Set.add !forced_p p;
                    changed := true))))
  done;
  Set.to_list (Set.union !forced0 !forced_p)
  |> List.map ~f:Ident.name_of_pvar
  |> List.dedup_and_sort ~compare:String.compare

(* [witness_causing_unknowns phis envs] is the names of the unknowns of
   [envs] that occur in [phis] beneath a quantifier existential in effect: a
   written [exists] at a positive position or a written [forall] at a negative
   one, i.e. an [exists] of the negation normal form.  These are exactly the
   unknowns that make [Problem.make] skolemise a quantifier into a functional
   predicate (it skolemises one exactly when an unknown occurs under it).
   Only the formula structure is walked: a formula embedded in a term is not
   entered, so an unknown that occurs only there is not reported.  The order
   is the order of first occurrence; [define_true] then keeps only the
   Boolean-valued ones of the ordinary kind. *)
let witness_causing_unknowns phis (envs : SMT.Problem.envs) =
  let open Ast.LogicOld in
  let found = ref [] in
  let add pvar =
    let tvar = Ident.pvar_to_tvar pvar in
    if
      Map.Poly.mem envs.exi_senv tvar
      && not (List.mem !found tvar ~equal:Stdlib.( = ))
    then found := tvar :: !found
  in
  let rec walk = function
    | Formula.Bind (Formula.Exists, _, body, _) ->
        Set.iter (Formula.pvs_of body) ~f:add
    | Formula.Bind (_, _, body, _) -> walk body
    | Formula.UnaryOp (_, phi, _) -> walk phi
    | Formula.BinaryOp (_, phi1, phi2, _) ->
        walk phi1;
        walk phi2
    | Formula.LetFormula (_, _, _, body, _) -> walk body
    | Formula.LetRec (_, body, _) -> walk body
    | Formula.Atom _ -> ()
  in
  List.iter phis ~f:(fun phi -> walk (Formula.nnf_of phi));
  List.rev_map !found ~f:Ident.name_of_tvar

(* [unguarded_witness_unknowns phis envs] is the names of the unknowns of
   [envs] that some [exists] of the negation normal form of [phis] binds a
   whole argument of with nothing else beneath it: [exists q. not p(.., q, ..)],
   a written [forall q. p(.., q, ..)] in a premise with no guard.  Such a
   premise holds only where [p] holds of every value at that argument, which
   is how a library function's contract assumes a closure's precondition
   ([requires forall x. pre(x)]); [true] is the definition that makes it hold.
   A guarded one, [forall k. lo <= k < hi => post(false, s[k])], is not
   reported. *)
let unguarded_witness_unknowns phis (envs : SMT.Problem.envs) =
  let open Ast.LogicOld in
  let found = ref [] in
  let add pvar =
    let tvar = Ident.pvar_to_tvar pvar in
    if
      Map.Poly.mem envs.exi_senv tvar
      && not (List.mem !found tvar ~equal:Stdlib.( = ))
    then found := tvar :: !found
  in
  let rec walk = function
    | Formula.Bind
        ( Formula.Exists,
          senv,
          Formula.UnaryOp
            ( Formula.Not,
              Formula.Atom (Atom.App (Predicate.Var (p, _), ts, _), _),
              _ ),
          _ )
      when List.exists ts ~f:(function
             | Term.Var (x, _, _) ->
                 List.exists senv ~f:(fun (y, _) -> Stdlib.( = ) x y)
             | _ -> false) ->
        add p
    | Formula.Bind (_, _, body, _) -> walk body
    | Formula.UnaryOp (_, phi, _) -> walk phi
    | Formula.BinaryOp (_, phi1, phi2, _) ->
        walk phi1;
        walk phi2
    | Formula.LetFormula (_, _, _, body, _) -> walk body
    | Formula.LetRec (_, body, _) -> walk body
    | Formula.Atom _ -> ()
  in
  List.iter phis ~f:(fun phi -> walk (Formula.nnf_of phi));
  List.rev_map !found ~f:Ident.name_of_tvar

(* [unknown_mention_tests unknown_tvar] is a pair of tests, of a formula and
   of a term, answering whether a free variable or a free predicate variable
   of it names an unknown ([unknown_tvar] of its name):
   [unknown_mention_tests_def] is the definition. *)
let unknown_mention_tests_def unknown_tvar =
  let open Ast.LogicOld in
  let unknown p = unknown_tvar (Ident.pvar_to_tvar p) in
  ( (fun phi ->
      Set.exists (Formula.pvs_of phi) ~f:unknown
      || Set.exists (Formula.fvs_of phi) ~f:unknown_tvar),
    fun t ->
      Set.exists (Term.pvs_of t) ~f:unknown
      || Set.exists (Term.fvs_of t) ~f:unknown_tvar )

let unknown_mention_tests_with ~ffind ~fadd ~tfind ~tadd unknown_tvar =
  let open Ast.LogicOld in
  let mentions_unknown_def, term_mentions_unknown_def =
    unknown_mention_tests_def unknown_tvar
  in
  (* [lower_bound_relax] asks these tests at every node its walks visit, of
     the whole subformula, and each answer of the definition folds that
     subformula into two sets: on a large input that is quadratic, and it was
     most of the time of reading one.  So each answer is kept for the physical node it was
     asked of, and a connective's answer is composed from its children's:
     the free variables and predicate variables of a connective are the
     union of its children's, and a binder or a [let] removes only the
     names it binds, so where it binds no unknown's name its answer is its
     body's (and its definition's).  A binder of an unknown's name, and
     every other shape, is answered by the definition.  Both answers are the
     definition's on every formula and term.  The tables are the caller's
     ([ffind], [fadd], [tfind], [tadd]): the walks build formulas of their
     own (renamed binders, relaxed sides), and a table that kept every one of
     them alive for a whole input ran a large input out of memory, so a table
     either holds its keys weakly ([unknown_mention_tests]) or is emptied
     between formulas ([unknown_mention_tests_scoped]). *)
  let term_mentions_unknown t =
    match tfind t with
    | Some r -> r
    | None ->
        let r = term_mentions_unknown_def t in
        tadd t r;
        r
  in
  let binds_unknown_name senv =
    List.exists senv ~f:(fun (x, _) -> unknown_tvar x)
  in
  let rec mentions_unknown phi =
    match ffind phi with
    | Some r -> r
    | None ->
        let r =
          match phi with
          | Formula.UnaryOp (_, a, _) -> mentions_unknown a
          | Formula.BinaryOp (_, a, b, _) ->
              mentions_unknown a || mentions_unknown b
          | Formula.Bind (_, senv, body, _) when not (binds_unknown_name senv)
            ->
              mentions_unknown body
          | Formula.LetFormula (x, _, d, body, _) when not (unknown_tvar x) ->
              term_mentions_unknown d || mentions_unknown body
          | _ -> mentions_unknown_def phi
        in
        fadd phi r;
        r
  in
  (mentions_unknown, term_mentions_unknown)

(* the tests with their answers kept in tables that hold their keys weakly, for the lifetime of the
   tests (see [unknown_mention_tests_with]) *)
let unknown_mention_tests unknown_tvar =
  let open Ast.LogicOld in
  let module Phys (T : sig
    type t
  end) =
  Stdlib.Ephemeron.K1.Make (struct
    type t = T.t

    let equal = phys_equal
    let hash = Stdlib.Hashtbl.hash_param 50 100
  end) in
  let module FTbl = Phys (Formula) in
  let module TTbl = Phys (Term) in
  let fmemo = FTbl.create 1024 and tmemo = TTbl.create 1024 in
  unknown_mention_tests_with
    ~ffind:(FTbl.find_opt fmemo) ~fadd:(FTbl.add fmemo)
    ~tfind:(TTbl.find_opt tmemo) ~tadd:(TTbl.add tmemo) unknown_tvar

(* the same tests with their answers kept in ordinary tables keyed by physical node, and a
   function that empties them.  A table of weak keys costs the collector work for every entry at
   every major cycle; on a 25 MB input whose walks build a renamed copy of each clause, the
   lower-bound relaxation's walk spent most of its time asking these tests (85 of its first
   114 s), and with these tables a whole round's walk took 13-20 s instead of 379 s.  A caller that empties the tables between the formulas it walks
   holds one formula's answers at a time, which that formula holds alive anyway; the answers are
   the definition's either way. *)
let unknown_mention_tests_scoped unknown_tvar =
  let open Ast.LogicOld in
  let module Phys (T : sig
    type t
  end) =
  Stdlib.Hashtbl.Make (struct
    type t = T.t

    let equal = phys_equal
    let hash = Stdlib.Hashtbl.hash_param 50 100
  end) in
  let module FTbl = Phys (Formula) in
  let module TTbl = Phys (Term) in
  let fmemo = FTbl.create 1024 and tmemo = TTbl.create 1024 in
  let mentions, term_mentions =
    unknown_mention_tests_with
      ~ffind:(FTbl.find_opt fmemo) ~fadd:(FTbl.replace fmemo)
      ~tfind:(TTbl.find_opt tmemo) ~tadd:(TTbl.replace tmemo) unknown_tvar
  in
  (mentions, term_mentions, fun () -> FTbl.reset fmemo; TTbl.reset tmemo)

(* Whether [lower_bound_relax] collects the occurrences with the walk that is
   linear in a clause's length (its [occurrences_linear]) instead of the one
   that rebuilds a side condition per disjunction it passes; both give the
   same relaxation up to the numbering of fresh variables (see
   [occurrences_linear]).  Process-wide, set by the solver from its configuration
   (PCSat's [probes.relax_linear_walk]). *)
let lower_bound_linear_walk = ref false

(* Whether [lower_bound_relax]'s one-point elimination ([close]) keeps each condition's
   substituted form and substitutes only into the conditions that mention the variable just
   eliminated ([one_point_incremental]) instead of substituting into every condition at each step
   and searching the list from its start again ([one_point_by_rescan]).  Both take the same
   equations in the same order and give the same conditions (a substitution leaves a condition
   that does not mention the variable as it is); the rescan is quadratic in the number of
   conditions, and a clause of a thousand conjuncts took 20-60 s per occurrence there. *)
let lower_bound_one_point_incremental = ref true

(* Whether [lower_bound_relax] builds what it does not read only on demand:
   each occurrence's side conditions and its closed disjunct are delayed until
   a later round's side condition or the relaxation of the constraints reads
   the unknown's bound.  Only the targets' bounds are read at the end, and a
   non-target's only where a later round's side condition meets it at a
   negative position, so most closings of every unknown in every round were
   never read.  The result is the eager construction's up to the names of
   fresh variables: a delayed closing or substitution draws its fresh names
   later, so they are numbered differently.  The disjuncts of one bound are
   kept in the eager order, so a bound is the eager one with its fresh names
   renamed.  [false]: the eager construction, closing every occurrence as it
   is walked. *)
let lower_bound_lazy = ref true

(* [one_point_by_rescan ~point conds]: while some condition is a point ([point c = Some (y, t)],
   an equation defining the bound [y] by [t]), take the first, drop it and substitute [t] for [y]
   in every other condition; the conditions left.  The order of the remaining conditions is
   theirs in [conds]. *)
let rec one_point_by_rescan ?(subst = Ast.LogicOld.Formula.subst) ~point conds =
  match
    List.find_mapi conds ~f:(fun i c -> Option.map (point c) ~f:(fun r -> (i, r)))
  with
  | None -> conds
  | Some (i, (y, t)) ->
      let sub = Map.Poly.singleton y t in
      one_point_by_rescan ~subst ~point
        (List.filter_mapi conds ~f:(fun j c ->
             if j = i then None else Some (subst sub c)))

(* [one_point_incremental ~point conds]: [one_point_by_rescan ~point conds], computed by keeping
   each condition's current form, the set of positions whose form is a point, and for each
   variable the positions whose form may mention it.  Each step takes the least point position,
   as the rescan's first match is, and substitutes only into the positions whose current form has
   the variable free: in any other the rescan's substitution changes nothing, so the forms and
   hence the points agree with the rescan's at every step.  Contract: the same list as
   [one_point_by_rescan], provided [Formula.subst] returns a formula equal to its argument when the
   substituted variable is not free in it. *)
let one_point_incremental ?(subst = Ast.LogicOld.Formula.subst) ~point conds =
  let open Ast.LogicOld in
  let forms = Array.of_list conds in
  let n = Array.length forms in
  let alive = Array.create ~len:n true in
  let occurs = Hashtbl.Poly.create () in
  let index j =
    Set.iter (Formula.fvs_of forms.(j)) ~f:(fun v ->
        Hashtbl.add_multi occurs ~key:v ~data:j)
  in
  let points = ref Int.Set.empty in
  let classify j =
    if Option.is_some (point forms.(j)) then points := Set.add !points j
    else points := Set.remove !points j
  in
  for j = 0 to n - 1 do
    index j;
    classify j
  done;
  let rec loop () =
    match Set.min_elt !points with
    | None -> ()
    | Some i ->
        let y, t = Option.value_exn (point forms.(i)) in
        alive.(i) <- false;
        points := Set.remove !points i;
        let sub = Map.Poly.singleton y t in
        let tvs_t = Term.fvs_of t in
        let touched = Hashtbl.find_multi occurs y in
        Hashtbl.remove occurs y;
        List.iter
          (List.dedup_and_sort touched ~compare:Int.compare)
          ~f:(fun j ->
            if alive.(j) && Set.mem (Formula.fvs_of forms.(j)) y then (
              forms.(j) <- subst sub forms.(j);
              Set.iter tvs_t ~f:(fun v -> Hashtbl.add_multi occurs ~key:v ~data:j);
              classify j));
        loop ()
  in
  loop ();
  List.filteri (Array.to_list forms) ~f:(fun j _ -> alive.(j))

(* Whether [lower_bound_relax] keeps the answers of its unknown-mention tests in tables emptied
   before each formula it walks ([unknown_mention_tests_scoped]) instead of in tables of weak keys
   kept for the whole relaxation ([unknown_mention_tests]); the answers are the same. *)
let lower_bound_mention_memo_scoped = ref true

(* Given one line per stage of [from_smt2_file] and [lower_bound_relax] with
   the seconds since the stage's start ("[read] ...", "[lower-bound relax]
   ..."); ignores them unless an instrument sets it.  Kept apart from [print],
   whose messages are lazy and which a caller that wants only these lines
   would otherwise have to force, the whole input's diagnostics included. *)
let stage_trace : (string -> unit) ref = ref (fun _ -> ())

(* Whether [close_existential]'s constructor-point rule keeps each
   condition's answer between steps ([constructor_point_rule_kept]) instead of searching
   every condition against every bound variable again after each removal;
   both give the same conditions.  [false]: the rescan, kept as the reference
   the property test compares against. *)
let close_existential_kept_cpoints = ref true

(* The constructor-point rule of [close_existential], repeated while it
   removes a bound variable: the first condition (in list order) that is an
   equation [u = t] (either way round) with, for the first variable [y] of
   [bound] that [t] contains along one constructor path and [u] does not,
   [Problem.solve_constructor_point y u t = Some (s, guards)]; that condition
   is replaced by [guards] at the front, [s] is substituted for [y] in every
   other condition by [subst], and the rule is applied again.  [subst] may
   raise; whatever it raises is passed on.  The conditions are equivalent to
   the input's conjunction under [exists y] for each removed [y]. *)
let rec constructor_point_rule_rescan ~bound ~subst conds =
  let open Ast.LogicOld in
  let found =
    List.find_mapi conds ~f:(fun i c ->
        if not (Formula.is_eq c) then None
        else
          let t1, t2, _ = Formula.let_eq c in
          List.find_map bound ~f:(fun (y, _) ->
              let occurs t = Set.mem (Evaluator.scalar_occurrences_of_term t) y in
              let try_ lhs rhs =
                match rhs with
                | Term.Var _ -> None
                | _ when occurs lhs || not (occurs rhs) -> None
                | _ ->
                    Option.map (Problem.solve_constructor_point y lhs rhs)
                      ~f:(fun (s, guards) -> (i, y, s, guards))
              in
              match try_ t1 t2 with Some r -> Some r | None -> try_ t2 t1))
  in
  match found with
  | None -> conds
  | Some (i, y, s, guards) ->
      let sub = Map.Poly.singleton y s in
      constructor_point_rule_rescan ~bound ~subst
        (guards
        @ List.filter_mapi conds ~f:(fun j c ->
              if j = i then None else Some (subst sub c)))

(* [constructor_point_rule_rescan ~bound ~subst conds], computed keeping per
   condition its free variables, its substitution scope and whether it is
   known to hold no constructor point.  Whether a condition holds a point
   depends only on the condition and on [bound], which the rule never
   changes.  A condition that does not mention the variable just removed and
   whose scope admits the substitution (no binder of it is named by a free
   variable of the replacement, no function head or binder sort conflicts) is
   kept as it is: [Formula.subst] leaves such a condition equal to itself (it
   renames a binder only when the replacement mentions the binder's name), so
   its earlier answer stands.  Every other condition is given to [subst] as
   the rescan gives it.  Each step thus asks only the conditions that are new
   or changed, and the two sides of an equation have their variables
   collected once rather than once per bound variable.  Contract: the same
   list as the rescan, in the same order, and [subst] raising in the same
   cases, provided [subst] is [Formula.subst] behind a check that refuses at
   least what [Evaluator.scalar_substitution_is_safe] refuses.
   [unchecked_unchanged] (only for the property test's mutant) keeps an
   unchanged condition without the scope check. *)
let constructor_point_rule_kept ?(unchecked_unchanged = false) ~bound ~subst
    conds =
  let open Ast.LogicOld in
  let candidate c =
    if not (Formula.is_eq c) then None
    else
      let t1, t2, _ = Formula.let_eq c in
      let v1 = Evaluator.scalar_occurrences_of_term t1 and v2 = Evaluator.scalar_occurrences_of_term t2 in
      List.find_map bound ~f:(fun (y, _) ->
          let try_ lhs vl rhs vr =
            match rhs with
            | Term.Var _ -> None
            | _ when Set.mem vl y || not (Set.mem vr y) -> None
            | _ ->
                Option.map (Problem.solve_constructor_point y lhs rhs)
                  ~f:(fun (s, guards) -> (y, s, guards))
          in
          match try_ t1 v1 t2 v2 with
          | Some r -> Some r
          | None -> try_ t2 v2 t1 v1)
  in
  let entry phi =
    ( phi,
      lazy (Formula.fvs_of phi),
      lazy
        (Evaluator.scalar_substitution_scope_of
           (Term.mk_fsym_app (T_bool.Formula phi) [])),
      ref false )
  in
  let rec find before = function
    | [] -> None
    | ((phi, _, _, none) as e) :: rest -> (
        if !none then find (e :: before) rest
        else
          match candidate phi with
          | None ->
              none := true;
              find (e :: before) rest
          | Some r -> Some (List.rev before, r, rest))
  in
  let rec loop entries =
    match find [] entries with
    | None -> List.map entries ~f:(fun (phi, _, _, _) -> phi)
    | Some (before, (y, s, guards), after) ->
        let sub = Map.Poly.singleton y s in
        let admits scope =
          unchecked_unchanged
          ||
          try
            Evaluator.scalar_substitution_is_safe_in_scope (Lazy.force scope)
              sub
          with exn_ when not (Common.Timer.is_async exn_) -> false
        in
        let update ((phi, fvs, scope, _) as e) =
          if (not (Set.mem (Lazy.force fvs) y)) && admits scope then e
          else entry (subst sub phi)
        in
        let rest = List.map before ~f:update @ List.map after ~f:update in
        loop (List.map guards ~f:entry @ rest)
  in
  loop (List.map conds ~f:entry)

(* [close_existential bound conds] is [exists bound. /\ conds] after the
   one-point rule on the equations that define a bound variable, then
   simplified; equivalent to it in every model of the background theory.
   [split_secs], [elim_secs] and [simplify_secs] accumulate the seconds spent
   splitting the conditions, in the one-point elimination and in the
   simplifier, for a stage trace.

   With [constructor_points], a bound variable that an equation determines
   through a path of constructor applications ([u = C(.., y, ..)], [u] free of
   [y]) is also removed, by [Problem.solve_constructor_point]: the equation is
   [y = s /\ guards] with [s] reading [y]'s position off [u] by selectors,
   then [exists y. y = s /\ phi] is [phi[s/y]] -- exact too.  Without it an
   equation such as [f = mut(tuple(mut a b), c)] with [a b c] bound keeps all
   three bound, and the closed formula keeps a quantifier the one-point rule
   could have removed. *)
let close_existential ?(constructor_points = false) ~split_secs ~elim_secs
    ~simplify_secs bound conds =
  let open Ast.LogicOld in
  let exception Unsafe_substitution in
  let fallback = Formula.mk_exists bound (Formula.and_of conds) in
  let subst sub phi =
    if Evaluator.scalar_substitution_is_safe sub phi then Formula.subst sub phi
    else raise Unsafe_substitution
  in
  try
  (* with [constructor_points], a bound variable of a datatype with one
     constructor is replaced by that constructor over fresh bound variables,
     one per field (every value of the sort is so built, so [exists y. phi] is
     [exists y1 .. yn. phi[C(y1, .., yn)/y]]), nested fields included up to a
     depth of four; the one-point rules then reach a variable that only
     selectors read, which no equation of its own defines *)
  let bound, conds =
    if not constructor_points then (bound, conds)
    else
      let single = function
        | T_dt.SDT dt when Datatype.is_dt dt -> (
            match Datatype.conses_of dt with
            | [ cons ] -> Some (dt, cons)
            | _ -> None)
        | _ -> None
      in
      let rec expand depth bound conds =
        if depth <= 0 then (bound, conds)
        else
          let changed = ref false in
          let bound', sub =
            List.fold bound ~init:([], []) ~f:(fun (acc, sub) (y, sort) ->
                match single sort with
                | Some (dt, cons) ->
                    changed := true;
                    let sorts = Datatype.sorts_of_cons dt cons in
                    let ys =
                      List.map sorts ~f:(fun s -> (Ident.mk_fresh_tvar (), s))
                    in
                    ( List.rev_append ys acc,
                      ( y,
                        T_dt.mk_cons dt (Datatype.name_of_cons cons)
                          (List.map ys ~f:(fun (z, s) -> Term.mk_var z s)) )
                      :: sub )
                | None -> ((y, sort) :: acc, sub))
          in
          if not !changed then (bound, conds)
          else
            let sub = Map.Poly.of_alist_exn sub in
            expand (depth - 1) (List.rev bound')
              (List.map conds ~f:(subst sub))
      in
      Common.PhaseTime.with_phase "ce-expand" (fun () -> expand 4 bound conds)
  in
  let is_bound y = List.exists bound ~f:(fun (x, _) -> Stdlib.( = ) x y) in
  let point c =
    if not (Formula.is_eq c) then None
    else
      let t1, t2, _ = Formula.let_eq c in
      let var a t =
        match a with
        | Term.Var (y, _, _)
          when is_bound y && not (Set.mem (Evaluator.scalar_occurrences_of_term t) y) ->
            Some (y, t)
        | _ -> None
      in
      match var t1 t2 with
      | Some r -> Some r
      | None -> (
          match var t2 t1 with
          | Some r -> Some r
          | None when constructor_points -> (
              (* [0 = y - t] and [0 = t - y] (the simplifier's form of
                 [y = t] over integers) define [y] as [t] too *)
              let diff = function
                | Term.FunApp (T_int.Sub, [ a; b ], _) -> Some (a, b)
                | _ -> None
              in
              let zero t = T_int.is_zero t in
              let lin z d =
                if not (zero z) then None
                else
                  match diff d with
                  | Some (a, b) -> (
                      match var a b with Some r -> Some r | None -> var b a)
                  | None -> None
              in
              match lin t1 t2 with Some r -> Some r | None -> lin t2 t1)
          | None -> None)
  in
  let elim conds =
    if !lower_bound_one_point_incremental then
      one_point_incremental ~subst ~point conds
    else one_point_by_rescan ~subst ~point conds
  in
  (* an equation between two applications of datatype constructors is
     the equations of their arguments when the constructors agree and
     [false] when they differ (constructors are injective and
     disjoint), so the arguments become equations the one-point rule can
     use *)
  let rec decompose c =
    if not (Formula.is_eq c) then [ c ]
    else
      match Formula.let_eq c with
      | ( Term.FunApp (T_dt.DTCons (n1, _, _), ts1, _),
          Term.FunApp (T_dt.DTCons (n2, _, _), ts2, _),
          _ ) ->
          if not (String.equal n1 n2) then [ Formula.mk_false () ]
          else (
            match List.map2 ts1 ts2 ~f:Formula.eq with
            | List.Or_unequal_lengths.Ok eqs ->
                List.concat_map eqs ~f:decompose
            | List.Or_unequal_lengths.Unequal_lengths -> [ c ])
      | _ -> [ c ]
  in
  let cpoints conds =
    if !close_existential_kept_cpoints then
      constructor_point_rule_kept ~bound ~subst conds
    else constructor_point_rule_rescan ~bound ~subst conds
  in
  (* twice: the simplification turns equations into the variable-defining
     form the second pass can use *)
  let pass conds =
    let t = Common.Clock.now_s () in
    let split =
      List.concat_map conds ~f:(fun c ->
          List.concat_map (Formula.conjuncts_list_of c) ~f:decompose)
    in
    (* with [constructor_points], a variable an equation defines directly is
       removed first, so that the constructor rule is left the equations
       through constructors *)
    let split =
      if constructor_points then
        Common.PhaseTime.with_phase "ce-cpoints" (fun () ->
            cpoints
              (Common.PhaseTime.with_phase "ce-elim" (fun () -> elim split)))
      else split
    in
    let t1 = Common.Clock.now_s () in
    let body =
      Common.PhaseTime.with_phase "ce-elim" (fun () ->
          Formula.and_of @@ elim split)
    in
    let t2 = Common.Clock.now_s () in
    let r =
      Common.PhaseTime.with_phase "ce-simplify" (fun () ->
          try Evaluator.simplify body
          with exn_ when not (Common.Timer.is_async exn_) -> body)
    in
    let t3 = Common.Clock.now_s () in
    split_secs := !split_secs +. (t1 -. t);
    elim_secs := !elim_secs +. (t2 -. t1);
    simplify_secs := !simplify_secs +. (t3 -. t2);
    r
  in
  let body = pass [ pass conds ] in
  let fvs = Formula.fvs_of body in
  Formula.exists (List.filter bound ~f:(fun (x, _) -> Set.mem fvs x)) body
  with Unsafe_substitution -> fallback

(* [lower_bound_relax ~rounds ~max_size names phis envs] is a relaxation of
   [phis] in which each unknown named in [names] that is Boolean-valued and of
   the ordinary kind ([define_true_targets]) no longer occurs where its
   polarity is definite: an occurrence at a positive position becomes [true],
   and an occurrence at a negative position, [not p(t)] in the negation normal
   form, becomes [not L_p(t)], for a formula [L_p] that mentions no unknown
   and implies [p] under every interpretation satisfying [phis].  The third
   component is the names relaxed, the fourth each relaxed name's bound as
   its parameters and body (absent: [false]); those that no longer occur are
   removed from the signature, as [define_true] does.  An occurrence beneath
   [iff], [xor], a random binder or inside a term is left as it is.

   The lower bounds.  For an unknown [q], each occurrence [q(t)] at a
   positive position of a constraint, reached through conjunctions,
   disjunctions, universals and lets (no existential), gives the disjunct
   [exists y. x = t /\ not S'_1 /\ ... /\ not S'_k], where [y] are the
   universals and let-variables on the path and [S'_j] are the disjuncts met
   beside the path, each made larger: an unknown's atom at a positive position
   becomes [true], one at a negative position [not r(s)] becomes [not L_r(s)]
   with the bound of the previous round, and anything else that mentions an
   unknown becomes [true].  [L_q] is the disjunction of these over [phis],
   starting from [false] and iterated [rounds] times; a disjunct larger than
   [max_size] is dropped, which only weakens the bound.

   Why the bounds hold.  Fix a model of the background theory and an
   interpretation [I] satisfying [phis].  By induction on the round, each
   [L_r] of the previous round implies [I(r)], so each [S'_j] is implied by
   [S_j] under [I]; where the path condition holds every [S_j] is false, and
   the constraint, which holds under [I] for every value of the path's
   universals, then forces [I(q)(t)].  A free variable of a bound is a
   variable the source constraint ranges over, so the inclusion holds for
   every value of it, also where the bound is substituted beneath a binder of
   the same name.

   Why the result is a relaxation.  Under [I], [true] is implied by [p(t)] and
   [not L_p(t)] by [not p(t)], and a formula in negation normal form is
   monotone in its literals, so every constraint of the result holds under [I]
   restricted to the remaining unknowns.  A model of the background theory in
   which the result has no satisfying interpretation is therefore one in which
   [phis] has none: an [unsat] of the result is an [unsat] of [phis] under the
   definition (every model admits an interpretation).  A [sat] of the result
   says nothing and must not be read. *)
let lower_bound_relax ?(print = fun _ -> ()) ?(rounds = 2) ?(max_size = 4000)
    names phis
    (envs : SMT.Problem.envs) =
  let open Ast.LogicOld in
  let targets = define_true_targets names envs in
  if Map.Poly.is_empty targets then (phis, envs, [], [])
  else
    let unknown (Ident.Pvar n) = Map.Poly.mem envs.exi_senv (Ident.Tvar n) in
    let unknown_tvar x = Map.Poly.mem envs.exi_senv x in
    let target (Ident.Pvar n) = Map.Poly.mem targets (Ident.Tvar n) in
    let mentions_unknown, term_mentions_unknown, clear_mentions =
      if !lower_bound_mention_memo_scoped then
        unknown_mention_tests_scoped unknown_tvar
      else
        let m, t = unknown_mention_tests unknown_tvar in
        (m, t, fun () -> ())
    in
    (* the bound of [p] at [ts]; [None] stands for [false] *)
    (* a round's bound of an unknown is its parameters and a delayed body,
       [None] when no disjunct was kept, which stands for [false] as an absent
       bound does *)
    let find_bound bounds p =
      match Map.Poly.find bounds p with
      | None -> None
      | Some (params, body) -> (
          match Lazy.force body with
          | None -> None
          | Some body -> Some (params, body))
    in
    let at bounds p ts =
      match find_bound bounds p with
      | None -> None
      | Some (params, body) ->
          Some
            (Formula.subst
               (Map.Poly.of_alist_exn
               @@ List.map2_exn params ts ~f:(fun (x, _) t -> (x, t)))
               body)
    in
    (* a formula in negation normal form made larger and unknown-free *)
    let rec relax_up bounds phi =
      if not (mentions_unknown phi) then phi
      else
        match phi with
        | Formula.UnaryOp
            ( Formula.Not,
              Formula.Atom (Atom.App (Predicate.Var (p, _), ts, _), _),
              _ )
          when unknown p && not (List.exists ts ~f:term_mentions_unknown) -> (
            match at bounds p ts with
            | Some l -> Formula.mk_neg l
            | None -> Formula.mk_true ())
        | Formula.BinaryOp (Formula.And, a, b, _) ->
            Formula.mk_and (relax_up bounds a) (relax_up bounds b)
        | Formula.BinaryOp (Formula.Or, a, b, _) ->
            Formula.mk_or (relax_up bounds a) (relax_up bounds b)
        | Formula.Bind (((Formula.Forall | Formula.Exists) as b), senv, body, _)
          ->
            Formula.mk_bind b senv (relax_up bounds body)
        | Formula.LetFormula (x, s, d, body, info)
          when not (term_mentions_unknown d) ->
            Formula.mk_let_formula ~info x s d (relax_up bounds body)
        | _ -> Formula.mk_true ()
    in
    let rename senv body =
      let fresh =
        List.map senv ~f:(fun (_, s) -> (Ident.mk_fresh_tvar (), s))
      in
      ( fresh,
        Formula.subst
          (Map.Poly.of_alist_exn
          @@ List.map2_exn senv fresh ~f:(fun (x, _) (y, s) ->
              (x, Term.mk_var y s)))
          body )
    in
    (* the seconds the linear walk spends renaming binders and forcing an
       occurrence's side conditions (the relaxed siblings), for the stage
       trace *)
    let walk_rename_secs = ref 0. and walk_force_secs = ref 0. in
    (* each occurrence of an unknown at a positive position reached without an
       existential: the unknown, its argument sorts and arguments, the path's
       variables and the path condition (innermost first) *)
    let occurrences_quadratic bounds phi =
      let acc = ref [] in
      let rec walk bound conds phi =
        match phi with
        | Formula.Atom (Atom.App (Predicate.Var (p, sorts), ts, _), _)
          when unknown p && not (List.exists ts ~f:term_mentions_unknown) ->
            acc := (p, sorts, ts, bound, Lazy.from_val conds) :: !acc
        | Formula.BinaryOp (Formula.And, a, b, _) ->
            walk bound conds a;
            walk bound conds b
        | Formula.BinaryOp (Formula.Or, a, b, _) ->
            let side s =
              Formula.nnf_of @@ Formula.mk_neg @@ relax_up bounds s
            in
            if mentions_unknown a then walk bound (side b :: conds) a;
            if mentions_unknown b then walk bound (side a :: conds) b
        | Formula.Bind (Formula.Forall, senv, body, _) ->
            let fresh, body = rename senv body in
            walk (bound @ fresh) conds body
        | Formula.LetFormula (x, s, d, body, _)
          when not (term_mentions_unknown d) ->
            let fresh, body = rename [ (x, s) ] body in
            let y, _ = List.hd_exn fresh in
            walk (bound @ fresh) (Formula.eq (Term.mk_var y s) d :: conds) body
        | _ -> ()
      in
      walk [] [] phi;
      !acc
    in
    (* The same occurrences with the same path conditions, built in time
       linear in [phi] where [occurrences_quadratic] is quadratic in the
       length of a disjunction.  Two changes:
       - a side condition is built only when an occurrence beneath it is
         recorded (a lazy cell on the shared path, consed once per level),
         where the quadratic walk built the side of the rest of a disjunction
         at every disjunct that mentions an unknown -- a negated atom
         included, beneath which nothing is recorded;
       - a side condition [nnf (not (relax_up s))] is composed from its
         children's for a conjunction or a disjunction, and kept per physical
         node: [relax_up] maps both connectives to themselves (or returns the
         node unchanged where no unknown occurs) and [nnf_of] of a negated
         [Or] / [And] is the [And] / [Or] of the negated children's, with the
         same plain constructors, so the composed formula is the one
         [nnf_of (mk_neg (relax_up bounds s))] builds.  The nested sides of a
         disjunction's tail are then shared rather than rebuilt per level.
       The result is the quadratic walk's up to the names of fresh
       variables: [at]'s capture-avoiding substitution draws a fresh name
       when an argument would capture a binder of a bound, and the quadratic
       walk made such draws also in the side conditions it discarded or
       rebuilt, so later fresh names are numbered differently (and binder
       lists ordered by name can come out in another order).  The walk's own
       draws ([rename]) are made in the same order. *)
    let occurrences_linear bounds phi =
      let module Memo = Stdlib.Ephemeron.K1.Make (struct
        type t = Formula.t

        let equal = phys_equal
        let hash = Stdlib.Hashtbl.hash_param 50 100
      end) in
      let memo = Memo.create 1024 in
      let rec neg_relax s =
        match Memo.find_opt memo s with
        | Some r -> r
        | None ->
            let r =
              match s with
              | Formula.BinaryOp (Formula.Or, a, b, _) ->
                  Formula.mk_and (neg_relax a) (neg_relax b)
              | Formula.BinaryOp (Formula.And, a, b, _) ->
                  Formula.mk_or (neg_relax a) (neg_relax b)
              | _ -> Formula.nnf_of @@ Formula.mk_neg @@ relax_up bounds s
            in
            Memo.add memo s r;
            r
      in
      let acc = ref [] in
      let timed r f =
        let t = Common.Clock.now_s () in
        let v = f () in
        r := !r +. (Common.Clock.now_s () -. t);
        v
      in
      let rec walk bound conds phi =
        match phi with
        | Formula.Atom (Atom.App (Predicate.Var (p, sorts), ts, _), _)
          when unknown p && not (List.exists ts ~f:term_mentions_unknown) ->
            let forced () =
              timed walk_force_secs (fun () -> List.map conds ~f:Lazy.force)
            in
            acc :=
              ( p,
                sorts,
                ts,
                bound,
                if !lower_bound_lazy then Lazy.from_fun forced
                else Lazy.from_val (forced ()) )
              :: !acc
        | Formula.BinaryOp (Formula.And, a, b, _) ->
            walk bound conds a;
            walk bound conds b
        | Formula.BinaryOp (Formula.Or, a, b, _) ->
            if mentions_unknown a then
              walk bound (lazy (neg_relax b) :: conds) a;
            if mentions_unknown b then
              walk bound (lazy (neg_relax a) :: conds) b
        | Formula.Bind (Formula.Forall, senv, body, _) ->
            let fresh, body = timed walk_rename_secs (fun () -> rename senv body) in
            walk (bound @ fresh) conds body
        | Formula.LetFormula (x, s, d, body, _)
          when not (term_mentions_unknown d) ->
            let fresh, body =
              timed walk_rename_secs (fun () -> rename [ (x, s) ] body)
            in
            let y, _ = List.hd_exn fresh in
            walk (bound @ fresh)
              (Lazy.from_val (Formula.eq (Term.mk_var y s) d) :: conds)
              body
        | _ -> ()
      in
      walk [] [] phi;
      !acc
    in
    let occurrences =
      if !lower_bound_linear_walk then occurrences_linear
      else occurrences_quadratic
    in
    (* the seconds [close] spends splitting its conditions, in the one-point
       elimination and in the simplifier, for the stage trace *)
    let split_secs = ref 0. and elim_secs = ref 0. and simplify_secs = ref 0. in
    (* [exists bound. /\ conds], after the one-point rule on the equations
       that define a bound variable (exact) *)
    let close bound conds =
      close_existential ~split_secs ~elim_secs ~simplify_secs bound conds
    in
    let nnfs =
      List.map phis ~f:(fun phi ->
          try Some (Formula.nnf_of phi)
          with exn_ when not (Common.Timer.is_async exn_) -> None)
    in
    (* the time of each stage, given to [stage_trace], so a slow relaxation
       names its stage *)
    let t0 = Common.Clock.now_s () in
    let stage name =
      !stage_trace
        (sprintf "[lower-bound relax] %s at %.2f s" name
           (Common.Clock.now_s () -. t0))
    in
    let walk_secs = ref 0. and close_secs = ref 0. and n_occ = ref 0 in
    let round bounds =
      let params = Hashtbl.Poly.create () in
      (* per unknown, its occurrences' disjuncts in order, each closed (or
         dropped: [None]) at once or, with [lower_bound_lazy], when the
         unknown's bound is first read *)
      let disjuncts = Hashtbl.Poly.create () in
      walk_secs := 0.;
      close_secs := 0.;
      n_occ := 0;
      List.iter (List.filter_opt nnfs) ~f:(fun phi ->
          clear_mentions ();
          let t = Common.Clock.now_s () in
          let occs = occurrences bounds phi in
          let walked = Common.Clock.now_s () -. t in
          walk_secs := !walk_secs +. walked;
          n_occ := !n_occ + List.length occs;
          if Float.(walked > 1.) then
            stage
              (sprintf
                 "a formula of %d nodes: %d occurrences walked in %.2f s \
                  (so far: rename %.2f s, force %.2f s)"
                 (Formula.ast_size phi) (List.length occs) walked
                 !walk_rename_secs !walk_force_secs);
          let t = Common.Clock.now_s () in
          List.iter (List.rev occs)
            ~f:(fun (p, sorts, ts, bound, conds) ->
              let xs =
                Hashtbl.find_or_add params p ~default:(fun () ->
                    List.map sorts ~f:(fun s -> (Ident.mk_fresh_tvar (), s)))
              in
              let eqs =
                List.map2_exn xs ts ~f:(fun (x, s) t ->
                    Formula.eq (Term.mk_var x s) t)
              in
              let closed () =
                let t = Common.Clock.now_s () in
                let d = close bound (eqs @ List.rev (Lazy.force conds)) in
                if !lower_bound_lazy then
                  close_secs := !close_secs +. (Common.Clock.now_s () -. t);
                if (not (Formula.is_false d)) && Formula.ast_size d <= max_size
                then Some d
                else None
              in
              Hashtbl.add_multi disjuncts ~key:p
                ~data:
                  (if !lower_bound_lazy then Lazy.from_fun closed
                   else Lazy.from_val (closed ())));
          let closed = Common.Clock.now_s () -. t in
          close_secs := !close_secs +. closed;
          if Float.(closed > 1.) then
            stage
              (sprintf
                 "a formula of %d nodes: %d occurrences closed in %.2f s \
                  (so far: split %.2f s, one-point %.2f s, simplify %.2f s)"
                 (Formula.ast_size phi) (List.length occs) closed !split_secs
                 !elim_secs !simplify_secs));
      stage
        (sprintf "round: %d occurrences, walk %.2f s, close %.2f s" !n_occ
           !walk_secs !close_secs);
      Map.Poly.of_alist_exn
      @@ List.map (Hashtbl.to_alist disjuncts) ~f:(fun (p, ds) ->
          ( p,
            ( Hashtbl.find_exn params p,
              lazy
                (match List.filter_map (List.rev ds) ~f:Lazy.force with
                | [] -> None
                | ds -> Some (Formula.or_of ds)) ) ))
    in
    stage "negation normal forms";
    let bounds =
      List.fold (List.init (max 0 rounds) ~f:Fn.id) ~init:Map.Poly.empty
        ~f:(fun bounds _ -> round bounds)
    in
    Map.Poly.iteri targets ~f:(fun ~key ~data:_ ->
        let p = Ident.tvar_to_pvar key in
        print
        @@ lazy
             (match find_bound bounds p with
             | None ->
                 sprintf "[lower-bound relax] %s: false" (Ident.name_of_pvar p)
             | Some (params, body) ->
                 sprintf "[lower-bound relax] %s(%s): %s" (Ident.name_of_pvar p)
                   (String.concat ~sep:","
                      (List.map params ~f:(fun (x, _) -> Ident.name_of_tvar x)))
                   (Formula.str_of body)));
    let rec down phi =
      match phi with
      | Formula.Atom (Atom.App (Predicate.Var (p, _), _, _), _) when target p ->
          Formula.mk_true ()
      | Formula.UnaryOp
          ( Formula.Not,
            Formula.Atom (Atom.App (Predicate.Var (p, _), ts, _), _),
            _ )
        when target p && not (List.exists ts ~f:term_mentions_unknown) -> (
          match at bounds p ts with
          | Some l -> Formula.mk_neg l
          | None -> Formula.mk_true ())
      | Formula.BinaryOp (((Formula.And | Formula.Or) as op), a, b, info) ->
          Formula.mk_binop ~info op (down a) (down b)
      | Formula.Bind (((Formula.Forall | Formula.Exists) as b), senv, body, info)
        ->
          Formula.mk_bind ~info b senv (down body)
      | Formula.LetFormula (x, s, d, body, info) ->
          Formula.mk_let_formula ~info x s d (down body)
      | phi -> phi
    in
    let phis =
      List.map2_exn phis nnfs ~f:(fun phi -> function
        | None -> phi
        | Some nnf ->
            clear_mentions ();
            down nnf)
    in
    stage "relaxed";
    let remaining =
      List.fold phis ~init:Set.Poly.empty ~f:(fun acc phi ->
          Set.union acc
            (Set.union
               (Set.Poly.map (Formula.pvs_of phi) ~f:Ident.pvar_to_tvar)
               (Formula.fvs_of phi)))
    in
    let keep x = Set.mem remaining x || not (Map.Poly.mem targets x) in
    ( phis,
      {
        envs with
        exi_senv = Map.Poly.filter_keys envs.exi_senv ~f:keep;
        kind_map = Map.Poly.filter_keys envs.kind_map ~f:keep;
        dep_map = Map.Poly.filter_keys envs.dep_map ~f:keep;
      },
      Map.Poly.keys targets,
      List.filter_map (Map.Poly.keys targets) ~f:(fun x ->
          Option.map
            (find_bound bounds (Ident.tvar_to_pvar x))
            ~f:(fun b -> (x, b))) )

(* [lower_bound_define ~rounds names phis envs] is [phis] with each unknown
   named in [names] that [lower_bound_relax] targets (Boolean-valued, of the
   ordinary kind) replaced at EVERY occurrence by the lower bound
   [lower_bound_relax] derives for it after [rounds] rounds ([false] where
   none is derived), and removed from the signature; the third component is
   each replaced unknown with its definition (parameters and body).

   Contract.  The result is [phis] under one particular choice of the named
   unknowns, so a solution of it, together with the definitions, is a solution
   of [phis]: a [sat] of the result transfers, and nothing else does (the
   choice may be wrong, and then the result is unsatisfiable while [phis] is
   not).  That the bounds are lower bounds is not used for this; it is why
   the choice is a good guess for an unknown that the problem only assumes
   beneath a universal and establishes by its own clauses -- a closure's
   postcondition that a library loop assumes for every element, whose least
   solution is what the closure's body gives.  With [qf_only] (the default)
   a bound keeps only its quantifier-free disjuncts when it has any. *)
(* Conservative definition admission: reject non-parameter ambient variables,
   including implicit universals not present in the target's dependency
   arguments. Background known heads retain their separate identity; their
   parameter-closed defining contexts are a caller premise. This is not a
   complete dependency analysis through arbitrary known-function contexts. *)
let bound_definition_is_closed (params, body) =
  Ast.Evaluator.known_function_body_is_closed params
    (Ast.LogicOld.T_bool.of_formula body)

let lower_bound_define ?(print = fun _ -> ()) ?(qf_only = true) ~rounds names phis
    (envs : SMT.Problem.envs) =
  let open Ast.LogicOld in
  let _, _, targets, bounds = lower_bound_relax ~print ~rounds names phis envs in
  if List.is_empty targets then (phis, envs, [])
  else
    (* the disjuncts whose condition, below its leading existential, has no
       quantifier, when there is one: a subset of a lower bound's disjuncts is
       a lower bound too, and the quantified ones come from an occurrence
       beneath a universal in a head whose side conditions already assume the
       unknown -- a loop step demanding the postcondition of every element
       passed -- which repeats, quantified, what the closure's own clause
       gives, and turns a decidable definition into one the zero-unknown
       check over sequences does not decide *)
    let qf_disjuncts body =
      let ds = Formula.disjuncts_list_of body in
      let qf d =
        let _, b, _ = Formula.let_exists_or_formula d in
        Formula.is_quantifier_free b
      in
      match List.filter ds ~f:qf with
      | [] -> body
      | kept -> Formula.or_of kept
    in
    let defs =
      List.map targets ~f:(fun x ->
          match List.Assoc.find bounds x ~equal:Ident.tvar_equal with
          | Some (params, body) when qf_only -> (x, (params, qf_disjuncts body))
          | Some b -> (x, b)
          | None ->
              ( x,
                ( mk_fresh_sort_env_list
                    (Sort.args_of (Map.Poly.find_exn envs.exi_senv x)),
                  Formula.mk_false () ) ))
      |> List.filter ~f:(fun (_, d) -> bound_definition_is_closed d)
    in
    let psub =
      Map.Poly.of_alist_exn
      @@ List.map defs ~f:(fun (x, d) -> (Ident.tvar_to_pvar x, d))
    in
    let keep x = not (List.Assoc.mem defs x ~equal:Ident.tvar_equal) in
    ( List.map phis ~f:(Formula.subst_preds psub),
      {
        envs with
        exi_senv = Map.Poly.filter_keys envs.exi_senv ~f:keep;
        kind_map = Map.Poly.filter_keys envs.kind_map ~f:keep;
        dep_map = Map.Poly.filter_keys envs.dep_map ~f:keep;
      },
      defs )

(* [define_formulas defs phis envs] is [phis] with each unknown [x] of [defs]
   replaced at every occurrence by its definition [(params, body)], and
   removed from the signature, as if the input had defined it so. Definitions
   must be parameter-closed; a non-parameter ambient dependency is rejected.
   Assuming parameter-closed background definitions, a solution of the result
   together with [defs] is a solution of [phis]; nothing else transfers. *)
let define_formulas defs phis (envs : SMT.Problem.envs) =
  let open Ast.LogicOld in
  if not (List.for_all defs ~f:(fun (_, d) -> bound_definition_is_closed d)) then
    invalid_arg "define_formulas: non-parameter ambient variables in definition";
  let psub =
    Map.Poly.of_alist_exn
    @@ List.map defs ~f:(fun (x, d) -> (Ident.tvar_to_pvar x, d))
  in
  let keep x = not (List.Assoc.mem defs x ~equal:Ident.tvar_equal) in
  ( List.map phis ~f:(Formula.subst_preds psub),
    {
      envs with
      exi_senv = Map.Poly.filter_keys envs.exi_senv ~f:keep;
      kind_map = Map.Poly.filter_keys envs.kind_map ~f:keep;
      dep_map = Map.Poly.filter_keys envs.dep_map ~f:keep;
    } )

(* [upper_bound_definitions ~rounds ~max_size names phis envs]: for each
   unknown named in [names] that [define_true_targets] admits (Boolean-valued,
   of the ordinary kind) and that occurs at a negative position, its upper
   bound [U_q] (parameters and body) and a list of candidate definitions, each its
   parameters and an unknown-free body, every one of which implies the upper
   bound [U_q] below at every argument.  The list holds the generalisations
   of [U_q] (below), parameter by parameter, then [U_q] itself, the
   quantifier-free ones first; [true], [false] and repeats are left out.

   The upper bounds.  For an unknown [q], each occurrence [not q(t)] at a
   negative position of a constraint (in its negation normal form), reached
   through conjunctions, disjunctions, universals and lets (no existential),
   gives the conjunct [not (exists y. x = t /\ not S'_1 /\ ... /\ not S'_k)],
   where [y] are the universals and let-variables on the path and [S'_j] the
   disjuncts met beside the path made larger: an unknown's atom at a positive
   position [r(s)] becomes [U_r(s)] with the bound of the previous round, one
   at a negative position becomes [true], and anything else that mentions an
   unknown becomes [true].  [U_q] is the conjunction of these, starting from
   [true] and iterated [rounds] times; a conjunct larger than [max_size] is
   dropped, which only weakens the bound.  It is [lower_bound_relax]'s
   construction with the polarities exchanged.

   Why they are upper bounds.  Fix a model and an interpretation [I]
   satisfying [phis].  By induction on the round each [U_r] of the previous
   round is implied by [I(r)], so each [S_j] implies [S'_j] under [I]; where
   the path condition holds and every [S'_j] is false, every [S_j] is false,
   and the constraint, which holds for every value of the path's universals,
   forces [not I(q)(t)].  So [I(q)(x)] implies each conjunct.

   The generalisations.  For a parameter [x_i] of [q], the conjunction of the
   same conjuncts with [x_i] made one more bound variable ([forall x_i. U_q]
   in effect), and, when [x_i]'s sort is a datatype with one constructor of
   several fields, for each field [j], the same with the field's argument
   bound ([forall z. U_q(.., C(sel_1 x_i, .., z, .., sel_n x_i), ..)]).  Each
   implies [U_q].  Why they are worth trying: a precondition of a function
   that takes a mutable borrow is read by the encoding at its argument's
   current value and a prophecy of its final value, and the function's body
   gives an upper bound that holds vacuously unless the prophecy is the one
   the body produces; a caller that assumes the precondition where the
   prophecy is fixed to the current value then learns nothing from [U_q],
   while the field-generalised bound over the prophecy is the condition on the
   current value alone -- the contract the source would write.

   Contract. A candidate respecting [q]'s dependencies is one admissible
   choice of [q]: a problem with [q] defined by it, solved [sat], gives with
   the definition a solution of [phis]; its [unsat] says nothing. Implying
   the necessary upper bound makes a candidate a plausible guess, but does
   not order it below every solution's [q]. Definition admission and solving
   the substituted original obligations are separate proof premises. *)
(* Whether [upper_bound_definitions] builds what it does not read only on
   demand: each round's bound of an unknown, and each occurrence's side
   conditions, are delayed until a later round's occurrence or the targets'
   candidates read them.  The bounds and candidates of the targets are the
   eager construction's up to the names of fresh variables (a delayed
   construction draws its fresh names later, so they are numbered
   differently, and a disjunction ordered by names can come out in another
   order); what is never read is never built.  Every unknown's bound used to
   be closed in every round although only the targets' are returned and only
   the unknowns met in a later round's side conditions are read: on one
   Thrust input 352 closings, about 8 s, of which 92 are read.  [false]: the
   eager construction. *)
let upper_bound_lazy = ref true

let upper_bound_definitions ?(print = fun _ -> ()) ?(rounds = 2)
    ?(max_size = 4000) names phis (envs : SMT.Problem.envs) =
  let open Ast.LogicOld in
  let targets = define_true_targets names envs in
  if Map.Poly.is_empty targets then []
  else
    let unknown (Ident.Pvar n) = Map.Poly.mem envs.exi_senv (Ident.Tvar n) in
    let unknown_tvar x = Map.Poly.mem envs.exi_senv x in
    let mentions_unknown, term_mentions_unknown, clear_mentions =
      unknown_mention_tests_scoped unknown_tvar
    in
    (* a value built when first read ([upper_bound_lazy]) or at once *)
    let delay f = if !upper_bound_lazy then Lazy.from_fun f else Lazy.from_val (f ()) in
    let at bounds p ts =
      match Map.Poly.find bounds p with
      | None -> None
      | Some (params, body) ->
          let body = Lazy.force body in
          let sub = Map.Poly.of_alist_exn
            (List.map2_exn params ts ~f:(fun (x, _) t -> (x, t))) in
          if Evaluator.scalar_substitution_is_safe sub body then
            Some (Formula.subst sub body)
          else None
    in
    (* a formula in negation normal form made larger and unknown-free *)
    let rec enlarge bounds phi =
      if not (mentions_unknown phi) then phi
      else
        match phi with
        | Formula.Atom (Atom.App (Predicate.Var (p, _), ts, _), _)
          when unknown p && not (List.exists ts ~f:term_mentions_unknown) -> (
            match at bounds p ts with
            | Some u -> u
            | None -> Formula.mk_true ())
        | Formula.BinaryOp (Formula.And, a, b, _) ->
            Formula.mk_and (enlarge bounds a) (enlarge bounds b)
        | Formula.BinaryOp (Formula.Or, a, b, _) ->
            Formula.mk_or (enlarge bounds a) (enlarge bounds b)
        | Formula.Bind (((Formula.Forall | Formula.Exists) as b), senv, body, _)
          ->
            Formula.mk_bind b senv (enlarge bounds body)
        | Formula.LetFormula (x, s, d, body, info)
          when not (term_mentions_unknown d) ->
            Formula.mk_let_formula ~info x s d (enlarge bounds body)
        | _ -> Formula.mk_true ()
    in
    let rename senv body =
      let fresh =
        List.map senv ~f:(fun (_, s) -> (Ident.mk_fresh_tvar (), s))
      in
      let sub = Map.Poly.of_alist_exn
        (List.map2_exn senv fresh ~f:(fun (x, _) (y, s) ->
           (x, Term.mk_var y s))) in
      if Evaluator.scalar_substitution_is_safe sub body then
        Some (fresh, Formula.subst sub body)
      else None
    in
    (* each occurrence of an unknown at a negative position reached without
       an existential: the unknown, its argument sorts and arguments, the
       path's variables and the path condition (innermost first) *)
    let occurrences bounds phi =
      let acc = ref [] in
      let rec walk bound conds phi =
        match phi with
        | Formula.UnaryOp
            ( Formula.Not,
              Formula.Atom (Atom.App (Predicate.Var (p, sorts), ts, _), _),
              _ )
          when unknown p && not (List.exists ts ~f:term_mentions_unknown) ->
            acc := (p, sorts, ts, bound, conds) :: !acc
        | Formula.BinaryOp (Formula.And, a, b, _) ->
            walk bound conds a;
            walk bound conds b
        | Formula.BinaryOp (Formula.Or, a, b, _) ->
            let side s =
              delay (fun () ->
                  Formula.nnf_of @@ Formula.mk_neg @@ enlarge bounds s)
            in
            if mentions_unknown a then walk bound (side b :: conds) a;
            if mentions_unknown b then walk bound (side a :: conds) b
        | Formula.Bind (Formula.Forall, senv, body, _) ->
            (match rename senv body with
             | Some (fresh, body) -> walk (bound @ fresh) conds body
             | None -> ())
        | Formula.LetFormula (x, s, d, body, _)
          when not (term_mentions_unknown d) ->
            (match rename [ (x, s) ] body with
             | Some (fresh, body) ->
                 let y, _ = List.hd_exn fresh in
                 walk (bound @ fresh)
                   (Lazy.from_val (Formula.eq (Term.mk_var y s) d) :: conds)
                   body
             | None -> ())
        | _ -> ()
      in
      walk [] [] phi;
      !acc
    in
    let secs () = (ref 0., ref 0., ref 0.) in
    (* [exists bound. /\ conds] with each existential conjunct of [conds]
       (a larger side's negation, holding a previous round's bound) pulled out
       with its variables renamed apart -- exact -- so that the one-point rules
       reach the equations beneath it *)
    let close bound conds =
      let rec flatten (bound, acc) c =
        match c with
        | Formula.Bind (Formula.Exists, ys, body, _) ->
            (match rename ys body with
             | Some (fresh, body) ->
                 List.fold (Formula.conjuncts_list_of body) ~init:(bound @ fresh, acc)
                   ~f:flatten
             | None -> (bound, c :: acc))
        | Formula.BinaryOp (Formula.And, a, b, _) ->
            flatten (flatten (bound, acc) a) b
        | c -> (bound, c :: acc)
      in
      let bound, conds = List.fold conds ~init:(bound, []) ~f:flatten in
      let split_secs, elim_secs, simplify_secs = secs () in
      close_existential ~constructor_points:true ~split_secs ~elim_secs
        ~simplify_secs bound (List.rev conds)
    in
    let nnfs =
      List.filter_map phis ~f:(fun phi ->
          try Some (Formula.nnf_of phi)
          with exn_ when not (Common.Timer.is_async exn_) -> None)
    in
    (* one round: the new bounds, and each unknown's parameters and
       occurrences (bound variables, equations, conditions) *)
    let round bounds =
      let params = Hashtbl.Poly.create () in
      let occs_of = Hashtbl.Poly.create () in
      List.iter nnfs ~f:(fun phi ->
          clear_mentions ();
          List.iter
            (List.rev
               (Common.PhaseTime.with_phase "occurrences" (fun () ->
                    occurrences bounds phi)))
            ~f:(fun (p, sorts, ts, bound, conds) ->
              let xs =
                Hashtbl.find_or_add params p ~default:(fun () ->
                    List.map sorts ~f:(fun s -> (Ident.mk_fresh_tvar (), s)))
              in
              let eqs =
                List.map2_exn xs ts ~f:(fun (x, s) t ->
                    Formula.eq (Term.mk_var x s) t)
              in
              Hashtbl.add_multi occs_of ~key:p
                ~data:(bound, eqs, List.rev conds)));
      let conj_of occs =
        Formula.and_of
        @@ List.filter_map occs ~f:(fun (bound, eqs, conds) ->
               let d =
                 Common.PhaseTime.with_phase "close" (fun () ->
                     close bound (eqs @ List.map conds ~f:Lazy.force))
               in
               if Formula.is_false d || Formula.ast_size d > max_size then None
               else Some (Formula.mk_neg d))
      in
      ( Map.Poly.of_alist_exn
        @@ List.map (Hashtbl.to_alist occs_of) ~f:(fun (p, occs) ->
               (p, (Hashtbl.find_exn params p, delay (fun () -> conj_of (List.rev occs))))),
        params,
        occs_of,
        conj_of )
    in
    let rec iterate k bounds =
      let bounds', params, occs_of, conj_of = round bounds in
      if k <= 1 then (bounds', params, occs_of, conj_of)
      else iterate (k - 1) bounds'
    in
    let bounds, params, occs_of, conj_of =
      Common.PhaseTime.with_phase "rounds" (fun () ->
          iterate (max 1 rounds) Map.Poly.empty)
    in
    let simplify phi =
      try Evaluator.simplify phi
      with exn_ when not (Common.Timer.is_async exn_) -> phi
    in
    List.filter_map (Map.Poly.keys targets) ~f:(fun x ->
        let p = Ident.tvar_to_pvar x in
        match (Map.Poly.find bounds p, Hashtbl.find params p) with
        | None, _ | _, None -> None
        | Some (_, u), Some xs ->
            let u = Lazy.force u in
            let occs = List.rev (Hashtbl.find_exn occs_of p) in
            (* the conjunction over [occs] with the [i]-th equation
               replaced: its parameter, or one field of it, made bound *)
            let generalised i =
              let xi, si = List.nth_exn xs i in
              let with_eq f =
                List.map occs ~f:(fun (bound, eqs, conds) ->
                    let extra, eq = f (List.nth_exn eqs i) in
                    ( bound @ extra,
                      List.mapi eqs ~f:(fun j e -> if j = i then eq else e),
                      conds ))
              in
              let whole =
                with_eq (fun e ->
                    let z = Ident.mk_fresh_tvar () in
                    ( [ (z, si) ],
                      Formula.subst
                        (Map.Poly.singleton xi (Term.mk_var z si))
                        e ))
              in
              let fields =
                match si with
                | T_dt.SDT dt when Datatype.is_dt dt -> (
                    match Datatype.conses_of dt with
                    | [ cons ] ->
                        let name = Datatype.name_of_cons cons in
                        let n = List.length (Datatype.sorts_of_cons dt cons) in
                        if n < 2 then []
                        else
                          List.init n ~f:(fun j ->
                              let sj =
                                List.nth_exn (Datatype.sorts_of_cons dt cons) j
                              in
                              with_eq (fun e ->
                                  let z = Ident.mk_fresh_tvar () in
                                  let v =
                                    T_dt.mk_cons dt name
                                      (List.init n ~f:(fun k ->
                                           if k = j then Term.mk_var z sj
                                           else
                                             T_dt.mk_sel_by_cons dt name k
                                               (Term.mk_var xi si)))
                                  in
                                  ( [ (z, sj) ],
                                    Formula.subst (Map.Poly.singleton xi v) e )))
                    | _ -> [])
                | _ -> []
              in
              fields @ [ whole ]
            in
            let cands =
              Common.PhaseTime.with_phase "generalised" (fun () ->
                  List.concat (List.init (List.length xs) ~f:generalised)
                  |> List.map ~f:conj_of)
            in
            let seen = Hash_set.Poly.create () in
            let defs =
              (* the quantifier-free candidates first, each group in its
                 order: a quantified definition puts a quantifier into every
                 constraint the unknown occurs in, beneath which the
                 zero-unknown check instantiates rather than decides *)
              List.stable_sort
                ~compare:(fun (_, a) (_, b) ->
                  Bool.compare
                    (not (Formula.is_quantifier_free a))
                    (not (Formula.is_quantifier_free b)))
              @@ List.filter_map (cands @ [ u ]) ~f:(fun body ->
                  let body = simplify body in
                  let key = Formula.str_of body in
                  if
                    Formula.is_true body || Formula.is_false body
                    || Hash_set.mem seen key
                  then None
                  else (
                    Hash_set.add seen key;
                    Some (xs, body)))
            in
            List.iteri defs ~f:(fun k (_, body) ->
                print
                @@ lazy
                     (sprintf "[upper-bound definitions] %s #%d: %s"
                        (Ident.name_of_tvar x) k (Formula.str_of body)));
            Some (x, (xs, simplify u), defs))

(* [upper_bound_candidates ~refuted names phis envs]: [upper_bound_definitions]
   of the named unknowns (two rounds: each target, its upper bound and its
   candidates), each target's list without the
   candidates that cannot be a solution's: [refuted] decides that a formula
   with no unknown is invalid (a countermodel found; anything else decides
   nothing), and a candidate [D] is dropped when [L(x) => D(x)] is refuted for
   the lower bound [L] [lower_bound_relax] derives (two rounds; its
   quantifier-free disjuncts, a subset of a lower bound being one too; no
   filter when it has none, since a question about a quantified bound over
   sequences is one Z3 does not decide).  Every solution's [q] contains [L], so a definition
   not containing [L] is no solution; dropping it loses no [sat] the probe
   could give. *)
let upper_bound_candidates ?(print = fun _ -> ()) ~refuted names phis envs =
  let open Ast.LogicOld in
  let cands =
    Common.PhaseTime.with_phase "ub-definitions" (fun () ->
        upper_bound_definitions ~print ~rounds:2 names phis envs)
    |> List.map ~f:(fun (x, bound, defs) ->
         (x, bound, List.filter defs ~f:(fun (params, body) ->
              bound_definition_is_closed (params, body))))
  in
  if List.is_empty cands then []
  else
    let _, _, _, lower =
      Common.PhaseTime.with_phase "ub-lower-bound" (fun () ->
          lower_bound_relax ~rounds:2 names phis envs)
    in
    List.iter lower ~f:(fun (x, (_, body)) ->
        print
        @@ lazy
             (sprintf "[upper-bound definitions] lower bound of %s: %s"
                (Ident.name_of_tvar x) (Formula.str_of body)));
    List.map cands ~f:(fun (x, u, defs) ->
        match List.Assoc.find lower x ~equal:Ident.tvar_equal with
        | None -> (x, u, defs)
        | Some (lparams, lbody) ->
            let qf =
              List.filter (Formula.disjuncts_list_of lbody) ~f:(fun d ->
                  let _, b, _ = Formula.let_exists_or_formula d in
                  Formula.is_quantifier_free b)
            in
            if List.is_empty qf then (x, u, defs)
            else
              let l = Formula.or_of qf in
              (* [L => forall z. phi] is valid exactly when [L => phi] is,
                 [z] not free in [L]: a leading universal is asked about free *)
              let rec strip = function
                | Formula.Bind (Formula.Forall, _, b, _) -> strip b
                | b -> b
              in
              ( x,
                u,
                List.filteri defs ~f:(fun k (params, body) ->
                    let body =
                      Formula.subst
                        (Map.Poly.of_alist_exn
                        @@ List.map2_exn params lparams ~f:(fun (y, _) (z, s) ->
                               (y, Term.mk_var z s)))
                        body
                    in
                    let r =
                      Common.PhaseTime.with_phase "ub-filter" (fun () ->
                          refuted (Formula.mk_imply l (strip body)))
                    in
                    print
                    @@ lazy
                         (sprintf "[upper-bound definitions] %s #%d %s"
                            (Ident.name_of_tvar x) k
                            (if r then "refuted by the lower bound; dropped"
                             else "kept"));
                    not r) ))

(* [define_true_sexps names sexps] is the input with the declaration of each
   unknown named in [names] -- [declare-fun] or [declare-dep-exists-fun] of a
   Boolean result -- replaced by a [define-fun] of the same arguments whose
   body is [true].  Reading that input is reading the file as if it had
   defined the unknown as [true], which [define_true]'s substitution into the
   read formulas is not exactly: a quantifier whose body the substitution
   makes constant is left in place, and its variables became variables of
   their clause that no literal mentions, so the clause set solved was
   equivalent and differently shaped -- and decided differently.  The
   dependency arguments of a [declare-dep-exists-fun] are implicit at every
   application, so the definition takes the declared arguments only. *)
let define_true_sexps names sexps =
  let module S = Ppx_sexp_conv_lib.Sexp in
  let named n = List.mem names n ~equal:String.equal in
  let definition name args =
    S.List
      [
        S.Atom "define-fun";
        S.Atom name;
        S.List
          (List.mapi args ~f:(fun i sort ->
               S.List [ S.Atom (sprintf "define_true_arg!%d" i); sort ]));
        S.Atom "Bool";
        S.Atom "true";
      ]
  in
  List.map sexps ~f:(function
    | S.List [ S.Atom "declare-fun"; S.Atom name; S.List args; S.Atom "Bool" ]
      when named name ->
        definition name args
    | S.List
        [
          S.Atom "declare-dep-exists-fun";
          S.Atom name;
          S.List _;
          S.List args;
          S.Atom "Bool";
        ]
      when named name ->
        definition name args
    | sexp -> sexp)

(* Which eligible definitions [opaque_definitions_sexps] makes universal.
   [Bodies { keep_quantifier_free }]: every eligible one, or with
   [keep_quantifier_free] only those whose body has a quantifier.
   [Goal_congruence]: those applied on both sides of a goal assertion -- one
   whose conclusion applies no unknown -- closed under the definitions their
   bodies apply ([goal_congruence_definitions]); whether a body has a
   quantifier does not enter.  [Goal_cone_congruence]: as [Goal_congruence],
   with a goal's premises extended by the premises of the clauses that
   define the unknowns its premises apply (one step; see
   [goal_congruence_definitions]).  [Bodies_or_goal_congruence
   { keep_quantifier_free }]: those either [Bodies] or [Goal_congruence]
   chooses. *)
type opaque_selection =
  | Bodies of { keep_quantifier_free : bool }
  | Goal_congruence
  | Goal_cone_congruence
  | Bodies_or_goal_congruence of { keep_quantifier_free : bool }

(* [goal_congruence_definitions ~cone ~unknowns ~defined sexps]: the names in
   [defined] applied both in a premise and in the conclusion of some goal
   assertion of [sexps], closed under the names in [defined] that the bodies
   ([defined]'s data) of the names already chosen contain.  A goal assertion
   is [(assert F)] where [F], below its universal quantifiers and [!]
   annotations, is [(=> P C)] or [(not P)] (read as [(=> P false)]) and [C]
   contains no name of [unknowns].  Its conjuncts are those of [P] with
   nested [and]s flattened; a conjunct [(not Q)] is moved to the conclusion,
   since [P' /\ not Q => C] is [P' => C \/ Q], so the conclusion is [C] with
   every such [Q] and the premises are the other conjuncts.  A name is
   applied in a part when it occurs as an atom there (bound names included,
   which can only choose more).
   With [cone], a goal's premises also include the premises of every clause
   -- an assertion of the same shape, conclusion unrestricted -- whose
   conclusion is an application of an unknown applied in the goal's
   premises: the facts that reach the goal through that unknown, which
   Thrust writes as [(=> (and facts) (p args))] beside the goal
   [(=> (and (p args') ...) C)].  Without it such a goal has no definition
   on its premise side and nothing is chosen.  Only one step is taken:
   the defining clauses' own premise unknowns are not followed.  Any subset of the eligible definitions may
   be made universal (the argument at [opaque_definitions_sexps] holds for
   each one separately), so this chooses what to abstract, not whether the
   answer may be read. *)
let goal_congruence_definitions ~cone ~unknowns ~defined sexps =
  let module S = Ppx_sexp_conv_lib.Sexp in
  let rec atoms acc = function
    | S.Atom a -> Set.add acc a
    | S.List l -> List.fold l ~init:acc ~f:atoms
  in
  let rec strip = function
    | S.List [ S.Atom "forall"; _; body ] -> strip body
    | S.List (S.Atom "!" :: body :: _) -> strip body
    | f -> f
  in
  let rec conjuncts = function
    | S.List (S.Atom "and" :: l) -> List.concat_map l ~f:conjuncts
    | f -> [ f ]
  in
  let names_in fs =
    Set.filter ~f:(Map.mem defined)
      (List.fold fs ~init:String.Set.empty ~f:atoms)
  in
  let clauses =
    List.filter_map sexps ~f:(function
      | S.List [ S.Atom "assert"; f ] -> (
          match strip f with
          | S.List [ S.Atom "=>"; p; c ] -> Some (p, c)
          | S.List [ S.Atom "not"; p ] -> Some (p, S.Atom "false")
          | _ -> None)
      | _ -> None)
  in
  (* with [cone]: each unknown to the names in [defined] occurring in the
     premises of the clauses whose conclusion applies it *)
  let defining_premises =
    if not cone then String.Map.empty
    else
      List.fold clauses ~init:String.Map.empty ~f:(fun acc (p, c) ->
          match strip c with
          | (S.Atom u | S.List (S.Atom u :: _)) when Set.mem unknowns u ->
              Map.update acc u ~f:(fun old ->
                  Set.union (names_in [ p ])
                    (Option.value old ~default:String.Set.empty))
          | _ -> acc)
  in
  let both =
    List.fold clauses ~init:String.Set.empty ~f:(fun acc (p, c) ->
        if Set.exists (atoms String.Set.empty c) ~f:(Set.mem unknowns) then acc
        else
          let negated, premises =
            List.partition_map (conjuncts p) ~f:(function
              | S.List [ S.Atom "not"; q ] -> Either.First q
              | q -> Either.Second q)
          in
          let premise_names =
            if not cone then names_in premises
            else
              Set.fold
                (Set.filter ~f:(Set.mem unknowns)
                   (List.fold premises ~init:String.Set.empty ~f:atoms))
                ~init:(names_in premises)
                ~f:(fun acc u ->
                  match Map.find defining_premises u with
                  | None -> acc
                  | Some names -> Set.union acc names)
          in
          Set.union acc (Set.inter premise_names (names_in (c :: negated))))
  in
  let rec close chosen = function
    | [] -> chosen
    | n :: rest ->
        let added =
          match Map.find defined n with
          | None -> []
          | Some body -> Set.to_list (Set.diff (names_in [ body ]) chosen)
        in
        close (List.fold added ~init:chosen ~f:Set.add) (added @ rest)
  in
  close both (Set.to_list both)

(* [opaque_definitions_sexps ~selection sexps] is [(sexps', names)]:
   the input with each eligible [define-fun] replaced, in its place, by a
   [declare-forall-fun] of the same name, argument sorts and result sort (its
   body dropped), and each such name added to the dependency set of every
   later [declare-dep-exists-fun] that already holds every universal function
   the definition's body reaches; [names] are the definitions so replaced.
   A definition is eligible when it has at least one parameter, its body
   reaches no unknown (a [declare-fun], [declare-dep-exists-fun] or
   [declare-rel] name), directly or through the bodies of the definitions it
   applies; of the eligible ones, [selection] ([opaque_selection]) says which
   are replaced.
   What a body reaches is over-approximated by every atom it contains, bound
   names included, which only makes fewer definitions eligible and fewer
   dependencies added.

   Why only a [sat] of the result may be read, and why it is one of the
   input.  Write [P(f)] for the result read with the universal [f] in place of
   the definition [d].  [P(f)] satisfiable means: for every model of the
   theories and every interpretation of the universal functions (each lawful
   one, for those with a law), there are interpretations of the unknowns, each
   depending only on its dependency set, satisfying the clauses.  The input is
   [P(d)], and [d], read in a model, is one interpretation of [f], a function
   of the model and of the universal functions its body reaches.  So
   instantiating [f] by it gives interpretations of the unknowns for [P(d)];
   an unknown whose set holds [f] now depends on [d]'s value, a function of the
   universals in its body, which its set holds too by the condition above,
   and an unknown whose set does not hold [f] did not depend on it.  A law
   premise is attached to the assertions that reach its function through the
   bodies of the definitions they apply, so dropping a body can only drop
   premises, which makes the result stronger.  An [unsat] or an undecided
   answer of [P(f)] says nothing about [P(d)]: the definition constrains [f]
   to one interpretation, and the result asks for all.  Interpretation-
   dependent terms inside a body (a division by zero, an out-of-range
   sequence read) are interpreted per model, as the body is, so the argument
   holds per model of the theories.  Nothing in the argument depends on
   which eligible definitions are replaced: each is instantiated by its own
   body, and a kept definition that applies a replaced one is again the
   input's definition once that one is instantiated. *)
let opaque_definitions_sexps ~selection sexps =
  let module S = Ppx_sexp_conv_lib.Sexp in
  let rec atoms acc = function
    | S.Atom a -> Set.add acc a
    | S.List l -> List.fold l ~init:acc ~f:atoms
  in
  let rec has_quantifier = function
    | S.Atom _ -> false
    | S.List (S.Atom ("forall" | "exists") :: _) -> true
    | S.List l -> List.exists l ~f:has_quantifier
  in
  (* every name a [declare-*] command other than a universal function's, a
     sort's or a datatype's introduces: the unknowns of every kind, and the
     clause variables of [declare-var], which a definition must not reach
     either *)
  let unknowns =
    List.fold sexps ~init:String.Set.empty ~f:(fun acc -> function
      | S.List
          (S.Atom
             ( "declare-forall-fun" | "declare-forall-sort" | "declare-sort"
             | "declare-datatype" | "declare-datatypes"
             | "declare-codatatypes" )
          :: _) ->
          acc
      | S.List (S.Atom cmd :: S.Atom name :: _)
        when String.is_prefix cmd ~prefix:"declare-" ->
          Set.add acc name
      | _ -> acc)
  in
  let universals =
    List.fold sexps ~init:String.Set.empty ~f:(fun acc -> function
      | S.List (S.Atom "declare-forall-fun" :: S.Atom name :: _) ->
          Set.add acc name
      | _ -> acc)
  in
  (* the atoms each definition reaches, its own body's and those of the
     definitions it applies, in input order *)
  let reach = String.Table.create () in
  let reaches_of body =
    let own = atoms String.Set.empty body in
    Set.fold own ~init:own ~f:(fun acc a ->
        match Hashtbl.find reach a with
        | Some r -> Set.union acc r
        | None -> acc)
  in
  List.iter sexps ~f:(function
    | S.List [ S.Atom ("define-fun" | "define-fun-rec"); S.Atom name; _; _; body ]
    | S.List [ S.Atom "define-const"; S.Atom name; _; body ] ->
        Hashtbl.set reach ~key:name ~data:(reaches_of body)
    | _ -> ());
  let by_body ~keep_quantifier_free body =
    (not keep_quantifier_free) || has_quantifier body
  in
  let by_goal ~cone () =
    let defined =
      List.fold sexps ~init:String.Map.empty ~f:(fun acc -> function
        | S.List [ S.Atom "define-fun"; S.Atom name; S.List (_ :: _); _; body ]
          ->
            Map.set acc ~key:name ~data:body
        | _ -> acc)
    in
    Set.mem (goal_congruence_definitions ~cone ~unknowns ~defined sexps)
  in
  let selected =
    match selection with
    | Bodies { keep_quantifier_free } ->
        fun _name body -> by_body ~keep_quantifier_free body
    | Goal_congruence ->
        let chosen = by_goal ~cone:false () in
        fun name _body -> chosen name
    | Goal_cone_congruence ->
        let chosen = by_goal ~cone:true () in
        fun name _body -> chosen name
    | Bodies_or_goal_congruence { keep_quantifier_free } ->
        let chosen = by_goal ~cone:false () in
        fun name body -> by_body ~keep_quantifier_free body || chosen name
  in
  let opaque = String.Table.create () in
  (* in input order, so that a dependency set is extended only by the
     definitions made universal before it *)
  let rewrite = function
    | S.List [ S.Atom "define-fun"; S.Atom name; S.List (_ :: _ as params); ret; body ]
      as sexp -> (
        let r = Option.value (Hashtbl.find reach name) ~default:String.Set.empty in
        if
          Set.exists r ~f:(Set.mem unknowns) || not (selected name body)
        then sexp
        else
          match
            List.map params ~f:(function
              | S.List [ S.Atom _; sort ] -> Some sort
              | _ -> None)
            |> Option.all
          with
          | None -> sexp
          | Some sorts ->
              Hashtbl.set opaque ~key:name ~data:(Set.inter r universals);
              S.List [ S.Atom "declare-forall-fun"; S.Atom name; S.List sorts; ret ])
    | S.List
        [ S.Atom "declare-dep-exists-fun"; S.Atom name; S.List deps; args; ret ]
      ->
        let held =
          List.fold deps ~init:String.Set.empty ~f:(fun acc -> function
            | S.Atom a -> Set.add acc a
            | _ -> acc)
        in
        let added =
          Hashtbl.fold opaque ~init:[] ~f:(fun ~key ~data acc ->
              if Set.is_subset data ~of_:held then key :: acc else acc)
        in
        S.List
          [
            S.Atom "declare-dep-exists-fun";
            S.Atom name;
            S.List
              (deps
              @ List.map ~f:(fun a -> S.Atom a)
                  (List.sort added ~compare:String.compare));
            args;
            ret;
          ]
    | sexp -> sexp
  in
  (* a [define-funs-rec] body is not looked into, so nothing is made
     universal in an input that has one *)
  if
    List.exists sexps ~f:(function
      | S.List (S.Atom "define-funs-rec" :: _) -> true
      | _ -> false)
  then (sexps, [])
  else
    let rewritten =
      List.rev @@ List.fold sexps ~init:[] ~f:(fun acc c -> rewrite c :: acc)
    in
    (rewritten, List.sort (Hashtbl.keys opaque) ~compare:String.compare)

(* [opaque_definitions_of_file ~selection file]: the names
   [opaque_definitions_sexps] would make universal in [file], read without
   building a problem (the parse only); [[]] when the file does not parse *)
let opaque_definitions_of_file ~selection filename =
  try
    let sexps =
      In_channel.with_file filename ~f:(fun ic ->
          let lexbuf = Lexing.from_channel ic in
          SMT.Parser.program SMT.Lexer.token lexbuf)
    in
    snd (opaque_definitions_sexps ~selection sexps)
  with exn when not (Common.Timer.is_async exn) -> []

(* Whether [from_smt2_file] names the input's quantified premises by fresh unknowns before
   [Problem.make] skolemises them ([name_quantified_premises]).  Process-wide, off by default;
   only ever turned on by a caller (the solver, from its configuration), so that every later
   reading in the process gives the same problem. *)
let name_quantified_premises = ref false

(* The fresh unknowns that name a part of a clause so that its clausal form does not multiply:
   those [name_quantified_premises] introduced in every reading of this process so far, and those
   a fixpoint-logic reduction added ([add_premise_names]).  They are of the ordinary kind; what
   sets them apart is that no preprocessing step may eliminate them ([premise_unknowns_of]):
   resolving one away substitutes the part it names back and rebuilds the product.  Atomic,
   because a primal and a dual reduction run in two domains at once and both may add names while
   the other side's preprocessing reads the set. *)
let premise_names : Ident.tvar Set.Poly.t Atomic.t = Atomic.make Set.Poly.empty

(* adds [names] to [premise_names]; safe from any domain (a lost update would let a named part be
   resolved away, so the set is replaced only by compare-and-set) *)
let rec add_premise_names names =
  let old = Atomic.get premise_names in
  if not (Atomic.compare_and_set premise_names old (Set.union old names)) then
    add_premise_names names

(* the unknowns of [senv] that name a quantified premise or a multiplied part of a clause *)
let premise_unknowns_of (senv : (Ident.tvar, 'a) Map.Poly.t) =
  Set.filter (Atomic.get premise_names) ~f:(Map.Poly.mem senv)

(* the counter the fresh names of [name_quantified_premises] are drawn from *)
let premise_counter = ref 0

(* [name_quantified_premises phis envs] is [(phis', envs', names)]: every quantified PREMISE of
   [phis] that would multiply a clause is replaced by an application of a fresh unknown of the
   ordinary kind over the premise's free term variables, and the definition of that unknown is
   added as an assertion.

   A premise here is a written [forall xs. B] at a NEGATIVE position (under an odd number of
   negations, the left of an implication) whose body mentions an unknown: it is an existential
   in effect, [Problem.make] skolemises it into functional witnesses, and the clausal form of the
   clause around it takes one conjunct of [not B] per such premise, so a clause assuming k
   premises whose negated bodies have n_1, ..., n_k conjuncts has n_1 * ... * n_k clauses.  It is
   named when its negated body holds a conjunction that mentions an unknown (a conjunction of
   theory atoms alone stays one pure part and does not multiply), and its free term variables are
   neither a universal of the input (a [declare-forall-fun], or a dependency argument) nor bound
   twice at different sorts.  Below an [iff] or a [xor] the position is both negative and
   positive, and nothing is named there; nor inside a probabilistic binder or a [define-fun-rec].

   The premise [F(ys) = forall xs. B] at a negative position becomes [P(ys)], [ys] its free term
   variables (unknowns excepted), and the assertion [forall ys. F(ys) => P(ys)] is added.  ONE
   direction is needed, and it is that one:

   - every constraint is monotone in each occurrence it holds (a negative one anti-monotone), so
     with [F => P] pointwise, the constraint with [P] in place of [F] at negative positions
     implies the constraint with [F].  A solution of the new problem therefore satisfies every
     constraint of the old one: restricted to the old unknowns it is an old solution;
   - conversely, an old solution extended by [P := F] (the relation [F] denotes, in the same model,
     under the old solution) satisfies the definition, and the new constraints become the old
     ones.  So the new problem is satisfiable in a model whenever the old one is, and a refutation
     of the new problem is one of the old.

   Both are per model of the theory, so satisfiability in the ∀M.∃I sense is preserved both ways.
   The other direction, [P => F], would be needed only at a positive position; none is named.
   The definition still holds [F] at a negative position, where [Problem.make] skolemises it as
   before -- but alone, so its clausal form has n_i clauses and not the product.

   The nested premises of a named premise are named first, inside its definition.  A premise
   reached twice as one physical formula at one position is named once.  Dependency: the fresh
   unknown gets the empty dependency set, which is enough because everything its definition
   depends on beyond its arguments is an unknown applied to explicit arguments -- a dependency
   argument is a universal and excludes the premise.  Nothing here asks a solver. *)
let premise_definitions phis (envs : SMT.Problem.envs) =
  let open Ast.LogicOld in
  (* the fresh unknowns count as unknowns from the moment they are made: a premise whose
     unknowns all lie in premises named inside it still multiplies through their names.  Only a
     formula built after a name was drawn can mention it, so the memoised test stays exact. *)
  let fresh_names = Hash_set.Poly.create () in
  let unknown_tvar x =
    Map.Poly.mem envs.exi_senv x || Hash_set.mem fresh_names x
  in
  let mentions, _ = unknown_mention_tests unknown_tvar in
  let universal x = Map.Poly.mem envs.uni_senv x in
  let taken name =
    let x = Ident.Tvar name in
    Map.Poly.mem envs.exi_senv x || Map.Poly.mem envs.uni_senv x
    || Map.Poly.mem envs.fenv x
  in
  let rec fresh () =
    let name = sprintf "pdef$%d" !premise_counter in
    incr premise_counter;
    if taken name then fresh () else name
  in
  (* whether the clausal form of [not phi] (with [neg]) or of [phi] multiplies: a conjunction
     that mentions an unknown is reached through disjunctions and binders *)
  let rec multiplies neg phi =
    match phi with
    | Formula.UnaryOp (Formula.Not, a, _) -> multiplies (not neg) a
    | Formula.BinaryOp (Formula.And, a, b, _) ->
        if neg then multiplies neg a || multiplies neg b else mentions phi
    | Formula.BinaryOp (Formula.Or, a, b, _) ->
        if neg then mentions phi else multiplies neg a || multiplies neg b
    | Formula.BinaryOp (Formula.Imply, a, b, _) ->
        if neg then mentions phi else multiplies true a || multiplies false b
    | Formula.BinaryOp ((Formula.Iff | Formula.Xor), _, _, _) -> mentions phi
    | Formula.Bind (_, _, body, _) -> multiplies neg body
    | Formula.LetFormula (_, _, _, body, _) -> multiplies neg body
    | Formula.Atom _ | Formula.LetRec _ -> false
  in
  let added = ref [] in
  (* the result of [walk] per physical node and position, so that a subformula shared
     physically is walked, and named, once *)
  let module Memo = Stdlib.Ephemeron.K1.Make (struct
    type t = Formula.t

    let equal = phys_equal
    let hash = Stdlib.Hashtbl.hash_param 50 100
  end) in
  let memo_pos = Memo.create 1024 and memo_neg = Memo.create 1024 in
  let memo_find pos phi =
    Memo.find_opt (if pos then memo_pos else memo_neg) phi
  in
  let memo_add pos phi r =
    Memo.replace (if pos then memo_pos else memo_neg) phi r
  in
  let name block =
    let ys =
      Set.to_list
      @@ Set.filter (Formula.term_sort_env_of block) ~f:(fun (x, _) ->
          not (unknown_tvar x))
    in
    let distinct =
      not
        (List.contains_dup ys ~compare:(fun (x, _) (y, _) ->
             Ident.tvar_compare x y))
    in
    let foreign =
      List.exists ys ~f:(fun (x, _) -> universal x)
      || Set.exists (Formula.pvs_of block) ~f:(fun p ->
          universal (Ident.pvar_to_tvar p))
    in
    if (not distinct) || foreign then block
    else
      let name = fresh () in
      Hash_set.add fresh_names (Ident.Tvar name);
      let sorts = List.map ys ~f:snd in
      let app =
        Formula.mk_atom
        @@ Atom.mk_pvar_app (Ident.Pvar name) sorts (Term.of_sort_env ys)
      in
      added :=
        ( Ident.Tvar name,
          Sort.mk_fun (sorts @ [ T_bool.SBool ]),
          Formula.mk_forall_if_bounded ys (Formula.mk_imply block app) )
        :: !added;
      app
  in
  let rec walk pos phi =
    match memo_find pos phi with
    | Some r -> r
    | None ->
        let r =
          match phi with
          | Formula.Atom _ | Formula.LetRec _ -> phi
          | Formula.BinaryOp ((Formula.Iff | Formula.Xor), _, _, _) -> phi
          | Formula.Bind (Formula.Random _, _, _, _) -> phi
          | Formula.UnaryOp (op, a, info) ->
              let a' = walk (not pos) a in
              if phys_equal a a' then phi else Formula.mk_unop ~info op a'
          | Formula.BinaryOp (op, a, b, info) ->
              let a' =
                walk
                  (match op with Formula.Imply -> not pos | _ -> pos)
                  a
              in
              let b' = walk pos b in
              if phys_equal a a' && phys_equal b b' then phi
              else Formula.mk_binop ~info op a' b'
          | Formula.Bind (binder, senv, body, info) ->
              let body' = walk pos body in
              let block =
                if phys_equal body body' then phi
                else Formula.mk_bind ~info binder senv body'
              in
              if
                (not pos)
                && Stdlib.(binder = Formula.Forall)
                && mentions block && multiplies true body'
              then name block
              else block
          | Formula.LetFormula (x, sort, def, body, info) ->
              let body' = walk pos body in
              if phys_equal body body' then phi
              else Formula.mk_let_formula ~info x sort def body'
        in
        memo_add pos phi r;
        r
  in
  let phis = List.map phis ~f:(walk true) in
  let added = List.rev !added in
  let names = List.map added ~f:(fun (x, _, _) -> x) in
  let envs =
    List.fold added ~init:envs ~f:(fun (envs : SMT.Problem.envs) (x, sort, _) ->
        {
          envs with
          exi_senv = Map.Poly.add_exn envs.exi_senv ~key:x ~data:sort;
          kind_map = Map.Poly.add_exn envs.kind_map ~key:x ~data:Ast.Kind.Ord;
          dep_map = Map.Poly.add_exn envs.dep_map ~key:x ~data:[];
        })
  in
  (phis @ List.map added ~f:(fun (_, _, def) -> def), envs, names)

(** the problem of an SMT-LIB2 file; with [define_true], the named unknowns
    are read as defined to be [true] ([define_true] above), and their names
    are recorded in [defined_true]; with [define_true_witness_causing], so are
    the unknowns [witness_causing_unknowns] reports, beside the named ones; with
    [define_true_all], so is every unknown the file declares (the targets are
    still only the Boolean-valued unknowns of the ordinary kind) *)
(* The last reading of a file by [from_smt2_file] that applied none of its optional
   transformations (no unknown defined as [true] or by a lower bound, no relaxation, the
   synthesis reading, empty initial environments), with the reader's four process-wide
   switches it was read under.  [None] after any other reading, and while a reading is in
   progress or after one that raised.

   Contract: when this is [Some r], the problem the last such call returned is the one a new
   call [from_smt2_file ~inline:r.inline ~skolem_pred:r.skolem_pred r.file] with the switches as
   recorded would return, up to the fresh names it draws -- provided the file has not changed,
   which a caller re-reading for its switches assumes as well.  A caller that would re-read the
   input only to apply the switches can then keep the problem it has. *)
type plain_read = {
  file : string;
  inline : bool;
  skolem_pred : bool;
  law_reaches_dependents : bool;
  law_dedup_premises : bool;
  onepoint_constructor_binders : bool;
  name_quantified_premises : bool;
  premise_witness_disjuncts : bool;
}

let last_plain_read : plain_read option ref = ref None

(* Whether a reading records, in [last_relaxable], which unknowns the lower-bound relaxation
   would relax in it.  Off by default (the record costs a walk of the assertions in negation
   normal form); process-wide, set before the readings it should cover. *)
let record_relaxable = ref false

type relaxable = {
  file : string;
  switches : bool * bool * bool * bool * bool;
      (** [law_reaches_dependents], [law_dedup_premises], [onepoint_constructor_binders],
          [name_quantified_premises] and [SMT.Smtlib2.premise_witness_disjuncts] at the
          reading's start *)
  defined : string list;  (** the unknowns the reading defined as [true], sorted *)
  targets : string list;
      (** the witness-causing unknowns of the assertions as read with [defined] defined that
          [define_true_targets] keeps (Boolean-valued, ordinary kind): exactly the names
          [lower_bound_relax] starts from when nothing else is named *)
}

(* the record of the last reading made with [record_relaxable] set, taken after its
   [true]-definitions and before any relaxation or premise naming *)
let last_relaxable : relaxable option ref = ref None

(* [relaxable_known ~file ~defined ~switches] is [Some targets] when the last recorded reading
   read [file] under [switches] with exactly [defined] defined as [true] (in any order): a
   reading of [file] that defines [defined] (a [define_true_names] reading, before its
   relaxation) builds the same assertions and environments, since both apply the same
   [define_true_sexps] to the same s-expressions under the same reader switches, so its
   witness-causing targets are [targets]; [None] otherwise *)
let relaxable_known ~file ~defined ~switches =
  match !last_relaxable with
  | Some r
    when String.equal r.file file
         && Stdlib.( = ) r.switches switches
         && List.equal String.equal r.defined
              (List.dedup_and_sort ~compare:String.compare defined) ->
      Some r.targets
  | _ -> None

(* the reader switches [relaxable] keys a record by, as they stand now *)
let relaxable_switches () =
  ( !SMT.Smtlib2.law_reaches_dependents,
    !SMT.Smtlib2.law_dedup_premises,
    !Problem.onepoint_constructor_binders,
    !name_quantified_premises,
    !SMT.Smtlib2.premise_witness_disjuncts )

(* Whether a plain reading (as [last_plain_read] records one) also keeps its assertions as read,
   for [forced_true_of_last_read].  Off by default: the assertions are as large as the problem,
   and keeping them is only worth it for a caller that will ask that question once and drop them.
   Process-wide, set before the reading. *)
let keep_plain_assertions = ref false

(* the file, assertions and environments of the last plain reading, when [keep_plain_assertions]
   asked for them; cleared by every reading and by [forced_true_of_last_read] *)
let last_plain_assertions = ref None

(* [forced_true_of_last_read ~file ~valid]: the unknowns a reading of [file] with
   [~define_forced_true:valid] would define as [true] -- [define_true_targets] of
   [forced_true_unknowns ~valid] over the assertions of the last plain reading, which are the
   ones that reading starts from -- or [None] when no such assertions are kept for [file].  The
   kept assertions are dropped either way.  A caller that would re-read the input only to learn
   that list, and discard the reading when it is empty, can ask this first. *)
(* The assertions and environments a problem was made from, with the unknowns defined as [true]
   before it was made, kept for the least-definition probe so that it need not read the input
   again.  The probe's reading reads the input, defines as [true] the unknowns it is given and
   the [unguarded_witness_unknowns] of the plain reading's assertions (both filtered by
   [define_true_targets]), and then replaces the witness-causing unknowns by their lower bounds.
   When the first of those three steps would define exactly [defined], its assertions are
   [phis] (the same reading of the same input, up to fresh names), and the probe's problem is
   [least_definition_problem] of them.

   Contract: [Some b] only when [keep_least_definition_base] was set, and only after
   - a plain reading of [b.file] whose kept assertions [forced_true_of_last_read] found to define
     nothing and to have no unguarded witness target; then [b.defined = []] and [b.phis],
     [b.envs] are that reading's; or
   - a [define_true_known] reading of [b.file] whose known list contains every unguarded witness
     target [forced_true_of_last_read] found in the plain reading before it; then [b.defined] is
     that list and [b.phis], [b.envs] are the reading's own.
   Cleared at the start of every reading.  The assertions are as large as the problem: a caller
   that sets the switch clears this as soon as the probe has taken it. *)
type least_definition_base = {
  file : string;
  defined : Ident.tvar list;
  phis : Ast.LogicOld.Formula.t list;
  envs : SMT.Problem.envs;
}

let keep_least_definition_base = ref false
let least_definition_base : least_definition_base option ref = ref None

(* the unguarded witness targets of the plain reading [forced_true_of_last_read] last examined,
   with its file, for the [define_true_known] reading that follows it *)
let unguarded_of_last_read : (string * Ident.tvar list) option ref = ref None

let forced_true_of_last_read ~file ~valid =
  let kept = !last_plain_assertions in
  last_plain_assertions := None;
  unguarded_of_last_read := None;
  match kept with
  | Some (f, phis, envs) when String.(f = file) ->
      let known =
        Map.Poly.keys
          (define_true_targets (forced_true_unknowns ~valid phis envs) envs)
      in
      (if !keep_least_definition_base then
         let unguarded =
           Map.Poly.keys
             (define_true_targets (unguarded_witness_unknowns phis envs) envs)
         in
         if List.is_empty known && List.is_empty unguarded then
           least_definition_base :=
             Some { file = f; defined = []; phis; envs }
         else unguarded_of_last_read := Some (f, unguarded));
      Some known
  | _ -> None

(* [least_definition_problem ~print ~rounds ~lower_bound_defined phis envs]: the problem of
   [phis] with their witness-causing unknowns replaced by their lower bounds
   ([lower_bound_define]), the replaced unknowns and their definitions recorded in
   [lower_bound_defined] -- the last steps of a reading with
   [~define_lower_bound_witness_causing:true], after its unknowns were defined as [true].  Sets
   the record of the input assertions to the result's, as that reading does. *)
let least_definition_problem ?(print = fun _ -> ()) ~rounds ~lower_bound_defined phis envs =
  let phis, envs, defs =
    lower_bound_define ~print ~rounds (witness_causing_unknowns phis envs) phis envs
  in
  lower_bound_defined := defs;
  Ast.LogicOld.set_input_assertions phis;
  Problem.make ~skolem_pred:true phis envs

let from_smt2_file ~print ~inline ?(skolem_pred = false) ?(define_true_names = [])
    ?(define_true_witness_causing = false) ?(define_true_all = false)
    ?(defined_true = ref [])
    ?(define_forced_true : (Ast.LogicOld.Formula.t -> bool) option)
    ?(define_true_known : Ident.tvar list option)
    ?(lower_bound_names = []) ?(lower_bound_witness_causing = false)
    ?(lower_bound_rounds = 2) ?(relaxed = ref []) ?(lower_bounds = ref [])
    ?(define_lower_bound_witness_causing = false)
    ?(define_lower_bound_rounds = 3) ?(lower_bound_defined = ref [])
    ?(define_upper_bound : (int * (Ast.LogicOld.Formula.t -> bool)) option)
    ?(upper_bound_defined = ref []) ?(upper_bound_count = ref 0)
    ?(upper_bounds = ref [])
    ?(decl_reading = SMT.Problem.Synthesize)
    ?(uni_sort = Set.Poly.empty)
    ?(uni_senv = Map.Poly.empty) ?(exi_senv = Map.Poly.empty)
    ?(dep_map = Map.Poly.empty) ?(kind_map = Map.Poly.empty)
    ?(fenv = Map.Poly.empty) ?(dtenv = Map.Poly.empty)
    ?(opaque_definitions : (opaque_selection * string list ref) option)
    filename =
  let plain =
    Option.is_none opaque_definitions
    && List.is_empty define_true_names
    && (not define_true_witness_causing)
    && (not define_true_all)
    && Option.is_none define_forced_true
    && Option.is_none define_true_known
    && List.is_empty lower_bound_names
    && (not lower_bound_witness_causing)
    && (not define_lower_bound_witness_causing)
    && Option.is_none define_upper_bound
    && Stdlib.(decl_reading = SMT.Problem.Synthesize)
    && Set.is_empty uni_sort && Map.is_empty uni_senv && Map.is_empty exi_senv
    && Map.is_empty dep_map && Map.is_empty kind_map && Map.is_empty fenv
    && Map.is_empty dtenv
  in
  last_plain_read := None;
  last_plain_assertions := None;
  least_definition_base := None;
  let switches_at_start =
    ( !SMT.Smtlib2.law_reaches_dependents,
      !SMT.Smtlib2.law_dedup_premises,
      !Problem.onepoint_constructor_binders )
  in
  let name_premises_at_start = !name_quantified_premises in
  let witness_premises_at_start = !SMT.Smtlib2.premise_witness_disjuncts in
  let relaxable_switches_at_start = relaxable_switches () in
  last_relaxable := None;
  let record_relaxable_now phis envs defined =
    if !record_relaxable then
      last_relaxable :=
        Some
          {
            file = filename;
            switches = relaxable_switches_at_start;
            defined =
              List.dedup_and_sort ~compare:String.compare
                (List.map defined ~f:Ident.name_of_tvar);
            targets =
              List.map ~f:Ident.name_of_tvar
              @@ Map.Poly.keys
                   (define_true_targets (witness_causing_unknowns phis envs) envs);
          }
  in
  let sexps =
    Common.PhaseTime.with_phase "parse" @@ fun () ->
    In_channel.with_file filename ~f:(fun ic ->
        let lexbuf = Lexing.from_channel ic in
        Lexing.set_filename lexbuf filename;
        try SMT.Parser.program SMT.Lexer.token lexbuf
        with e ->
          LexingHelper.print_error_information lexbuf;
          raise e)
  in
  SMT.Smtlib2.warn_if_several_checks ~filename sexps;
  (* [opaque_definitions = Some (selection, made)]: the selected eligible
     definitions read as universal functions ([opaque_definitions_sexps]),
     their names recorded in [made]; only a [sat] of such a reading may be
     read as one of the input *)
  let sexps =
    match opaque_definitions with
    | None -> sexps
    | Some (selection, made) ->
        let sexps, names = opaque_definitions_sexps ~selection sexps in
        made := names;
        sexps
  in
  let read sexps =
    let phis, envs =
      Common.PhaseTime.with_phase "toplevel" @@ fun () ->
      SMT.Smtlib2.toplevel ~print ~inline []
        {
          decl_reading;
          lifted_universals = Map.Poly.empty;
          candidates = Map.Poly.empty;
          uni_sort;
          uni_senv;
          exi_senv;
          dep_map;
          kind_map;
          fenv;
          dtenv;
        }
        sexps
    in
    ( Common.PhaseTime.with_phase "typeinf" @@ fun () ->
      Typeinf.typeinf ~print
        ~rigid:(SMT.Smtlib2.rigid_of envs.uni_sort)
          (* A sort the inference cannot resolve becomes [Int], silently.
           The alternative -- [None], i.e. leave it unresolved and let the
           caller fail -- is written and switched off.  Elsewhere in this
           code base the opposite decision was taken for the same situation
           (the assumed bit-vector width): when the input carries no
           information, make the default a setting the user sees
           ([--bv-default]) rather than a guess.  Nothing reports the guess
           here, so a `.clp`/`.smt2` file whose sort really is not integer is
           solved as if it were. *)
        ~default:(if false then None else Some Ast.LogicOld.T_int.SInt (*ToDo*))
        ~to_sus:true phis,
      envs )
  in
  let read_started = Common.Clock.now_s () in
  let read_stage name =
    !stage_trace
      (sprintf "[read] %s at %.2f s" name
         (Common.Clock.now_s () -. read_started))
  in
  (* [name_quantified_premises]: the last step before [Problem.make], so that every other
     transformation reads the premises as written *)
  let name_premises phis envs =
    if not name_premises_at_start then (phis, envs)
    else
      let phis, envs, names = premise_definitions phis envs in
      add_premise_names (Set.Poly.of_list names);
      read_stage
        (sprintf "%d quantified premise(s) named" (List.length names));
      (phis, envs)
  in
  (* [define_true_known]: the unknowns to define as [true] are already known -- the
     [define_true_targets] of a plain reading of this file under the same switches (as
     [forced_true_of_last_read] gives them) -- so the input is read once, with them defined, and
     not first read to find them; the other optional transformations are not combined with it *)
  match define_true_known with
  | Some (_ :: _ as known) ->
      let phis, envs =
        read (define_true_sexps (List.map known ~f:Ident.name_of_tvar) sexps)
      in
      read_stage "assertions read, known unknowns defined";
      defined_true := known;
      record_relaxable_now phis envs known;
      (* a base kept for the least-definition probe holds the assertions before premise naming,
         which the probe's own steps do not apply, so none is kept while naming is on *)
      (if !keep_least_definition_base && not name_premises_at_start then
         match !unguarded_of_last_read with
         | Some (f, unguarded)
           when String.(f = filename)
                && List.for_all unguarded ~f:(fun x ->
                       List.mem known x ~equal:Ident.tvar_equal) ->
             least_definition_base :=
               Some { file = filename; defined = known; phis; envs }
         | _ -> ());
      unguarded_of_last_read := None;
      let phis, envs = name_premises phis envs in
      Ast.LogicOld.set_input_assertions phis;
      let pcsp = Problem.make ~skolem_pred phis envs in
      read_stage "problem made";
      pcsp
  | Some [] | None ->
  let phis, envs = read sexps in
  read_stage "assertions read";
  if plain && !keep_plain_assertions then
    last_plain_assertions := Some (filename, phis, envs);
  let define_true_names =
    if not define_true_witness_causing then define_true_names
    else define_true_names @ witness_causing_unknowns phis envs
  in
  let define_true_names =
    if not define_true_all then define_true_names
    else
      define_true_names
      @ List.map (Map.Poly.keys envs.exi_senv) ~f:Ident.name_of_tvar
  in
  (* [define_lower_bound_witness_causing] reads a closure's precondition,
     assumed by an unguarded universal, as [true] before the lower bounds of
     the remaining witness-causing unknowns are taken *)
  let define_true_names =
    if not define_lower_bound_witness_causing then define_true_names
    else define_true_names @ unguarded_witness_unknowns phis envs
  in
  let define_true_names =
    match define_forced_true with
    | None -> define_true_names
    | Some valid -> define_true_names @ forced_true_unknowns ~valid phis envs
  in
  (* the named unknowns are replaced by reading the input again with each
     declared as [true] ([define_true_sexps]) *)
  let phis, envs, replaced =
    if List.is_empty define_true_names then (phis, envs, [])
    else
      let replaced =
        Map.Poly.keys (define_true_targets define_true_names envs)
      in
      if List.is_empty replaced then (phis, envs, [])
      else
        let phis, envs =
          read
            (define_true_sexps
               (List.map replaced ~f:Ident.name_of_tvar)
               sexps)
        in
        (phis, envs, replaced)
  in
  defined_true := replaced;
  (* the record is about the assertions a lower-bound reading starts its relaxation from; a
     reading that changes them otherwise first records nothing *)
  if not define_lower_bound_witness_causing then record_relaxable_now phis envs replaced;
  (* [define_lower_bound_witness_causing]: the unknowns that make the reader
     skolemise a quantifier are replaced at every occurrence by their lower
     bounds ([lower_bound_define]): one choice of them, of which only a [sat]
     may be read *)
  let phis, envs =
    if not define_lower_bound_witness_causing then (phis, envs)
    else
      let phis, envs, defs =
        lower_bound_define ~print ~rounds:define_lower_bound_rounds
          (witness_causing_unknowns phis envs)
          phis envs
      in
      lower_bound_defined := defs;
      (phis, envs)
  in
  (* [define_upper_bound = Some (k, refuted)]: the witness-causing unknowns
     replaced at every occurrence by their [k]-th candidate of
     [upper_bound_candidates] (none replaced when a target has fewer); one
     choice of them, of which only a [sat] may be read.  [upper_bound_count]
     is the largest number of candidates a target has, so a caller knows
     which [k] to try, and [upper_bounds] each target's upper bound *)
  let phis, envs =
    match define_upper_bound with
    | None -> (phis, envs)
    | Some (k, refuted) ->
        let cands =
          upper_bound_candidates ~print ~refuted
            (witness_causing_unknowns phis envs)
            phis envs
        in
        upper_bounds := List.map cands ~f:(fun (x, u, _) -> (x, u));
        upper_bound_count :=
          List.fold cands ~init:0 ~f:(fun m (_, _, ds) ->
              max m (List.length ds));
        let defs =
          List.filter_map cands ~f:(fun (x, _, ds) ->
              Option.map (List.nth ds k) ~f:(fun d -> (x, d)))
        in
        upper_bound_defined := defs;
        if List.is_empty defs then (phis, envs)
        else define_formulas defs phis envs
  in
  (* the named unknowns are replaced by their lower bounds where they are
     assumed and by [true] where they are demanded ([lower_bound_relax]): a
     relaxation, of which only an [unsat] may be read *)
  let phis, envs =
    if List.is_empty lower_bound_names && not lower_bound_witness_causing then
      (phis, envs)
    else
      let names =
        lower_bound_names
        @
        if lower_bound_witness_causing then witness_causing_unknowns phis envs
        else []
      in
      read_stage "witness-causing unknowns selected";
      let phis, envs, names, bounds =
        lower_bound_relax ~print ~rounds:lower_bound_rounds names phis envs
      in
      relaxed := names;
      lower_bounds := bounds;
      (phis, envs)
  in
  read_stage "relaxations done";
  let phis, envs = name_premises phis envs in
  Ast.LogicOld.set_input_assertions phis;
  let pcsp =
    Common.PhaseTime.with_phase "make" (fun () ->
        Problem.make ~skolem_pred phis envs)
  in
  read_stage "problem made";
  (let reach, dedup, onepoint = switches_at_start in
   if plain then
     last_plain_read :=
       Some
         {
           file = filename;
           inline;
           skolem_pred;
           law_reaches_dependents = reach;
           law_dedup_premises = dedup;
           onepoint_constructor_binders = onepoint;
           name_quantified_premises = name_premises_at_start;
           premise_witness_disjuncts = witness_premises_at_start;
         });
  pcsp

let from_gzipped_smt2_file ~print ~inline ?(skolem_pred = false)
    ?(decl_reading = SMT.Problem.Synthesize) ?(uni_sort = Set.Poly.empty)
    ?(uni_senv = Map.Poly.empty) ?(exi_senv = Map.Poly.empty)
    ?(dep_map = Map.Poly.empty) ?(kind_map = Map.Poly.empty)
    ?(fenv = Map.Poly.empty) ?(dtenv = Map.Poly.empty) filename =
  let sexps =
    In_channel.with_file ~binary:true filename ~f:(fun raw ->
        let ic = Gzip.open_in_chan raw in
        Exn.protect ~finally:(fun () -> Gzip.dispose ic) ~f:(fun () ->
            let lexbuf =
              Lexing.from_function (fun b len -> Gzip.input ic b 0 len)
            in
            Lexing.set_filename lexbuf filename;
            try SMT.Parser.program SMT.Lexer.token lexbuf
            with e ->
              LexingHelper.print_error_information lexbuf;
              raise e))
  in
  SMT.Smtlib2.warn_if_several_checks ~filename sexps;
  let phis, envs =
    SMT.Smtlib2.toplevel ~print ~inline []
      {
        decl_reading;
        lifted_universals = Map.Poly.empty;
        candidates = Map.Poly.empty;
        uni_sort;
        uni_senv;
        exi_senv;
        dep_map;
        kind_map;
        fenv;
        dtenv;
      }
      sexps
  in
  let phis =
    Typeinf.typeinf
      ~print
      ~rigid:(SMT.Smtlib2.rigid_of envs.uni_sort)
        (* A sort the inference cannot resolve becomes [Int], silently.  The
         alternative -- [None], i.e. leave it unresolved and let the caller
         fail -- is written and switched off.  Elsewhere in this code base the
         opposite decision was taken for the same situation (the assumed
         bit-vector width): when the input carries no information, make the
         default a
         setting the user sees ([--bv-default]) rather than a guess.  Nothing
         reports the guess here, so a `.clp`/`.smt2` file whose sort really is
         not integer is solved as if it were. *)
      ~default:(if false then None else Some Ast.LogicOld.T_int.SInt (*ToDo*))
      ~to_sus:true phis
  in
  Problem.make ~skolem_pred phis envs

let from_clp_file ~print filename =
  let res =
    In_channel.with_file filename ~f:(fun ic ->
        let lexbuf = Lexing.from_channel ic in
        Lexing.set_filename lexbuf filename;
        try LPParser.parser_main_logic_program LPLexer.token lexbuf
        with e ->
          LexingHelper.print_error_information lexbuf;
          raise e)
  in
  let phis =
    List.map res ~f:(fun (head, body) -> LogicOld.Formula.mk_imply body head)
  in
  let params =
    let psenv =
      Set.Poly.union_list @@ List.map phis ~f:LogicOld.Formula.pred_sort_env_of
    in
    let kind_map =
      (* ToDo *)
      let fnpvs =
        Set.Poly.filter_map psenv ~f:(fun (Ident.Pvar n, _) ->
            if String.is_prefix ~prefix:"FN_" n then Some (Ident.Tvar n)
            else None)
      in
      let wfpvs =
        Set.Poly.filter_map psenv ~f:(fun (Ident.Pvar n, _) ->
            if String.is_prefix ~prefix:"WF_" n then Some (Ident.Tvar n)
            else None)
      in
      Map.Poly.empty
      |> Kind.add_kinds fnpvs Kind.FN
      |> Kind.add_kinds wfpvs Kind.WF
    in
    try
      Params.make ~kind_map @@ of_old_sort_env_map @@ Map.of_set_exn
      @@ LogicOld.Term.pred_to_sort_env psenv
    with exn_ when not (Common.Timer.is_async exn_) ->
      print
      @@ lazy
           (sprintf "pred sort env:\n%s"
           @@ LogicOld.str_of_pred_sort_env_set LogicOld.Term.str_of_sort psenv
           );
      failwith
        "The sort of a predicate variable is defined multiple times in the \
         environment, causing a conflict."
  in
  (*Problem.normalize @@*)
  Problem.of_formulas ~params
  @@ Set.Poly.of_list
  @@ List.rev_map phis ~f:(fun phi ->
      ( Map.of_set_exn @@ Logic.of_old_sort_env_set
        @@ LogicOld.Formula.term_sort_env_of phi,
        ExtTerm.of_old_formula phi ))

(* A known solution for some of a problem's unknowns, written as SMT-LIB2
   [define-fun]s in the scope of the problem's own declarations, so that a
   definition can use the problem's datatypes, quantified sorts, arrays,
   sequences and quantifiers -- none of which the SyGuS solution reader takes.

   The oracle file is read after the problem file's commands with every
   assertion and query removed, so each definition is parsed exactly as a
   [define-fun] of the problem itself would be. Each definition's parameters
   are returned as written: the caller is responsible for their order matching
   the unknown's (for an unknown declared with [declare-dep-exists-fun], its
   universals come first, in the order of their names, then its arguments).
   Nothing global is written: the reader keeps every environment it builds in
   the value it returns, except a recursive definition's, which no oracle file
   has. Raises on a file holding anything but [define-fun]s. *)
let oracle_of_smt2_file ~print ~problem_file oracle_file =
  let read file =
    let ic = In_channel.create file in
    let lexbuf = Lexing.from_channel ic in
    Lexing.set_filename lexbuf file;
    Exn.protect
      ~f:(fun () -> SMT.Parser.program SMT.Lexer.token lexbuf)
      ~finally:(fun () -> In_channel.close ic)
  in
  let is_query = function
    | Sexp.List
        (Sexp.Atom
           ( "assert" | "check-sat" | "check-sat-assuming" | "check-sat-using"
           | "get-model" | "get-value" | "get-info" | "exit" )
        :: _) ->
        true
    | _ -> false
  in
  let decls = List.filter (read problem_file) ~f:(Fn.non is_query) in
  let defs = read oracle_file in
  let names =
    List.map defs ~f:(function
      | Sexp.List (Sexp.Atom "define-fun" :: Sexp.Atom name :: _) -> name
      | sexp ->
          failwith
          @@ sprintf "[oracle_of_smt2_file] %s: not a define-fun: %s"
               oracle_file (Sexp.to_string sexp))
  in
  (* each definition replaces the problem's declaration of the same unknown:
     the reader refuses a name declared and then defined, so the declaration
     is dropped rather than shadowed *)
  let declared_name = function
    | Sexp.List (Sexp.Atom cmd :: Sexp.Atom name :: _)
      when String.is_prefix cmd ~prefix:"declare-" ->
        Some name
    | Sexp.List (Sexp.Atom ("declare-totp" | "declare-uniqp") :: _ :: Sexp.Atom name :: _) ->
        Some name
    | _ -> None
  in
  let decls =
    List.filter decls ~f:(fun d ->
        match declared_name d with
        | Some name -> not (List.mem names name ~equal:String.equal)
        | None -> true)
  in
  let _, envs =
    SMT.Smtlib2.toplevel ~print ~inline:true []
      {
        decl_reading = SMT.Problem.Synthesize;
        lifted_universals = Map.Poly.empty;
        candidates = Map.Poly.empty;
        uni_sort = Set.Poly.empty;
        uni_senv = Map.Poly.empty;
        exi_senv = Map.Poly.empty;
        dep_map = Map.Poly.empty;
        kind_map = Map.Poly.empty;
        fenv = Map.Poly.empty;
        dtenv = Map.Poly.empty;
      }
      (decls @ defs)
  in
  List.map names ~f:(fun name ->
      match Map.Poly.find envs.fenv (Ident.Tvar name) with
      | Some (params, _sort, body, _, _) ->
          (Ident.Pvar name, (params, LogicOld.Formula.of_bool_term body))
      | None ->
          failwith
          @@ sprintf "[oracle_of_smt2_file] %s: %s was not defined" oracle_file
               name)
