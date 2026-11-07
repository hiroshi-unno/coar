(* Meaning-preserving simplification of a muCLP problem before it is solved.
   [f] runs, in order: optionally, the one-point rule on quantified integer
   variables ([OnePoint]); removal of redundant quantifiers and of lets; inlining of
   a predicate called exactly once, from a predicate defined before it;
   optionally, removal of argument positions whose parameters are only passed
   on to such positions; optionally, elimination of quantifiers over variables that are adjustable
   (each occurs once, so the term ranges over its whole sort and the quantifier
   can move onto the argument position); removal of predicates unreachable from
   the query; removal of predicate arguments that are the same constant at every
   call; replacement of each quantified subformula free of predicate variables
   by [true] when Z3 shows it valid, or by [false] when Z3 shows it
   unsatisfiable (an undecided query leaves it alone); and a final
   simplification and inlining.  With [enable] off only the first step runs.
   Every step must preserve validity of the query; a syntactic test used to
   license one (the adjustable variables) may miss a variable but must never
   claim one that is not. *)
open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld

module Config = struct
  (* What the erasure does with a quantified call from a predicate's body to a predicate in the
     same call-graph strongly connected component as that predicate (the origin of a predicate
     the erasure created standing for it).  Erasing such a call adds the fresh predicate to the
     recursion, and the fixpoint-to-pfwCSP reduction then threads copies of the members'
     arguments through each indirectly recursive member and adds a well-foundedness unknown per
     member. *)
  type same_scc_calls =
    | Erase_same_scc  (** erase such calls like any other *)
    | Keep_same_scc  (** leave every such call quantified *)
    | Keep_same_scc_if_grows
        (** leave such calls quantified only in the strongly connected components the erasure
            would grow.  The erasure is first run erasing them; a component of the original
            call graph grows when, in the problem that run produces, two predicates standing
            for one original predicate (the original itself, or a predicate the erasure made
            from it) lie in one strongly connected component of the call graph restricted to
            what the query reaches.  Then the original is still called beside its fresh copy,
            and the reduction pays for the extra member.  Where every original predicate has at
            most one representative in each component (a fresh predicate that replaces its
            original in the recursion, the original left unreachable or outside the cycle),
            the first run's result is kept.  Otherwise the erasure runs again, declining only
            the same-component calls of a grown component. *)
    | Keep_same_scc_if_grows_or_splits
        (** as [Keep_same_scc_if_grows], and also leave such calls quantified in an original
            component the erasure splits: one whose predicates have representatives in two
            or more distinct recursive strongly connected components of the erased problem
            (restricted to what the query reaches).  Then the original cycle survives beside
            a recursive fresh copy of it, so the reduction gets two recursions, each with its
            own well-foundedness unknown, where the original had one.  A fresh predicate that
            replaces its original in the recursion (the original left non-recursive or
            unreachable) splits nothing and keeps its erasure. *)
  [@@deriving yojson]

  (* What body a predicate made by the erasure gets.  A made predicate [P'] stands for the
     projection [Q w. P(w, s)] of its source [P] onto the source's unflagged positions.
     Both choices denote that projection in the problem's solution; they differ in how the
     body is built, and only the second is the construction whose correctness is argued
     from the factorisation of a fixpoint block (a block whose made members' bodies are
     projections of their sources' bodies, so that the block's operator factors through the
     projection map, and the rolling rule carries the extremal fixpoint over, whatever the
     fixpoint sign and binder). *)
  type made_bodies =
    | Copy_and_erase
        (** copy the source's body as it is when the predicate is made (the original body
            when the source has not been erased yet), bind the flagged parameters, and erase
            the copy again like any other body, which can fold occurrences of the copy into
            further made predicates *)
    | Project_final
        (** after every original body and the query have been erased, give each made
            predicate the source's final (erased) body under the binder of the flagged
            parameters, and do not erase it again.  No erasure then fires inside a made
            body, so the sources are original predicates and every made body is exactly
            the one-level projection of its source's final body. *)
    | Hybrid
        (** [Copy_and_erase], except on the blocks (an original with the predicates made
            from it) that a structural coverage test does not accept, which are built as
            under [Project_final] instead; the run is repeated with those blocks projected
            until every block is accepted or projected.  A block is accepted when every
            predicate that an erasure of one of its made bodies (or of the unerased source
            body such a body copied) folded an occurrence into lies in an outer block or in
            a robustly consistent inner one; or when it is a least fixpoint whose made
            predicates all bind existentially, or a greatest one whose made predicates all
            bind universally.  On such a block the copied-and-erased bodies have the
            projections of the original solution as their solution; a projected block has
            them by construction.  The test reads only the erasure's own record of its
            folds, the binders, the signs and the order, and asks no solver. *)
    | Hybrid_miniscoped
        (** [Hybrid], with each projected body miniscoped: the binder block of the flagged
            parameters is pushed inwards, as a block, over the connectives it distributes
            over (a universal over a conjunction and past the disjuncts that mention none of
            its variables, an existential dually, and past a binder of the same kind), and a
            bound variable that does not occur is dropped.  Each step is a first-order
            equivalence valid in every structure with nonempty sorts, so a projected body
            stays equivalent to the one-level projection for every interpretation of the
            predicates, and the block keeps the projection map's factorisation.  It gives
            back the shape the default's re-erasure reaches where that re-erasure only moved
            the binder inwards; a projected body with its binder on top hands a strategy
            check a quantifier over the whole body. *)
  [@@deriving yojson]

  (* Whether quantifiers over adjustable variables are erased (each occurs once, so the term
     ranges over its whole sort and the quantifier can move onto the argument position), and
     which erasures the optional rules decline.  A declined erasure leaves the quantifier in
     place, which preserves the query's validity whatever the rules decide. *)
  type quantifier_erasure =
    | No_erasure
    | Erase of {
        keep_query_binder : bool; [@default true]
            (** leave a quantifier block the query reaches from its root through
                conjunctions only.  Such a universal is already a clause variable of the
                primal problem (and an existential one is skolemised alike either way), so
                erasing it only adds a nullary predicate whose body is the callee unfolded
                once, which pins the callee's solution less. *)
        same_scc_calls : same_scc_calls; [@default Erase_same_scc]
        made_bodies : made_bodies; [@default Copy_and_erase]
      }
  [@@deriving yojson]

  (* Which cycle pass-through predicates the inlining also removes.  A predicate is a cycle
     pass-through when it lies on a cycle of the call graph, does not call itself, is not
     mentioned by the query, and is called only from the bodies of predicates listed before
     it (however many times); each occurrence is replaced by its body and its equation is
     dropped.  Exact for any signs and any nesting: a later equation holds as an identity of
     functions of the earlier variables, so substituting its right-hand side for its
     occurrences in an earlier equation's body leaves that equation's operator, and hence
     every fixpoint, unchanged.  It turns a cycle through such a predicate into a self-call of
     the predicate before it, so a loop whose guard sits on one call edge and whose update on
     the next becomes one edge carrying both.  The parity progress measure checks a ranking on
     every call edge of a component separately; on the split form a strict decrease made
     where the update is has no guard bounding it, so the ranking needs an invariant or a
     piecewise form, and the fused edge needs neither.  Each occurrence receives a copy of the
     body, so along a chain of such predicates the size grows as the product of their
     occurrence counts. *)
  type cycle_passthrough =
    | No_passthrough  (** only the predicates called exactly once are inlined *)
    | Fix_passthrough
        (** also the cycle pass-through predicates whose sign is [fix], the sign a producer
            gives a predicate it knows every cycle through which passes a least or greatest
            one (the transition-system translation gives it to a location that is not a cut
            point) *)
    | Fix_passthrough_unquantified
        (** [Fix_passthrough], except a predicate the quantifier erasure makes a
            quantified copy of (in an erasure of the problem without this inlining
            that takes every same-component erasure) is not inlined as a
            pass-through.  Such a copy is how a nondeterministic assignment at that
            location reaches the solver; inlining the predicate moves the quantifier
            into its caller's body, inside the loop.  A quantifier the erasure
            removes (an assignment written as a quantified equation, a havoc
            nothing reads) withholds nothing.  Still exact: it only inlines fewer
            predicates than [Fix_passthrough]. *)
    | Fix_passthrough_once_per_body
        (** [Fix_passthrough], except a predicate that occurs more than once in
            one body (or in the query) is not inlined as a pass-through.  Such a
            predicate is a location its caller reaches along several
            transitions; inlining it puts one copy of its body, with its own
            guard, under each of them, so every one of the caller's edges
            becomes a two-step edge, which a strategy-based solver must then
            read a choice through.  A predicate occurring once in each of
            several bodies (a loop head and a quantified copy of it) is still
            inlined: each body receives one copy.  Exact: it only inlines fewer
            predicates than [Fix_passthrough]. *)
    | Any_passthrough  (** also every cycle pass-through predicate, whatever its sign *)
  [@@deriving yojson]

  type t = {
    enable : bool; [@default true]
    quantifier_erasure : quantifier_erasure;
        [@default
          Erase
            {
              keep_query_binder = true;
              same_scc_calls = Keep_same_scc_if_grows;
              made_bodies = Hybrid;
            }]
        (** the erasure every MuVal and MuValPPM entry configuration runs; a
            configuration that runs without it states [No_erasure] *)
    elim_irrelevant_args : bool; [@default true]
        (** before the quantifier erasure, remove every argument position of a predicate
            whose parameter is read only to be passed on to such positions (a variable a
            loop havocs and nothing reads, a value only carried along), and the
            quantifiers left vacuous by it.  Exact for least and greatest fixpoints: the
            interpretations that ignore those positions form a complete sublattice the
            body operator preserves.  On by default because it is exact; without it the
            erasure removes a quantifier over such a havocked variable by unfolding the
            recursion that carries it, which copies an enclosing loop into a second
            component beside the original. *)
    inline_cycle_passthrough : cycle_passthrough;
        [@default Fix_passthrough_unquantified]
        (** [Fix_passthrough_unquantified] by default: exact, and it reaches only the
            predicates a frontend marks [fix], so a hand-written system is left as
            written; a head carrying a nondeterministic choice stays a predicate of its
            own, since moving the choice's quantifier into the loop it closes cost
            answers that the split form gives *)
    one_point_quantifiers : bool; [@default false]
        (** first of all steps, remove each quantified integer variable a body fixes by
            the one-point rule: [forall x. x <> e \/ phi] becomes [phi[e/x]] and
            [exists x. x = e /\ phi] becomes [phi[e/x]], for a disjunct (conjunct) that
            is an integer (dis)equation in which [x] has coefficient 1 or -1 and [e] is
            free of [x].  An equivalence of the body at every interpretation of the
            predicate variables, so exact for every fixpoint.  The transition-system
            translation writes each deterministic update of a variable as such a
            quantifier, which a strategy-based solver otherwise reads as an opponent's
            decision it must Skolemise and refine.  Off by default since it changes the
            questions every later step and solver is asked *)
    verbose : bool; [@default false]
  }
  [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  include MakeExtFile (struct
    type nonrec t = t

    let of_yojson = of_yojson
    let to_yojson = to_yojson
    let name = "Optimizer"

    (* a leaf: no nested config to load *)
    let instantiate = Or_error.return
  end)
end

module type OptimizerType = sig
  val f :
    ?id:int option ->
    ?elim_forall:bool ->
    ?elim_exists:bool ->
    ?elim_pvar_args:bool ->
    ?erased_constants:(Ident.pvar * Ident.tvar * Term.t) list ref ->
    Problem.t ->
    Problem.t
  (** [f muclp] is the optimized problem, whose query is valid iff [muclp]'s is.
      With [erased_constants], every argument position the constant-argument
      step removes is added to it as [(predicate, parameter, constant)] (see
      [EraseConstVariables]); nothing else about the run changes. *)
end

(* the configuration's types, under a name the functor's parameter does not shadow *)
module Opt = Config

module Make (Config : Config.ConfigType) = struct
  let config = Config.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  module EraseUnreachedPredicates : sig
    val optimize : Problem.t -> Problem.t
  end = struct
    (* 0: query, n: n-th pvar from toplevel *)
    let pvargraph_of_muclp muclp =
      let pvar_to_id = Hashtbl.Poly.create ~size:1234 () in
      (* initialize pvar_to_id *)
      List.iteri muclp.Problem.preds ~f:(fun i pred ->
          if false then
            Debug.print @@ lazy ("adding: " ^ Ident.name_of_pvar @@ pred.name);
          Hashtbl.Poly.set pvar_to_id ~key:pred.name ~data:(i + 1));
      muclp.Problem.query
      :: List.map ~f:(fun pred -> pred.body) muclp.Problem.preds
      |> List.map
           ~f:
             (Formula.pvs_of
             >> Set.Poly.map ~f:(fun pvar ->
                 try Hashtbl.Poly.find_exn pvar_to_id pvar
                 with exn_ when not (Common.Timer.is_async exn_) ->
                   failwith @@ "not found: " ^ Ident.name_of_pvar pvar)
             >> Set.to_list)
      |> Array.of_list

    let reachable_from starting_node_id graph =
      let res = Array.init (Array.length graph) ~f:(fun _ -> false) in
      let queue = Queue.create () in
      res.(starting_node_id) <- true;
      Queue.enqueue queue starting_node_id;
      while Fn.non Queue.is_empty queue do
        let node_id = Queue.dequeue_exn queue in
        List.iter graph.(node_id) ~f:(fun nxt_node_id ->
            if not res.(nxt_node_id) then (
              res.(nxt_node_id) <- true;
              Queue.enqueue queue nxt_node_id))
      done;
      res

    let optimize muclp =
      let reachable =
        Array.to_list @@ reachable_from 0 @@ pvargraph_of_muclp muclp
      in
      let preds =
        List.zip_exn muclp.Problem.preds (List.tl_exn reachable)
        |> List.filter_map ~f:(fun (p, r) -> if r then Some p else None)
      in
      Problem.make preds muclp.Problem.query
  end

  (* inline extension

     if a predicate P1 is called from only one predicate P2
     and depth(P1) > depth(P2)
     then P1 is eliminated by inline extension.

     With [~cycle_passthrough] other than [No_passthrough], P1 is also eliminated
     when it lies on a cycle of the call graph, does not occur in its own body, does
     not occur in the query, every occurrence of it is in the body of a predicate
     listed before it, and (under [Fix_passthrough]) its sign is [fix]: each
     occurrence is replaced by P1's body.  Exact because the bodies of later
     equations are substituted into earlier ones only (a later equation holds as an
     identity of functions of the earlier variables, whatever the signs).  The
     predicates are processed from the last to the first, so a body substituted
     has already had its own inlinable callees substituted (an inlinable callee
     [k] of [P1] has every caller before it, [P1] included, so it is processed
     first).  The body grows by one copy per occurrence, so the size of the
     result is the product of the occurrence counts along a chain of such
     predicates. *)
  module InlineExtension : sig
    (* [~quantified]: under [Fix_passthrough_unquantified], the predicates whose
       inlining is withheld because a quantifier sits over an occurrence of them
       (default: [quantified_occurrences], read off the input syntactically).
       Any set is exact: withholding an inlining never changes a fixpoint. *)
    val optimize :
      ?cycle_passthrough:Opt.cycle_passthrough ->
      ?quantified:(Problem.t -> Ident.pvar Set.Poly.t) ->
      Problem.t ->
      Problem.t

    val quantified_occurrences : Problem.t -> Ident.pvar Set.Poly.t
  end = struct
    (* let update_called_counts_in_fml called_counts fml =
       if Formula.is_atom fml then
       let atom, _ = Formula.let_atom fml in
       update_called_counts_in_atom called_counts atom
       else if Formula.is_unop fml then
       let _, fml, _ = Formula.let_unop fml in
       update_called_counts_in_fml called_counts fml
       else if Formula.is_binop fml then
       let _, fml1, fml2, _ = Formula.let_binop fml in
       update_called_counts_in_fml called_counts fml1;
       update_called_counts_in_fml called_counts fml2
       else if Formula.is_bind fml then
       let _, fml, _ = Formula.let_bind fml in
       update_called_counts_in_fml called_counts fml
       else
       failwith @@ sprintf "InlineExtension.update_called_counts_in_fml: not implemented for: %s" (Convert.PrinterHum.str_of_formula fml) *)
    let get_pvar_called_counts pvar_to_id preds query =
      let res = Array.init (List.length preds) ~f:(fun _ -> 0) in
      List.iter
        (query :: List.map preds ~f:(fun pred -> pred.Pred.body))
        ~f:
          (Formula.iter_atom ~f:(function
            | Atom.App (Predicate.Var (pvar, _), _, _) ->
                let pvar_id = pvar_to_id pvar in
                res.(pvar_id) <- res.(pvar_id) + 1
            | _ -> ()));
      res

    (* [passthrough_of pvar_to_id preds query]: for each predicate (by position), whether
       it lies on a cycle of the call graph, does not occur in its own body or in the
       query, and occurs only in bodies of predicates before it. *)
    let passthrough_of ~fix_only pvar_to_id preds query =
      let preds = Array.of_list preds in
      let n = Array.length preds in
      let callees =
        Array.map preds ~f:(fun p ->
            Set.to_list @@ Set.Poly.map ~f:pvar_to_id @@ Formula.pvs_of p.Pred.body)
      in
      let in_query = Set.Poly.map ~f:pvar_to_id @@ Formula.pvs_of query in
      let callers_ok = Array.init n ~f:(fun _ -> true) in
      Array.iteri callees ~f:(fun i cs ->
          List.iter cs ~f:(fun j -> if i >= j then callers_ok.(j) <- false));
      (* [on_cycle j]: [j] reaches itself by one or more calls *)
      let on_cycle j =
        let seen = Array.init n ~f:(fun _ -> false) in
        let rec go = function
          | [] -> false
          | k :: rest ->
              if k = j then true
              else if seen.(k) then go rest
              else (
                seen.(k) <- true;
                go (callees.(k) @ rest))
        in
        go callees.(j)
      in
      Array.init n ~f:(fun j ->
          ((not fix_only)
          || Stdlib.( = ) preds.(j).Pred.kind Predicate.MuOrNu)
          && callers_ok.(j)
          && (not (Set.mem in_query j))
          && on_cycle j)

    (* [quantified_pvs phi]: the predicate variables with an occurrence whose
       arguments mention a variable bound by an enclosing quantifier of [phi] --
       the occurrences a quantifier erasure would turn into a made predicate.  An
       occurrence under a quantifier whose variables its arguments do not mention
       does not count: the transition-system translation puts whole loop bodies
       under such binders, and counting them withholds inlinings that carry no
       quantifier into the caller.  Over-approximates elsewhere: a predicate
       variable under a let or a recursive let, or inside an atom's term
       arguments, counts as quantified, so the set never misses an occurrence
       whose arguments mention a bound variable. *)
    let quantified_pvs phi =
      let rec go bound = function
        | Formula.Atom (atm, _) -> (
            match atm with
            | Atom.App (Predicate.Var (pvar, _), args, _) ->
                let inner = Set.remove (Atom.pvs_of atm) pvar in
                if
                  List.exists args ~f:(fun t ->
                      not (Set.is_empty (Set.inter (Term.tvs_of t) bound)))
                then Set.add inner pvar
                else inner
            | _ -> Atom.pvs_of atm)
        | Formula.UnaryOp (_, phi, _) -> go bound phi
        | Formula.BinaryOp (_, phi1, phi2, _) ->
            Set.union (go bound phi1) (go bound phi2)
        | Formula.Bind (_, senv, phi, _) ->
            go (Set.union bound (Set.Poly.of_list (List.map ~f:fst senv))) phi
        | (Formula.LetRec _ | Formula.LetFormula _) as phi -> Formula.pvs_of phi
      in
      go Set.Poly.empty phi

    (* the predicates with an occurrence, in a body or in the query, whose
       arguments mention a variable of an enclosing quantifier *)
    let quantified_occurrences muclp =
      Set.Poly.union_list
      @@ List.map
           (muclp.Problem.query
           :: List.map muclp.Problem.preds ~f:(fun p -> p.Pred.body))
           ~f:quantified_pvs

    let optimize ?(cycle_passthrough = Opt.No_passthrough)
        ?(quantified = quantified_occurrences) muclp =
      let n = List.length muclp.Problem.preds in
      (* pvar -> depth *)
      let pvar_to_id = Hashtbl.Poly.find_exn @@ Problem.get_depth_ht muclp in
      let called_counts =
        get_pvar_called_counts pvar_to_id muclp.Problem.preds
          muclp.Problem.query
      in
      let passthrough =
        match cycle_passthrough with
        | Opt.No_passthrough -> Array.init n ~f:(fun _ -> false)
        | Fix_passthrough | Any_passthrough ->
            passthrough_of
              ~fix_only:(Stdlib.( = ) cycle_passthrough Opt.Fix_passthrough)
              pvar_to_id muclp.Problem.preds muclp.Problem.query
        | Fix_passthrough_once_per_body ->
            let fix =
              passthrough_of ~fix_only:true pvar_to_id muclp.Problem.preds
                muclp.Problem.query
            in
            (* withheld: a candidate with two or more occurrences in one body or
               in the query *)
            List.iter
              (muclp.Problem.query
              :: List.map muclp.Problem.preds ~f:(fun p -> p.Pred.body))
              ~f:(fun phi ->
                let counts = Array.init n ~f:(fun _ -> 0) in
                Formula.iter_atom phi ~f:(function
                  | Atom.App (Predicate.Var (pvar, _), _, _) ->
                      let i = pvar_to_id pvar in
                      counts.(i) <- counts.(i) + 1;
                      if counts.(i) > 1 then fix.(i) <- false
                  | _ -> ()));
            fix
        | Fix_passthrough_unquantified ->
            let fix =
              passthrough_of ~fix_only:true pvar_to_id muclp.Problem.preds
                muclp.Problem.query
            in
            (* asked only when there is a candidate to withhold, so a problem
               without one is left exactly as [Fix_passthrough] leaves it *)
            let quantified =
              if Array.exists fix ~f:Fn.id then quantified muclp
              else Set.Poly.empty
            in
            List.iteri muclp.Problem.preds ~f:(fun i p ->
                if Set.mem quantified p.Pred.name then fix.(i) <- false);
            fix
      in
      let expanded = Array.init n ~f:(fun _ -> false) in
      let preds = Array.of_list muclp.Problem.preds in
      List.iteri (List.rev muclp.Problem.preds) ~f:(fun i pred ->
          let pred_id = n - i - 1 in
          let body =
            Formula.map_atom pred.Pred.body ~f:(function
              | Atom.App (Predicate.Var (pvar, _), args, _) as atm ->
                  let pred_id' = pvar_to_id pvar in
                  if
                    (called_counts.(pred_id') = 1 || passthrough.(pred_id'))
                    && pred_id' > pred_id
                  then (
                    expanded.(pred_id') <- true;
                    assert (Stdlib.(pvar = preds.(pred_id').name));
                    let tsub =
                      Map.Poly.of_alist_exn
                      @@ List.zip_exn
                           (List.map ~f:fst preds.(pred_id').args)
                           args
                    in
                    Formula.subst tsub
                    @@
                    (* avoid variable capture *)
                    Formula.aconv_tvar preds.(pred_id').body)
                  else Formula.mk_atom atm
              | atm -> Formula.mk_atom atm)
          in
          preds.(pred_id) <- { pred with body });
      let preds =
        List.filter (Array.to_list preds) ~f:(fun pred ->
            not expanded.(pvar_to_id pred.Pred.name))
      in
      Problem.make preds muclp.Problem.query
  end

  module EraseQuantifiers : sig
    (* One predicate made by an erasure run.  [delta] is its difference set: the made
       predicates that the erasure of its body folded an occurrence into, and, when its body
       was copied from the source before the source's own body was erased, those that the
       source's erasure folded an occurrence into.  When every predicate of [delta] denotes
       the projection of what its source denotes, the made body is equivalent to the
       projection of its source's final body.  [projected] holds when the body was set to
       that projection and not erased; [delta] is then empty. *)
    type made_record = {
      name : Ident.pvar;
      binder : Formula.binder;
      bounds : sort_env_list;
      source : Ident.pvar;
      origin : Ident.pvar;
      projected : bool;
      delta : Ident.pvar list;
    }

    (* How a block (an original with the predicates made from it) is accepted; see
       [classify]. *)
    type block_class = Exact | Robust | Fusion | Uncovered

    type report = {
      order : (Ident.pvar * Predicate.fixpoint) list;
          (** the original predicates, outermost first, with their signs *)
      made : made_record list;  (** oldest first *)
      classes : (Ident.pvar * block_class) list;
          (** one per original with at least one made predicate, in [order] *)
      fallback : Ident.pvar list;
          (** the originals whose blocks were projected because their copies were not
              accepted ([Hybrid] only) *)
      rounds : int;  (** erasure runs taken by the last run of the rule *)
    }

    val classify :
      order:(Ident.pvar * Predicate.fixpoint) list ->
      made_record list ->
      (Ident.pvar * block_class) list

    val optimize :
      ?keep_query_binder:bool ->
      ?same_scc_calls:Opt.same_scc_calls ->
      ?made_bodies:Opt.made_bodies ->
      ?elim_forall:bool ->
      ?elim_exists:bool ->
      Problem.t ->
      Problem.t

    (* [optimize], with the report of its last erasure run *)
    val optimize_report :
      ?keep_query_binder:bool ->
      ?same_scc_calls:Opt.same_scc_calls ->
      ?made_bodies:Opt.made_bodies ->
      ?elim_forall:bool ->
      ?elim_exists:bool ->
      Problem.t ->
      Problem.t * report
  end = struct
    let seed = 1007

    type made_record = {
      name : Ident.pvar;
      binder : Formula.binder;
      bounds : sort_env_list;
      source : Ident.pvar;
      origin : Ident.pvar;
      projected : bool;
      delta : Ident.pvar list;
    }

    type block_class = Exact | Robust | Fusion | Uncovered

    type report = {
      order : (Ident.pvar * Predicate.fixpoint) list;
      made : made_record list;
      classes : (Ident.pvar * block_class) list;
      fallback : Ident.pvar list;
      rounds : int;
    }

    (* The structural coverage test of the blocks of one erasure run.
       Assumes: [order] lists the run's original predicates, outermost first (a lower
       position is an outer block); every [origin] is an original of [order]; every [delta]
       element is a [name] of [made].
       Guarantees, for each original with a made predicate, in [order]:
       - [Exact] when every member's [delta] is empty;
       - else [Robust] when no member's [delta] has an element of the block itself, and every
         element lies in an outer block or in a robustly consistent inner block.  A block is
         robustly consistent when every element of every member's [delta] lies in a robustly
         consistent block strictly inner to it; an exact block is so vacuously, and the
         recursion descends strictly inwards, so it terminates;
       - else [Fusion] when the block is a least fixpoint and every member binds [Exists], or
         a greatest fixpoint or [MuOrNu] (read as greatest, as the reducer reads it) and every
         member binds [Forall];
       - else [Uncovered].
       Why a block that is not [Uncovered] keeps the original solution's projections as the
       solutions of its made predicates.  [Exact], [Robust]: every made body is equivalent to
       the projection of its source's final body whenever its difference targets denote the
       projections of their sources, which an outer block (at the original solution) and a
       robustly consistent inner block (at every value of the outer predicates) guarantee;
       so the block's operator factors through the projection map, and the rolling rule
       ([f (g x)] and [g (f x)] have their extremal fixpoints related by [f]) carries the
       fixpoint over.  [Fusion]: an existential distributes over arbitrary unions and a
       universal over arbitrary intersections, so the projection map preserves all joins
       (or all meets), and the fixpoint fusion law needs only that the two operators agree on
       consistent points, which every erasure step gives.  A block mixing a universal under a
       least fixpoint (or an existential under a greatest) with a difference target in itself
       or in an inner block that is not robustly consistent has no such argument: a fold
       that agrees on consistent points can change a least fixpoint there.  Pure. *)
    let classify ~order made =
      let index =
        Map.Poly.of_alist_exn (List.mapi order ~f:(fun i (p, _) -> (p, i)))
      in
      let block_of =
        let m =
          Map.Poly.of_alist_exn (List.map made ~f:(fun r -> (r.name, r.origin)))
        in
        Map.Poly.find_exn m
      in
      let blocks =
        List.fold (List.rev made) ~init:Map.Poly.empty ~f:(fun m r ->
            Map.Poly.add_multi m ~key:r.origin ~data:r)
      in
      let members o = Option.value ~default:[] (Map.Poly.find blocks o) in
      let pos = Map.Poly.find_exn index in
      let targets o =
        List.concat_map (members o) ~f:(fun r -> List.map r.delta ~f:block_of)
      in
      let rc_memo = Hashtbl.Poly.create () in
      let rec rc o =
        match Hashtbl.Poly.find rc_memo o with
        | Some b -> b
        | None ->
            let b =
              List.for_all (targets o) ~f:(fun t -> pos t > pos o && rc t)
            in
            Hashtbl.Poly.set rc_memo ~key:o ~data:b;
            b
      in
      List.filter_map order ~f:(fun (o, kind) ->
          match members o with
          | [] -> None
          | rs ->
              let all_bind b =
                List.for_all rs ~f:(fun r -> Stdlib.(r.binder = b))
              in
              let cls =
                if List.for_all rs ~f:(fun r -> List.is_empty r.delta) then Exact
                else if
                  List.for_all (targets o) ~f:(fun t ->
                      Stdlib.(t <> o) && (pos t < pos o || rc t))
                then Robust
                else
                  match kind with
                  | Predicate.Mu when all_bind Formula.Exists -> Fusion
                  | (Predicate.Nu | Predicate.MuOrNu) when all_bind Formula.Forall ->
                      Fusion
                  | _ -> Uncovered
              in
              Some (o, cls))

    (* The adjustable variables AV(t) of a term: the bound variables [a] such that, with the other
       variables fixed, [fun a -> t] is onto the sort, so that [exists a. P t] can become
       [exists y. P y] (and [forall] likewise).  The rules below are only a sufficient syntactic
       test and must never claim a variable that is not adjustable: over the integers [a + a + a]
       and [a + 2 * a] are [3a], which is not onto, and [|a|] is never onto (neither over the
       integers nor the reals), yet these were once claimed, which turned an invalid
       [exists a. P (a + a + a)] into a valid one.  So [|a|] contributes nothing, and a variable is
       kept only when it occurs exactly once in the whole term, along additions, subtractions and
       negations; a single occurrence under [+], [-] and unary [-] is a translate of [a] or [-a],
       which is onto in every sort these arms cover.
       AV(a+1) = {a}
       AV(a*2) = {}
       AV(a + a + b) = {b}
       AV(a + b + c) = {a, b, c}
       AV(1) = {} *)
    let rec occurrences_of v = function
      | Term.Var (x, _, _) -> if Stdlib.( = ) x v then 1 else 0
      | FunApp (T_bool.Formula phi, [], _) ->
          if Set.mem (Formula.tvs_of phi) v then 2 else 0
      | FunApp (_, args, _) ->
          List.fold args ~init:0 ~f:(fun n t -> n + occurrences_of v t)
      | LetTerm _ as t -> if Set.mem (Term.tvs_of t) v then 2 else 0

    let rec adj_vars_of_term_raw = function
      | Term.Var (tvar, _, _) ->
          (* AV(a) = {a} *)
          Set.Poly.singleton tvar
      | FunApp
          ( ( T_int.Int _ | T_real.Real _ | T_bv.BVNum _
            | T_bool.Formula (Formula.Atom (Atom.(True _ | False _), _)) ),
            [],
            _ ) ->
          Set.Poly.empty
      | FunApp ((T_int.Neg | T_real.RNeg | T_bv.BVNeg _), [ a ], _) ->
          (* AV(-a) = AV(a) *) adj_vars_of_term_raw a
      | FunApp ((T_int.Abs | T_real.RAbs), [ _ ], _) ->
          (* |a| is not onto: AV(|a|) = {} *) Set.Poly.empty
      | FunApp
          ( (T_int.(Add | Sub) | T_real.(RAdd | RSub) | T_bv.(BVAdd _ | BVSub _)),
            [ a; b ],
            _ ) ->
          (* AV(a + b) = AV(a - b) = AV(a) + AV(b) - (AV(a) and AV(b)) *)
          let av1 = adj_vars_of_term_raw a in
          let av2 = adj_vars_of_term_raw b in
          Set.diff (Set.union av1 av2) (Set.inter av1 av2)
      | FunApp
          ( ( T_int.(Mul | Div _ | Rem _ | Power)
            | T_real.(RMul | RDiv | RPower)
            | T_bv.(BVMul _ | BVDiv _ (*| BVPower _*)) ),
            [ _; _ ],
            _ ) ->
          (* AV(a * b) = AV(a / b) = AV(a % b) = AV(a ^ b) = {} *)
          Set.Poly.empty
      | term ->
          if true then (*ToDo*) Set.Poly.empty
          else failwith @@ sprintf "unknown operation: %s" (Term.str_of term)

    let adj_vars_of_term t =
      Set.filter (adj_vars_of_term_raw t) ~f:(fun v -> occurrences_of v t = 1)

    let check_separatable avfvs =
      let avfvs = Array.of_list avfvs in
      (* multiset of fv1 U fv2 U ... U fvN *)
      let fv_count : (Ident.tvar, int) Hashtbl.t =
        Hashtbl.Poly.create ~size:seed ()
      in
      (* x in fv1 iff 1 in indexes_of_ftv[x] *)
      let indexes_of_ftv : (Ident.tvar, int list) Hashtbl.t =
        Hashtbl.Poly.create ~size:seed ()
      in
      Array.iteri avfvs ~f:(fun idx ->
          snd >> Set.to_list
          >> List.iter ~f:(fun tvar ->
              let current_count =
                match Hashtbl.Poly.find fv_count tvar with
                | None -> 0
                | Some x -> x
              in
              Hashtbl.Poly.set fv_count ~key:tvar ~data:(current_count + 1);
              Hashtbl.Poly.add_multi indexes_of_ftv ~key:tvar ~data:idx));
      let tvars = Hashtbl.Poly.keys fv_count in
      let is_assigned = Array.init (Array.length avfvs) ~f:(fun _ -> false) in
      let queue = Queue.create () in
      List.iter tvars ~f:(fun tvar ->
          if Hashtbl.Poly.find_exn fv_count tvar = 1 then
            Queue.enqueue queue tvar);
      while Fn.non Queue.is_empty queue do
        let tvar = Queue.dequeue_exn queue in
        if Hashtbl.Poly.find_exn fv_count tvar = 1 then
          Hashtbl.find_multi indexes_of_ftv tvar
          |> List.iter ~f:(fun idx ->
              if (not is_assigned.(idx)) && Set.mem (fst avfvs.(idx)) tvar then (
                is_assigned.(idx) <- true;
                Set.iter
                  (snd avfvs.(idx))
                  ~f:(fun tvar' ->
                    let nxt_count = Hashtbl.Poly.find_exn fv_count tvar' - 1 in
                    Hashtbl.Poly.set fv_count ~key:tvar' ~data:nxt_count;
                    if nxt_count = 1 then Queue.enqueue queue tvar')))
      done;
      Array.for_all ~f:Fn.id is_assigned

    let str_of_tvarset s =
      sprintf "{%s}" @@ String.concat_map_set s ~sep:", " ~f:Ident.name_of_tvar

    let bound_flags_of_app_opt bounds args =
      (* let args = List.map Term.simplify args in *)
      let bounds = Set.Poly.of_list @@ List.map ~f:fst bounds in
      let avs = List.map args ~f:(adj_vars_of_term >> Set.inter bounds) in
      (* Match SimpleFormula.get_ftv: a scalar Bool bound name can occur
         as a nullary predicate alias inside a term. Omitting it here would
         treat an argument depending on that binder as independent, even
         after get_ftv correctly retained the binder. Positive-arity relation
         heads are not scalar dependencies. *)
      let scalar_dependencies term =
        Set.union (Term.tvs_of term)
          (Set.Poly.of_list
             (Set.to_list (Formula.predicate_signatures_of_term term)
              |> List.filter_map ~f:(fun (pvar, args) ->
                     if List.is_empty args then
                       Some (Ident.pvar_to_tvar pvar)
                     else None)))
      in
      let fvs = List.map args ~f:(scalar_dependencies >> Set.inter bounds) in
      let avfvs = List.zip_exn avs fvs in
      if false then
        printf "[%s]: %s\n"
          (String.concat_map_list ~sep:"; " ~f:Term.str_of args)
          (String.concat_map_list ~sep:" "
             ~f:(fun (av, fv) ->
               String.paren
               @@ sprintf "%s, %s" (str_of_tvarset av) (str_of_tvarset fv))
             avfvs);
      if
        List.exists avfvs ~f:(fun (av, fv) ->
            Fn.non Set.is_empty fv && Set.is_empty av)
      then
        (* if FV(t) and bounds != {} /\ AV(t) and bounds = {} for some arg t *)
        None
      else if
        check_separatable (List.filter avfvs ~f:(snd >> Fn.non Set.is_empty))
      then
        (* exists x, y. F x (x + y) -> exists x, y. F x y
           exists x, y. F (x + y) (x + y) -> exists x, y. F (x + y) (x + y) *)
        Some (List.map avs ~f:(Fn.non Set.is_empty))
      else None

    let create_initial_pvar_to_xpvar bounds pvar =
      let res = Hashtbl.Poly.create ~size:seed () in
      Hashtbl.Poly.set res ~key:(List.map ~f:(fun _ -> false) bounds) ~data:pvar;
      res

    let let_if_opt fml =
      if Fn.non SimpleFormula.is_branch fml then None
      else
        let outer_op, fmls = SimpleFormula.let_branch fml in
        match fmls with
        | [ fml1; fml2 ] ->
            let inner_op = Formula.flip_binop outer_op in
            let get_formulas op fml =
              (* for fmls: atom *)
              if SimpleFormula.is_branch fml then
                let op', fmls = SimpleFormula.let_branch fml in
                if Stdlib.(op' = op) then fmls else [ fml ]
              else [ fml ]
            in
            let ht_of_formulas fmls =
              let ht = Hashtbl.Poly.create ~size:1234 () in
              List.iteri fmls ~f:(fun i fml ->
                  Hashtbl.Poly.set ht ~key:fml ~data:i);
              ht
            in
            let search_for_dual_formulas fmls ht =
              List.fold_left ~init:None (List.zip_index fmls)
                ~f:(fun res (fml, i) ->
                  if Option.is_none res then
                    if Set.is_empty @@ SimpleFormula.get_fpv fml then
                      (* TODO: to be more efficient *)
                      let fmls =
                        get_formulas inner_op @@ SimpleFormula.neg fml
                      in
                      if List.for_all ~f:(Hashtbl.Poly.mem ht) fmls then
                        Some ([ i ], List.map ~f:(Hashtbl.Poly.find_exn ht) fmls)
                      else None
                    else None
                  else res)
            in
            let fmls1 = get_formulas inner_op fml1 in
            let fmls2 = get_formulas inner_op fml2 in
            let ht1 = ht_of_formulas fmls1 in
            let ht2 = ht_of_formulas fmls2 in
            let result =
              match search_for_dual_formulas fmls1 ht2 with
              | Some result -> Some result
              | None -> (
                  match search_for_dual_formulas fmls2 ht1 with
                  | Some (pos2, pos1) -> Some (pos1, pos2)
                  | None -> None)
            in
            if Option.is_none result then None
            else
              let pos1, pos2 = Option.value_exn result in
              let set_pos1 = Set.Poly.of_list pos1 in
              let set_pos2 = Set.Poly.of_list pos2 in
              let cond_fml =
                List.zip_index fmls1
                |> List.filter ~f:(snd >> Set.mem set_pos1)
                |> List.map ~f:fst
                |> SimpleFormula.mk_branch_with_simplification_one inner_op
              in
              (* TODO: O(nlogn) -> O(n) *)
              let fml1 =
                List.zip_index fmls1
                |> List.filter ~f:(snd >> Set.mem set_pos1 >> not)
                |> List.map ~f:fst
                |> SimpleFormula.mk_branch_with_simplification_one inner_op
              in
              let fml2 =
                List.zip_index fmls2
                |> List.filter ~f:(snd >> Set.mem set_pos2 >> not)
                |> List.map ~f:fst
                |> SimpleFormula.mk_branch_with_simplification_one inner_op
              in
              Some (outer_op, cond_fml, fml1, fml2)
        | _ -> None

    let let_if fml =
      match let_if_opt fml with Some res -> res | None -> assert false

    let is_from_if fml =
      match let_if_opt fml with Some _ -> true | None -> false

    (* [scc_of_preds preds a b]: whether [a] and [b] are in one strongly connected component of
       the call graph of [preds] (an edge P -> Q when Q occurs in P's body), that is [a = b] or
       each reaches the other by one or more calls.  A name that is not in [preds] reaches
       nothing.  [a = b] is only asked of an application of [a] inside [a]'s own body, which is
       a cycle, so counting every predicate as in its own component costs nothing. *)
    let scc_of_preds (preds : Pred.t list) =
      let callees =
        Map.Poly.of_alist_reduce ~f:Set.union
        @@ List.map preds ~f:(fun (p : Pred.t) -> (p.name, Formula.pvs_of p.body))
      in
      let reach_of p =
        (* every predicate reachable from [p] by one or more calls *)
        let rec go seen = function
          | [] -> seen
          | q :: rest ->
              let next =
                Set.diff
                  (Option.value ~default:Set.Poly.empty (Map.Poly.find callees q))
                  seen
              in
              go (Set.union seen next) (Set.to_list next @ rest)
        in
        go Set.Poly.empty [ p ]
      in
      let reach =
        Map.Poly.of_alist_reduce ~f:(fun a _ -> a)
        @@ List.map preds ~f:(fun (p : Pred.t) -> (p.name, reach_of p.name))
      in
      let reaches a b =
        match Map.Poly.find reach a with Some r -> Set.mem r b | None -> false
      in
      fun a b -> Stdlib.(a = b) || (reaches a b && reaches b a)

    (* Optional rules that decline an erasure ([keep_query_binder] and the [same_scc_calls]
       choice of [Config.Erase]).  A declined application keeps its quantifier, exactly as this
       pass leaves one whose bound arguments are not adjustable, so no later step can rely on an
       erasure having fired: every rule preserves the query's validity whatever it decides (also
       when [Keep_same_scc_if_grows] decides from a first run's output), and changes only the
       shape of the problem handed on.

       One run of the erasure.  [decline_scc q] holds for the original predicates [q] whose
       same-component calls are left quantified (the rule of [Keep_same_scc], restricted to the
       components it names).  Returns the erased problem and, for each of its predicates, the
       original predicate it stands for. *)
    (* [miniscope b xs phi] is [b xs. phi] with the binder block pushed inwards as a block:
       a variable that does not occur is dropped; a universal block distributes over a
       conjunction (each conjunct keeping the variables it mentions) and moves past the
       disjuncts that mention none of its variables (an existential block dually, over a
       disjunction and past the conjuncts); a block commutes with a nested binder of the
       same kind that rebinds none of its variables.  The block is never split by variable,
       so a body whose disjuncts each mention some of the variables keeps the block on top.
       Every step is an equivalence of first-order logic over nonempty sorts, valid whatever
       the predicates denote, so the result is equivalent to [b xs. phi] for every
       interpretation.  Other shapes keep the block where it stands.  A random binder is
       left alone. *)
    let miniscope binder bounds phi =
      let rec flatten op = function
        | Formula.BinaryOp (op', a, b, _) when Stdlib.(op = op') ->
            flatten op a @ flatten op b
        | f -> [ f ]
      in
      let rebuild op = function
        | [] -> if Stdlib.(op = Formula.And) then Formula.mk_true () else Formula.mk_false ()
        | f :: fs -> List.fold fs ~init:f ~f:(fun acc g -> Formula.mk_binop op acc g)
      in
      let mentions xs f =
        let fvs = Formula.tvs_of f in
        List.exists xs ~f:(fun (x, _) -> Set.mem fvs x)
      in
      let rec block b xs phi =
        let fvs = Formula.tvs_of phi in
        let xs = List.filter xs ~f:(fun (x, _) -> Set.mem fvs x) in
        if List.is_empty xs then phi
        else
          (* the connective [b] distributes over, and the one it moves past *)
          let dist, past =
            match b with
            | Formula.Forall -> (Formula.And, Formula.Or)
            | _ -> (Formula.Or, Formula.And)
          in
          match phi with
          | Formula.BinaryOp (op, _, _, _) when Stdlib.(op = dist) ->
              rebuild dist (List.map (flatten dist phi) ~f:(block b xs))
          | Formula.BinaryOp (op, _, _, _) when Stdlib.(op = past) -> (
              let yes, no = List.partition_tf (flatten past phi) ~f:(mentions xs) in
              match (yes, no) with
              | _, [] -> Formula.mk_bind b xs phi
              | [ f ], _ -> rebuild past (no @ [ block b xs f ])
              | _ -> rebuild past (no @ [ Formula.mk_bind b xs (rebuild past yes) ]))
          | Formula.Bind (b', ys, psi, info)
            when Stdlib.(b = b')
                 && not
                      (List.exists ys ~f:(fun (y, _) ->
                           List.exists xs ~f:(fun (x, _) -> Ident.tvar_equal x y)))
            ->
              Formula.mk_bind ~info b' ys (block b xs psi)
          | _ -> Formula.mk_bind b xs phi
      in
      match binder with
      | Formula.Forall | Formula.Exists -> block binder bounds phi
      | _ -> Formula.mk_bind_if_bounded binder bounds phi

    let run ~keep_query_binder ~decline_scc ~made_bodies ~project_origin
        ~elim_forall ~elim_exists muclp =
      (* whether the predicates made from the original [o] get their bodies as under
         [Project_final]: everywhere under it, and on the blocks [project_origin] names
         otherwise (the fallback of [Hybrid]) *)
      let project_block o =
        Stdlib.(made_bodies = Opt.Project_final) || project_origin o
      in
      let miniscope_projected =
        Stdlib.(made_bodies = Opt.Hybrid_miniscoped)
      in
      let preds = Array.of_list muclp.Problem.preds in
      let same_scc = scc_of_preds muclp.Problem.preds in
      (* The list sentinel and generated predicates share the input's symbol
         namespace. A counter alone is not freshness for API-built problems:
         a colliding sentinel truncates the list and a colliding copy replaces
         an existing definition. Reserve all input names and every allocation. *)
      let occupied = ref
        (List.fold muclp.Problem.preds
           ~init:(Formula.names_spelled_in muclp.Problem.query)
           ~f:(fun names (pred : Pred.t) ->
             Set.union
               (Set.add names (Ident.pvar_to_tvar pred.name))
               (Set.union (Formula.names_spelled_in pred.body)
                  (Set.Poly.of_list (List.map pred.args ~f:fst)))))
      in
      let rec fresh_pvar () =
        let p = Ident.mk_fresh_pvar () in
        let name = Ident.pvar_to_tvar p in
        if Set.mem !occupied name then fresh_pvar ()
        else (
          occupied := Set.add !occupied name;
          p)
      in
      (* the original predicate a predicate made by [add_pred] stands for (itself otherwise) *)
      let origin_of : (Ident.pvar, Ident.pvar) Hashtbl.t =
        Hashtbl.Poly.create ~size:seed ()
      in
      let origin p = Option.value ~default:p (Hashtbl.Poly.find origin_of p) in
      (* the predicate whose body is being erased; [None] while the query is *)
      let owner : Ident.pvar option ref = ref None in
      (* the predicates whose bodies have been erased (read by the census only) *)
      let erased_bodies : Ident.pvar Hash_set.t = Hash_set.Poly.create () in
      let pvar_to_pred : (Ident.pvar, Pred.t) Hashtbl.t =
        Hashtbl.Poly.create ~size:seed ()
      in
      let pvar_to_nxtpvar : (Ident.pvar, Ident.pvar) Hashtbl.t =
        Hashtbl.Poly.create ~size:seed ()
      in
      let pvar_to_epvar :
          (Ident.pvar, (bool list, Ident.pvar) Hashtbl.t) Hashtbl.t =
        Hashtbl.Poly.create ~size:seed ()
      in
      let pvar_to_fpvar :
          (Ident.pvar, (bool list, Ident.pvar) Hashtbl.t) Hashtbl.t =
        Hashtbl.Poly.create ~size:seed ()
      in
      let endpvar = fresh_pvar () in
      let startpvar =
        if Array.is_empty preds then endpvar else preds.(0).name
      in
      let ht_of_binder = function
        | Formula.Forall -> pvar_to_fpvar
        | Exists -> pvar_to_epvar
        | _ -> assert false
      in
      (* init pvar_to_pred, pvar_to_nxtpvar, pvar_to_epvar, pvar_to_fpvar *)
      Array.iteri preds ~f:(fun i pred ->
          let nxtpvar =
            if i = Array.length preds - 1 then endpvar else preds.(i + 1).name
          in
          Hashtbl.Poly.set pvar_to_nxtpvar ~key:pred.name ~data:nxtpvar;
          Hashtbl.Poly.set pvar_to_pred ~key:pred.name ~data:pred;
          Hashtbl.Poly.set pvar_to_epvar ~key:pred.name
            ~data:(create_initial_pvar_to_xpvar pred.args pred.name);
          Hashtbl.Poly.set pvar_to_fpvar ~key:pred.name
            ~data:(create_initial_pvar_to_xpvar pred.args pred.name));
      (* queue for erase_quantifiers_rep *)
      let queue = Queue.create () in
      (* Under [Project_final], the predicates made so far, newest first, each with its
         binder, the parameters it binds and its source; their bodies are set after the
         queue is empty. *)
      let made_later = ref [] in
      (* every predicate made, newest first, with the same data and its origin, whether its
         body is projected, and whether it was copied from a source whose body had not been
         erased yet *)
      let made_info = ref [] in
      (* for each predicate whose body has been erased, the made predicates its erasure
         folded an occurrence into (repeats kept; a failed erasure's folds are kept too, which
         only enlarges the difference sets read from them) *)
      let folds_of : (Ident.pvar, Ident.pvar list) Hashtbl.t =
        Hashtbl.Poly.create ~size:seed ()
      in
      (* add exists/forall pred of [pvar] pred and return the pvar of it *)
      let add_pred binder bound_flags pvar =
        (* construct new function *)
        let pvar, pred, qbounds =
          let pred' = Hashtbl.find_exn pvar_to_pred pvar in
          let pvar' = fresh_pvar () in
          (* TODO *)
          Debug.print
          @@ lazy
               (sprintf "add_pred (pvar): %s. %s"
                  (Formula.str_of_binder binder)
                  (Ident.name_of_pvar pvar'));
          let qbounds, args =
            List.partition_map (List.zip_exn pred'.args bound_flags)
              ~f:(fun (b, f) -> if f then First b else Second b)
          in
          ( pred'.name,
            {
              pred' with
              name = pvar';
              args;
              body = Formula.mk_bind_if_bounded binder qbounds pred'.body;
            },
            qbounds )
        in
        (* update pvar_to_nxtpvar: insert the pred just after [pvar] *)
        let nxtpvar = Hashtbl.Poly.find_exn pvar_to_nxtpvar pvar in
        Hashtbl.Poly.set pvar_to_nxtpvar ~key:pvar ~data:pred.name;
        Hashtbl.Poly.set pvar_to_nxtpvar ~key:pred.name ~data:nxtpvar;
        (* update pvar_to_pred *)
        Hashtbl.Poly.set pvar_to_pred ~key:pred.name ~data:pred;
        Hashtbl.Poly.set origin_of ~key:pred.name ~data:(origin pvar);
        (* update pvar_to_fpvar, pvar_to_epvar *)
        Hashtbl.Poly.set
          (Hashtbl.find_exn (ht_of_binder binder) pvar)
          ~key:bound_flags ~data:pred.name;
        Hashtbl.Poly.set (ht_of_binder binder) ~key:pred.name
          ~data:(Hashtbl.Poly.create ~size:seed ());
        let project_final = project_block (origin pvar) in
        let unerased = not (Hash_set.mem erased_bodies pvar) in
        if Option.is_some (Sys.getenv "COAR_ERASURE_CENSUS") then
          eprintf "erasure-census-made: %s src=%s copied=%s\n%!"
            (Ident.name_of_pvar pred.name) (Ident.name_of_pvar pvar)
            (if project_final then "final"
             else if unerased then "unerased"
             else "erased");
        (* push to the queue for erase_quantifiers_rep, or, when its block is projected,
           record it so that its body is built from the source's final body *)
        made_info :=
          ( (pred.name, binder, qbounds, pvar),
            (origin pvar, project_final, unerased) )
          :: !made_info;
        if project_final then
          made_later :=
            (pred.name, binder, qbounds, pvar)
            :: !made_later
        else Queue.enqueue queue pred.name;
        (* return new pvar *)
        pred.name
      in
      let get_or_add_pred binder bound_flags pvar =
        Debug.print
        @@ lazy
             (sprintf "get_or_add_pred: %s. %s"
                (Formula.str_of_binder binder)
                (Ident.name_of_pvar pvar));
        let ht' =
          let ht = ht_of_binder binder in
          Hashtbl.Poly.find_or_add
            ~default:(fun _ -> Hashtbl.Poly.create ())
            ht pvar
        in
        if not (Hashtbl.Poly.mem ht' bound_flags) then
          ignore (add_pred binder bound_flags pvar : Ident.pvar);
        Hashtbl.find_exn ht' bound_flags
      in
      (* With [COAR_ERASURE_CENSUS] set, one stderr line per erased
         occurrence: the fixpoint of the predicate applied there (which the
         new predicate inherits), the erased binder, and whether the
         occurrence is in the query, in an original predicate's body or in
         the body of a predicate this pass made, with that predicate's name;
         one line per predicate made, with its source and whether the
         source's body had already been erased when it was copied ([final] under
         [Project_final], where the body is set from the source's final body); and one
         line per run with the number of predicates it was given, followed by one line
         listing them in order, outermost first, each with its fixpoint.  A census of
         where each combination of fixpoint and binder occurs; it changes
         nothing, and prints nothing without the variable. *)
      let erasure_census binder pvar =
        if Option.is_some (Sys.getenv "COAR_ERASURE_CENSUS") then
          let kind =
            match Hashtbl.Poly.find pvar_to_pred pvar with
            | Some (p : Pred.t) -> Predicate.str_of_fop p.kind
            | None -> "?"
          in
          eprintf "erasure-census: %s %s %s\n%!" kind
            (match binder with
            | Formula.Forall -> "forall"
            | Formula.Exists -> "exists"
            | _ -> "other")
            (match !owner with
            | None -> "query"
            | Some p ->
                sprintf "%s owner=%s"
                  (if Stdlib.( = ) (origin p) p then "body" else "made-body")
                  (Ident.name_of_pvar p))
      in
      (* With [COAR_ERASURE_CENSUS] set, one more stderr line per erased occurrence, after the
         predicate standing for it is found or made: the body it is in (as above), the predicate
         applied at the occurrence and the made predicate that replaces it. *)
      let erasure_census_fold pvar made =
        Option.iter !owner ~f:(fun p ->
            Hashtbl.Poly.add_multi folds_of ~key:p ~data:made);
        if Option.is_some (Sys.getenv "COAR_ERASURE_CENSUS") then
          eprintf "erasure-census-fold: owner=%s target=%s pred=%s\n%!"
            (match !owner with None -> "query" | Some p -> Ident.name_of_pvar p)
            (Ident.name_of_pvar pvar) (Ident.name_of_pvar made)
      in
      let binder_of_op = function
        | Formula.Forall -> Formula.And
        | Formula.Exists -> Formula.Or
        | _ -> assert false
      in
      (* erase quantifiers in [binder] [bounds]. [fml] *)
      (* [keep] holds while [binder] [bounds] is the query's outermost quantifier block under
         [keep_query_binder]: an application under it keeps its quantifier. *)
      let rec erase_quantifiers_rep_bind ?(keep = false) binder bounds fml =
        let erase_quantifiers_rep_bind' = erase_quantifiers_rep_bind ~keep in
        let ftv = SimpleFormula.get_ftv fml in
        let bounds = List.filter ~f:(fst >> Set.mem ftv) bounds in
        if List.is_empty bounds then erase_quantifiers_rep fml
        else if SimpleFormula.is_branch fml then (
          (* exists a. P(a) \/ P(b) -> (exists a. P(a)) \/ (exists a. P(b))
             exists a. P(a) /\ Q -> (exists a. P(a)) /\ Q *)
          let op, fmls = SimpleFormula.let_branch fml in
          if Stdlib.(binder_of_op binder = op) then
            (* exists a. P(a) \/ P(b) -> (exists a. P(a)) \/ (exists a. P(b)) *)
            SimpleFormula.mk_branch op
            @@ List.map ~f:(erase_quantifiers_rep_bind' binder bounds) fmls
          else if is_from_if fml then (
            (* forall x. (P /\ Q) \/ (not P /\ R)
               -> forall x. (P => Q) /\ (not P => R)
               -> (forall x. not P \/ Q) /\ (forall x. P \/ R)

               exists x. (P \/ Q) /\ (not P \/ R)
               -> exists x. (not P => Q) /\ (P => R)
               -> exists x. (not P /\ Q) \/ (P /\ R)
               -> (exists x. not P /\ Q) \/ (exists x. P /\ R) *)
            let op', cond_fml, fml1, fml2 = let_if fml in
            assert (Stdlib.(op' = op));
            let fml1 =
              SimpleFormula.mk_branch_with_simplification_one op
                [ SimpleFormula.neg cond_fml; fml1 ]
              |> erase_quantifiers_rep_bind' binder bounds
            in
            let fml2 =
              SimpleFormula.mk_branch_with_simplification_one op
                [ cond_fml; fml2 ]
              |> erase_quantifiers_rep_bind' binder bounds
            in
            SimpleFormula.mk_branch_with_simplification_one
              (Formula.flip_binop op) [ fml1; fml2 ])
          else
            (* exists a. P(a) /\ Q
                 -> (exists a. P(a)) /\ Q

               [exists a, b, c. P1(a, b) /\ P2(a) /\ P3(c)]
                 -> [exists a, b, c. P1(a, b) /\ P2(a)] /\ [exists a, b, c. P3(c)]
                 with UnionFind *)
            let bounds_tvar_set = Set.Poly.of_list @@ List.map ~f:fst bounds in
            let ht = Hashtbl.Poly.create ~size:seed () in
            List.iteri fmls ~f:(fun i fml ->
                Set.iter (SimpleFormula.get_ftv fml) ~f:(fun tvar ->
                    if Set.mem bounds_tvar_set tvar then
                      let ids =
                        match Hashtbl.Poly.find ht tvar with
                        | Some ids -> ids
                        | None -> []
                      in
                      Hashtbl.Poly.set ht ~key:tvar ~data:(i :: ids)));
            let n = List.length fmls in
            if false then
              printf "%s\n\n"
                (String.concat_map_list ~sep:"\n" ~f:SimpleFormula.string_of
                   fmls);
            assert (n >= 2);
            (* because of simplification *)
            (* construct uf *)
            let uf = UnionFind.mk_size_uf ~size:n in
            Hashtbl.Poly.iter ht ~f:(fun ids ->
                let ids = Array.of_list ids in
                Array.iteri ids ~f:(fun i _ ->
                    if i + 1 < Array.length ids then
                      UnionFind.unite ids.(i) ids.(i + 1) uf));
            (* reconstruct the branch *)
            let fmls = Array.of_list fmls in
            UnionFind.get_groups uf
            |> List.map ~f:(fun ids ->
                let fmls' = List.map ~f:(fun id -> fmls.(id)) ids in
                match fmls' with
                | [ fml' ] -> erase_quantifiers_rep_bind' binder bounds fml'
                (* try let_if *)
                | [ _; _ ] ->
                    (* TODO *)
                    let fml' =
                      SimpleFormula.mk_branch_with_simplification_one op fmls'
                    in
                    if is_from_if fml' then
                      erase_quantifiers_rep_bind' binder bounds fml'
                    else
                      List.map ~f:erase_quantifiers_rep fmls'
                      |> SimpleFormula.mk_branch_with_simplification_one op
                      |> SimpleFormula.mk_bind_with_filter binder bounds
                | _ ->
                    (* List.length fmls >= 2 *)
                    List.map ~f:erase_quantifiers_rep fmls'
                    |> SimpleFormula.mk_branch_with_simplification_one op
                    |> SimpleFormula.mk_bind_with_filter binder bounds)
            |> SimpleFormula.mk_branch_with_simplification_one op)
        else if SimpleFormula.is_bind fml then
          let binder', bounds', fml' = SimpleFormula.let_bind fml in
          (* forall x. forall y. P -> forall x, y. P *)
          if Stdlib.(binder = binder') then
            (* bounds, bounds' must be distinct *)
            (*let new_bounds = bounds @ bounds' in
              assert (Stdlib.(SimpleFormula.update_bounds bounds bounds' = new_bounds));*)
            let new_bounds = SimpleFormula.update_bounds bounds bounds' in
            erase_quantifiers_rep_bind' binder new_bounds fml'
          else
            (* forall x. exists y. P
               1. process [exists y. P]
               2. if it's still of the form [forall x. exists y. P] then give up erasing (to avoid an infinite-loop)
               3. otherwise, continue to process erase_quantifiers_rep_bind *)
            let fml = erase_quantifiers_rep_bind binder' bounds' fml' in
            if SimpleFormula.is_bind fml then
              let binder', _, _ = SimpleFormula.let_bind fml in
              if Stdlib.(binder <> binder') then
                SimpleFormula.mk_bind_with_filter binder bounds fml
              else erase_quantifiers_rep_bind' binder bounds fml
            else erase_quantifiers_rep_bind' binder bounds fml
        else if SimpleFormula.is_app fml then (
          let pvar, args = SimpleFormula.let_app fml in
          Debug.print
          @@ lazy
               (sprintf "erase_quantifiers_rep_bind(is_app): "
               ^ SimpleFormula.string_of fml);
          let declined =
            keep
            || decline_scc (origin pvar)
               &&
               match !owner with
               | Some p -> same_scc (origin p) (origin pvar)
               | None -> false
          in
          match
            if declined then None else bound_flags_of_app_opt bounds args
          with
          | Some bound_flags ->
              erasure_census binder pvar;
              let made = get_or_add_pred binder bound_flags pvar in
              erasure_census_fold pvar made;
              SimpleFormula.mk_app made
              @@ List.map ~f:fst
              @@ List.filter ~f:(snd >> not)
              @@ List.zip_exn args bound_flags
          | None -> SimpleFormula.mk_bind_with_filter binder bounds fml)
        else if SimpleFormula.is_cond fml then
          SimpleFormula.mk_bind_with_filter binder bounds fml
        else assert false
      (* [top] holds on the query's root and on what it reaches through conjunctions only *)
      and erase_quantifiers_rep ?(top = false) fml =
        if SimpleFormula.is_and fml then
          SimpleFormula.let_and fml
          |> List.map ~f:(erase_quantifiers_rep ~top)
          |> SimpleFormula.mk_and
        else if SimpleFormula.is_or fml then
          SimpleFormula.let_or fml
          |> List.map ~f:erase_quantifiers_rep
          |> SimpleFormula.mk_or
        else if SimpleFormula.is_bind fml then
          let binder, bounds, fml' = SimpleFormula.let_bind fml in
          if
            Stdlib.(
              (elim_forall && binder = Formula.Forall)
              || (elim_exists && binder = Formula.Exists))
          then
            erase_quantifiers_rep_bind ~keep:(top && keep_query_binder) binder
              bounds fml'
          else fml
        else if SimpleFormula.is_atom fml then fml
        else assert false
      in
      let erase_quantifiers ?(top = false) fml =
        try
          Debug.print
          @@ lazy (sprintf "erase_quantifiers before: " ^ Formula.str_of fml);
          let fml = SimpleFormula.of_formula @@ Formula.nnf_of fml in
          Debug.print
          @@ lazy
               (sprintf "erase_quantifiers normalized: "
               ^ SimpleFormula.string_of fml);
          SimpleFormula.formula_of @@ erase_quantifiers_rep ~top fml
        with exn_ when not (Common.Timer.is_async exn_) -> fml
      in
      if Option.is_some (Sys.getenv "COAR_ERASURE_CENSUS") then (
        eprintf "erasure-census-run: preds=%d\n%!" (Array.length preds);
        (* the predicates in the problem's order, outermost first, with their fixpoints *)
        eprintf "erasure-census-order:%s\n%!"
          (String.concat
             (Array.to_list
                (Array.map preds ~f:(fun (p : Pred.t) ->
                     sprintf " %s:%s" (Ident.name_of_pvar p.name)
                       (Predicate.str_of_fop p.kind))))));
      (* init queue *)
      Array.iter preds ~f:(fun pred -> Queue.enqueue queue pred.name);
      owner := None;
      let query = erase_quantifiers ~top:true muclp.Problem.query in
      while Fn.non Queue.is_empty queue do
        let pvar = Queue.dequeue_exn queue in
        let pred = Hashtbl.Poly.find_exn pvar_to_pred pvar in
        assert (Stdlib.( = ) pvar pred.name);
        Debug.print @@ lazy (sprintf "%s: " (Ident.name_of_pvar pvar));
        owner := Some pvar;
        Hashtbl.Poly.set pvar_to_pred ~key:pvar
          ~data:{ pred with body = erase_quantifiers pred.body };
        Hash_set.add erased_bodies pvar
      done;
      (* A projected block: each of its made predicates gets its source's final body under the
         binder of the flagged parameters (its one-level projection), oldest first, so that a
         source made earlier already has its own body (a source is in the same block and made
         before the predicate it is the source of).  Under [Project_final] every source is an
         original predicate: a fold happens only while the query or an original body is
         erased, and those mention only original predicates until they are erased.  Under
         [Hybrid] a source can be a projected predicate whose occurrence an erased body of
         another block folded.  The body is not erased again. *)
      List.iter (List.rev !made_later) ~f:(fun (name, binder, qbounds, src) ->
          let pred = Hashtbl.Poly.find_exn pvar_to_pred name in
          let src_body = (Hashtbl.Poly.find_exn pvar_to_pred src).Pred.body in
          Hashtbl.Poly.set pvar_to_pred ~key:name
            ~data:
              {
                pred with
                body =
                  (if miniscope_projected then miniscope binder qbounds src_body
                   else Formula.mk_bind_if_bounded binder qbounds src_body);
              });
      (* With [COAR_ERASURE_CENSUS] set, one stderr line per made predicate: whether its final
         body is equivalent, for every interpretation of the predicates, to the one-level
         projection of its source's final body (the body [Project_final] gives it).  Asked of
         Z3 with the predicates uninterpreted, 3 s each; [unknown] is any other answer. *)
      if Option.is_some (Sys.getenv "COAR_ERASURE_CENSUS") then
        List.iter (List.rev !made_info) ~f:(fun ((name, binder, qbounds, src), _) ->
            let body = (Hashtbl.Poly.find_exn pvar_to_pred name).Pred.body in
            let proj =
              Formula.mk_bind_if_bounded binder qbounds
                (Hashtbl.Poly.find_exn pvar_to_pred src).Pred.body
            in
            let answer =
              if String.equal (Formula.str_of body) (Formula.str_of proj) then "equal"
              else
                match
                  Z3Smt.Z3interface.check_valid ~timeout:(Some 3000) ~id:None
                    (LogicOld.get_fenv ()) (Formula.mk_iff body proj)
                with
                | `Valid -> "equivalent"
                | `Invalid _ -> "differs"
                | _ -> "unknown"
                | exception exn_ when not (Common.Timer.is_async exn_) ->
                    "unknown"
            in
            eprintf "erasure-census-shat: %s %s\n%!" (Ident.name_of_pvar name) answer);
      (* reconstruct preds from startpvar, endpvar, pvar_to_nxtpvar, pvar_to_pred, processed_pvars(reached) *)
      let preds_queue = Queue.create () in
      let current_pvar = ref startpvar in
      while Stdlib.(!current_pvar <> endpvar) do
        Queue.enqueue preds_queue
        @@ Hashtbl.Poly.find_exn pvar_to_pred !current_pvar;
        current_pvar := Hashtbl.Poly.find_exn pvar_to_nxtpvar !current_pvar
      done;
      let made =
        List.rev_map !made_info
          ~f:(fun ((name, binder, bounds, source), (origin, projected, unerased)) ->
            let folds p =
              Option.value ~default:[] (Hashtbl.Poly.find folds_of p)
            in
            let delta =
              if projected then []
              else
                List.dedup_and_sort ~compare:Ident.pvar_compare
                  (folds name @ if unerased then folds source else [])
            in
            { name; binder; bounds; source; origin; projected; delta })
      in
      (Problem.make ((*ToDo*) Queue.to_list preds_queue) query, origin, made)

    (* The original predicates whose call-graph component the erasure [erased] grew: those in
       the original component of an original predicate [q] with two representatives (by
       [origin]) in one strongly connected component of [erased]'s call graph restricted to
       the predicates the query reaches.  Each call edge of [erased] maps by [origin] to a
       call edge of the original problem (a fresh predicate's body is its original's body with
       some quantified calls renamed to fresh copies of their callees), so each component of
       [erased] maps into one original component; two representatives of one original in a
       component are therefore exactly a component larger than the original's image. *)
    let grown_sccs ?(splits = false) ~original ~erased ~origin () =
      let same_scc_orig = scc_of_preds original.Problem.preds in
      let same_scc_er = scc_of_preds erased.Problem.preds in
      let callees =
        Map.Poly.of_alist_reduce ~f:Set.union
        @@ List.map erased.Problem.preds ~f:(fun (p : Pred.t) ->
            (p.name, Formula.pvs_of p.body))
      in
      let reached =
        let rec go seen = function
          | [] -> seen
          | q :: rest ->
              let next =
                Set.diff
                  (Option.value ~default:Set.Poly.empty (Map.Poly.find callees q))
                  seen
              in
              go (Set.union seen next) (Set.to_list next @ rest)
        in
        let roots = Formula.pvs_of erased.Problem.query in
        go roots (Set.to_list roots)
      in
      let members =
        List.filter_map erased.Problem.preds ~f:(fun (p : Pred.t) ->
            if Set.mem reached p.name then Some p.name else None)
      in
      let dup_origins =
        List.fold members ~init:Set.Poly.empty ~f:(fun acc a ->
            if
              List.exists members ~f:(fun b ->
                  Stdlib.(a <> b && origin a = origin b) && same_scc_er a b)
            then Set.add acc (origin a)
            else acc)
      in
      (* [splits]: also the original components with representatives in two distinct
         recursive components of [erased].  A member is recursive when it reaches itself by
         one or more calls. *)
      let dup_origins =
        if not splits then dup_origins
        else
          let reaches_self a =
            let rec go seen = function
              | [] -> false
              | q :: rest ->
                  let next =
                    Set.diff
                      (Option.value ~default:Set.Poly.empty
                         (Map.Poly.find callees q))
                      seen
                  in
                  Set.mem next a || go (Set.union seen next) (Set.to_list next @ rest)
            in
            go Set.Poly.empty [ a ]
          in
          let recursive = List.filter members ~f:reaches_self in
          List.fold recursive ~init:dup_origins ~f:(fun acc a ->
              if
                List.exists recursive ~f:(fun b ->
                    (not (same_scc_er a b))
                    && same_scc_orig (origin a) (origin b))
              then Set.add acc (origin a)
              else acc)
      in
      fun q -> Set.exists dup_origins ~f:(fun d -> same_scc_orig d q)

    (* One application of the erasure under [made_bodies], with its report.  Under [Hybrid]
       the run is repeated, each time also projecting the blocks the last run left
       [Uncovered], until no block is [Uncovered]; so every block of the output is projected
       (its made bodies are the projections of their sources' final bodies) or accepted by
       [classify].  It terminates within one run per original plus one: a projected block's
       members have empty difference sets, so it is never [Uncovered], and the projected set
       grows strictly.  The first run projects nothing, so where it leaves nothing
       [Uncovered] the output is [Copy_and_erase]'s.  With [COAR_ERASURE_CENSUS] set, one
       stderr line per application gives the blocks with a made predicate by class (the
       projected ones apart), the runs taken and the projected originals; it changes
       nothing. *)
    let run_mode ~keep_query_binder ~decline_scc ~made_bodies ~elim_forall
        ~elim_exists muclp =
      let order =
        List.map muclp.Problem.preds ~f:(fun (p : Pred.t) -> (p.name, p.kind))
      in
      let rec go rounds projected =
        let out, origin, made =
          run ~keep_query_binder ~decline_scc ~made_bodies
            ~project_origin:(Set.mem projected) ~elim_forall ~elim_exists muclp
        in
        let classes = classify ~order made in
        let uncovered =
          List.filter_map classes ~f:(function
            | o, Uncovered -> Some o
            | _ -> None)
        in
        match made_bodies with
        | (Opt.Hybrid | Hybrid_miniscoped) when not (List.is_empty uncovered) ->
            go (rounds + 1) (Set.union projected (Set.Poly.of_list uncovered))
        | _ ->
            let fallback =
              List.filter_map classes ~f:(fun (o, _) ->
                  if Set.mem projected o then Some o else None)
            in
            (if Option.is_some (Sys.getenv "COAR_ERASURE_CENSUS") then
               let count c =
                 List.count classes ~f:(fun (o, c') ->
                     Stdlib.(c = c') && not (Set.mem projected o))
               in
               eprintf
                 "erasure-census-cover: mode=%s blocks=%d exact=%d robust=%d \
                  fusion=%d uncovered=%d fallback=%d rounds=%d fallback_origins=%s\n%!"
                 (match made_bodies with
                 | Opt.Copy_and_erase -> "copy"
                 | Project_final -> "project"
                 | Hybrid -> "hybrid"
                 | Hybrid_miniscoped -> "hybrid-miniscoped")
                 (List.length classes) (count Exact) (count Robust) (count Fusion)
                 (count Uncovered) (List.length fallback) rounds
                 (String.concat ~sep:"," (List.map fallback ~f:Ident.name_of_pvar)));
            (out, origin, { order; made; classes; fallback; rounds })
      in
      go 1 Set.Poly.empty

    let optimize_report ?(keep_query_binder = false)
        ?(same_scc_calls = Opt.Erase_same_scc)
        ?(made_bodies = Opt.Copy_and_erase) ?(elim_forall = true)
        ?(elim_exists = true) muclp =
      let drop_origin (out, _, report) = (out, report) in
      match same_scc_calls with
      | Opt.Erase_same_scc | Keep_same_scc ->
          let keep = Stdlib.(same_scc_calls = Opt.Keep_same_scc) in
          drop_origin
          @@ run_mode ~keep_query_binder
               ~decline_scc:(fun _ -> keep)
               ~made_bodies ~elim_forall ~elim_exists muclp
      | (Keep_same_scc_if_grows | Keep_same_scc_if_grows_or_splits) as rule ->
          let erased, origin, report =
            run_mode ~keep_query_binder
              ~decline_scc:(fun _ -> false)
              ~made_bodies ~elim_forall ~elim_exists muclp
          in
          let splits = Stdlib.(rule = Opt.Keep_same_scc_if_grows_or_splits) in
          let grown = grown_sccs ~splits ~original:muclp ~erased ~origin () in
          if
            List.for_all muclp.Problem.preds ~f:(fun (p : Pred.t) ->
                not (grown p.name))
          then (erased, report)
          else
            drop_origin
            @@ run_mode ~keep_query_binder ~decline_scc:grown ~made_bodies
                 ~elim_forall ~elim_exists muclp

    let optimize ?keep_query_binder ?same_scc_calls ?made_bodies ?elim_forall
        ?elim_exists muclp =
      fst
        (optimize_report ?keep_query_binder ?same_scc_calls ?made_bodies
           ?elim_forall ?elim_exists muclp)
  end

  (* exists x. 0 <= x /\ x <= 100 -> true *)
  module CheckAndReplaceToTopOrBot : sig
    val optimize :
      id:int option -> ?timeout_milliseconds:int -> Problem.t -> Problem.t
  end = struct
    let bind_free_tvas_with_forall fml =
      let bounds = Set.to_list @@ Formula.term_sort_env_of fml in
      Formula.mk_forall_if_bounded bounds fml ~info:Dummy

    (* One Z3 context per optimisation pass, not per query: creating a context
       costs about nine milliseconds, and this pass asks two questions of every
       quantified subformula, so on a muCLP with a few dozen of them the
       context creation was 80% of the pass (0.32 s of 0.40 s, 35 questions).
       The solver is still fresh for every question. *)
    let gen_smt_solver ctx = Z3.Solver.mk_simple_solver ctx

    let check_always_true ~id ~ctx fml =
      if Fn.non Set.is_empty @@ Formula.pvs_of fml then false
      else (
        Debug.print @@ lazy "\n[optimize][check_always_true]";
        Debug.print @@ lazy (sprintf "input: %s" (Formula.str_of fml));
        (* x >= 10 -> forall (x: int). x >= 10 *)
        let fml = bind_free_tvas_with_forall fml in
        (* to smt format and solve it with z3 *)
        let solver = gen_smt_solver ctx in
        let fenv =
          Map.Poly.empty
          (*ToDo*)
          (*PCSP.Problem.fenv_of APCSP.problem*)
        in
        let dtenv =
          (* The datatypes have to be declared to the solver before a term over
             them is converted for it, and this used to pass the EMPTY set with
             the correct call commented out beside it.  A formula mentioning a
             constructor or a selector then ended the run in an uncaught
             failure naming a datatype that the input had declared perfectly
             well -- no verdict, a backtrace -- because the set the conversion
             searches had size zero.  A fixpoint-logic problem has no
             environment of its own to read, so the process-wide one is the
             source; whatever reduced a constraint problem to this one
             registers it there on the way in. *)
          Z3Smt.Z3interface.z3_dtenv_of_formula ctx fml
        in
        let expr = Z3Smt.Z3interface.of_formula ~id ctx [] [] fenv dtenv fml in
        Debug.print @@ lazy (sprintf "expr: %s" (Z3.Expr.to_string expr));
        try
          (* ALWAYS TRUE IS NOT SATISFIABLE.  The question asked here decides
             whether a subformula may be replaced by true, so it has to be
             "true in every model of the theory" -- which is the negation being
             unsatisfiable.  Asking whether the formula itself is satisfiable
             answers "true in SOME model", and the two part company exactly
             where the theory leaves a term open: a read outside a sequence, a
             selector on a datatype with several constructors, an uninterpreted
             function, a division.  A twenty-line input asserting that two
             out-of-range reads of different sequences agree is satisfiable and
             not valid, and it was being replaced by true, which turned a
             refutation into "satisfiable" for the whole problem.

             The caller's second arm is then right as it stands: a formula is
             always false exactly when its negation is always true.

             An undecided or failed query leaves the formula alone, which is
             the safe direction -- the replacement is an optimisation and not
             an obligation. *)
          let z3result =
            Z3.Solver.check solver [ Z3.Boolean.mk_not ctx expr ]
          in
          Debug.print
          @@ lazy
               (sprintf "Z3 on the negation: %s\n"
                  (Z3.Solver.string_of_status z3result));
          match z3result with Z3.Solver.UNSATISFIABLE -> true | _ -> false
        with Z3.Error reason ->
          (* timeout *)
          Debug.print @@ lazy (sprintf "Z3 Error: %s" reason);
          false)

    let rec replace_to_topbot ~id ~ctx = function
      | Formula.BinaryOp (op, phi1, phi2, info) ->
          Formula.mk_binop ~info op
            (replace_to_topbot ~id ~ctx phi1)
            (replace_to_topbot ~id ~ctx phi2)
      | Formula.UnaryOp (op, phi1, info) ->
          Formula.mk_unop ~info op (replace_to_topbot ~id ~ctx phi1)
      | Formula.Atom (_, _) as phi -> phi
      | Formula.Bind (binder, bounds, fml, info) as phi ->
          if check_always_true ~id ~ctx phi then Formula.mk_true ()
          else if check_always_true ~id ~ctx (Evaluator.simplify_neg phi) then
            Formula.mk_false ()
          else
            Formula.mk_bind binder bounds ~info
            @@ replace_to_topbot ~id ~ctx fml
      | _ -> failwith "replace_to_topbot"

    let optimize ~id ?(timeout_milliseconds = 1000) muclp =
      let ctx =
        Z3.mk_context [ ("timeout", string_of_int timeout_milliseconds) ]
      in
      Problem.map_formula (replace_to_topbot ~id ~ctx) muclp
  end

  module EraseConstVariables : sig
    val optimize :
      ?record:(Ident.pvar * Ident.tvar * Term.t) list ref ->
      Problem.t ->
      Problem.t
    (** [optimize ?record muclp] removes every argument position that receives the
        same constant at every application, substituting the constant for the
        parameter in the body.  With [record], each removed position is added to it
        as [(predicate, parameter, constant)]: the removed predicate's solution is
        the reduced one conjoined with [parameter = constant] (only tuples with
        that value at the position are ever reached), which is how a caller
        restores a solution over the original parameters. *)
  end = struct
    type vartype =
      | UnReached
      | ConstInt of Z.t
      | ConstReal of Q.t
      | ConstBool of bool
      | NonConst

    let merge_vt vt1 vt2 =
      match (vt1, vt2) with
      | UnReached, vt | vt, UnReached -> vt
      | ConstInt x, ConstInt y -> if Z.(equal x y) then ConstInt x else NonConst
      | ConstReal x, ConstReal y ->
          if Q.(equal x y) then ConstReal x else NonConst
      | ConstBool x, ConstBool y ->
          if Stdlib.(x = y) then ConstBool x else NonConst
      | _ -> NonConst

    let is_const = function
      | ConstInt _ -> true
      | ConstReal _ -> true
      | ConstBool _ -> true
      | _ -> false

    let string_of_vt = function
      | UnReached -> "unreached"
      | NonConst -> "nonconst"
      | ConstInt x -> sprintf "const %s" (Z.to_string x)
      | ConstReal x -> sprintf "const %s" (Q.to_string x)
      | ConstBool x -> sprintf "const %s" (Bool.to_string x)

    let seed = 1007

    let vt_of_pt ht_vt (pvar, tvar) =
      Hashtbl.Poly.(find_exn (find_exn ht_vt pvar) tvar)

    let init_ht_vt muclp =
      let ht_vt : (Ident.pvar, (Ident.tvar, vartype) Hashtbl.t) Hashtbl.t =
        Hashtbl.Poly.create ~size:seed ()
      in
      List.iter muclp.Problem.preds ~f:(fun pred ->
          let ht = Hashtbl.Poly.create ~size:seed () in
          List.iter pred.args ~f:(fun (tvar, _) ->
              Hashtbl.Poly.set ht ~key:tvar ~data:UnReached);
          Hashtbl.Poly.set ht_vt ~key:pred.name ~data:ht);
      ht_vt

    let rec nonconst_update ht_vt graph pt =
      let pvar, tvar = pt in
      Hashtbl.Poly.set
        (Hashtbl.Poly.find_exn ht_vt pvar)
        ~key:tvar ~data:NonConst;
      Hashtbl.Poly.find_exn graph pt
      |> List.iter ~f:(fun (nxt_pvar, nxt_tvar, _) ->
          let nxt_pt = (nxt_pvar, nxt_tvar) in
          let env = Hashtbl.Poly.find_exn ht_vt nxt_pvar in
          if Stdlib.( <> ) (Hashtbl.Poly.find_exn env nxt_tvar) NonConst then
            nonconst_update ht_vt graph nxt_pt)

    let rec vt_of_term env = function
      | Term.Var (tvar, _, _) ->
          if Hashtbl.Poly.mem env tvar then Hashtbl.Poly.find_exn env tvar
          else NonConst
      | Term.FunApp (funsym, args, _) -> (
          let arg_vts = List.map ~f:(vt_of_term env) args in
          if List.exists ~f:(Stdlib.( = ) NonConst) arg_vts then NonConst
          else if List.exists ~f:(Stdlib.( = ) UnReached) arg_vts then UnReached
          else
            match (funsym, arg_vts) with
            | T_bool.Formula (Formula.Atom (Atom.True _, _)), [] ->
                ConstBool true
            | T_bool.Formula (Formula.Atom (Atom.False _, _)), [] ->
                ConstBool false
            | T_int.Int x, [] -> ConstInt x
            | T_int.Neg, [ ConstInt x ] -> ConstInt (Z.neg x)
            | T_int.Nop, [ ConstInt x ] -> ConstInt x
            | T_int.Abs, [ ConstInt x ] -> ConstInt (Z.abs x)
            | T_int.Add, [ ConstInt x; ConstInt y ] -> ConstInt (Z.( + ) x y)
            | T_int.Sub, [ ConstInt x; ConstInt y ] -> ConstInt (Z.( - ) x y)
            | T_int.Mul, [ ConstInt x; ConstInt y ] -> ConstInt (Z.( * ) x y)
            | T_int.Div m, [ ConstInt x; ConstInt y ]
              when Z.Compare.(y <> Z.zero) ->
                ConstInt (Value.div_of m x y)
            | T_int.Rem m, [ ConstInt x; ConstInt y ]
              when Z.Compare.(y <> Z.zero) ->
                ConstInt (Value.rem_of m x y)
            | T_int.Power, [ ConstInt x; ConstInt y ] -> (
                (* not folded where the exponent is negative or too large for
                   the power to be computed: the term is then left as it is *)
                match Value.pow_of x y with
                | Some z -> ConstInt z
                | None -> NonConst)
            | T_real.Real x, [] -> ConstReal x
            | T_real.RNeg, [ ConstReal x ] -> ConstReal (Q.neg x)
            | T_real.RAbs, [ ConstReal x ] -> ConstReal (Q.abs x)
            | T_real.RAdd, [ ConstReal x; ConstReal y ] ->
                ConstReal (Q.( + ) x y)
            | T_real.RSub, [ ConstReal x; ConstReal y ] ->
                ConstReal (Q.( - ) x y)
            | T_real.RMul, [ ConstReal x; ConstReal y ] ->
                ConstReal (Q.( * ) x y)
            | T_real.RDiv, [ ConstReal x; ConstReal y ] ->
                ConstReal (Q.( / ) x y)
            | T_real.RPower, [ ConstReal _x; ConstReal _y ] ->
                NonConst
                (*ToDo*)
                (*ConstReal (Q.pow x y)*)
            | T_bv.BVNum (_, _), []
            | ( T_bv.(BVNot _ | BVNeg _ | BVEXTRACT _ | BVSEXT _ | BVZEXT _),
                [ _ ] )
            | ( T_bv.(
                  ( BVAnd _ | BVOr _ | BVXor _ | BVNand _ | BVNor _ | BVXnor _
                  | BVCONCAT _ | BVAdd _ | BVSub _ | BVMul _ | BVDiv _ | BVRem _
                  | BVSMod _ | BVSHL _ | BVLSHR _ | BVASHR _ )),
                [ _; _ ] ) ->
                NonConst (*ToDo*)
            | _ ->
                (* any other term (an embedded formula such as a Boolean
                   argument [x < c], a conditional term, ...) is read as not
                   constant: that only keeps the argument, so it is sound,
                   where refusing the term lost the problem's answer *)
                NonConst)
      | _ -> failwith "vt_of_term"

    let value_of_const_term term =
      match vt_of_term (Hashtbl.Poly.create ~size:seed ()) term with
      | ConstInt x -> ConstInt x
      | ConstReal x -> ConstReal x
      | ConstBool x -> ConstBool x
      | _ -> assert false

    let rec get_vargraph_rep (tvars_of_pvar : Ident.pvar -> Ident.tvar list)
        (pvar : Ident.pvar) arg_tvars consts nonconsts graph = function
      | Formula.UnaryOp (_, fml, _) ->
          get_vargraph_rep tvars_of_pvar pvar arg_tvars consts nonconsts graph
            fml
      | Formula.BinaryOp (_, fml1, fml2, _) ->
          let consts, nonconsts =
            get_vargraph_rep tvars_of_pvar pvar arg_tvars consts nonconsts graph
              fml1
          in
          get_vargraph_rep tvars_of_pvar pvar arg_tvars consts nonconsts graph
            fml2
      | Formula.Atom (Atom.App (Predicate.Var (pvar', _), args, _), _) ->
          List.zip_exn args (tvars_of_pvar pvar')
          |> List.fold_left ~init:(consts, nonconsts)
               ~f:(fun (consts, nonconsts) (arg, tvar') ->
                 let ftv = Term.tvs_of arg in
                 if Set.is_empty ftv then
                   try
                     ( (pvar', tvar', value_of_const_term arg) :: consts,
                       nonconsts )
                   with exn_ when not (Common.Timer.is_async exn_) ->
                     (* a ground argument whose value cannot be computed
                        (division by zero, ite, datatype constructors, select,
                        ...) is not known to agree with the other call sites'
                        values, so the position is not constant *)
                     (consts, (pvar', tvar') :: nonconsts)
                 else if Set.is_empty @@ Set.diff ftv arg_tvars then (
                   Set.iter (Set.inter ftv arg_tvars) ~f:(fun tvar ->
                       let pt = (pvar, tvar) in
                       let edges = Hashtbl.Poly.find_exn graph pt in
                       Hashtbl.Poly.set graph ~key:pt
                         ~data:((pvar', tvar', arg) :: edges));
                   (consts, nonconsts))
                 else (consts, (pvar', tvar') :: nonconsts))
      | Formula.Atom (_, _) -> (consts, nonconsts)
      | Formula.Bind (_, bounds, fml, _) ->
          let arg_tvars =
            Set.diff arg_tvars @@ Set.Poly.of_list @@ List.map ~f:fst bounds
          in
          get_vargraph_rep tvars_of_pvar pvar arg_tvars consts nonconsts graph
            fml
      | _ -> failwith "get_vargraph_rep"

    let tvars_of_pvar_of_muclp muclp =
      let tvars_of_pvar_ht = Hashtbl.Poly.create ~size:seed () in
      List.iter muclp.Problem.preds ~f:(fun pred ->
          Hashtbl.Poly.set tvars_of_pvar_ht ~key:pred.name
            ~data:(List.map ~f:fst pred.args));
      fun pvar -> Hashtbl.find_exn tvars_of_pvar_ht pvar

    let get_vargraph muclp =
      let dummy_pvar = Ident.Pvar "dummy" in
      let consts : (Ident.pvar * Ident.tvar * vartype) list = [] in
      let nonconsts : (Ident.pvar * Ident.tvar) list = [] in
      let graph :
          ( Ident.pvar * Ident.tvar,
            (Ident.pvar * Ident.tvar * Term.t) list )
          Hashtbl.Poly.t =
        Hashtbl.Poly.create ~size:seed ()
      in
      let tvars_of_pvar = tvars_of_pvar_of_muclp muclp in
      List.iter (Pred.pvars_of_list muclp.Problem.preds) ~f:(fun pvar ->
          List.iter (tvars_of_pvar pvar) ~f:(fun tvar ->
              Hashtbl.Poly.set graph ~key:(pvar, tvar) ~data:[]));
      let consts, nonconsts =
        List.fold_left muclp.Problem.preds
          ~init:
            (get_vargraph_rep tvars_of_pvar dummy_pvar Set.Poly.empty consts
               nonconsts graph muclp.Problem.query)
          ~f:(fun (consts, nonconsts) pred ->
            let arg_tvars = Set.Poly.of_list @@ List.map ~f:fst pred.args in
            get_vargraph_rep tvars_of_pvar pred.name arg_tvars consts nonconsts
              graph pred.body)
      in
      (consts, nonconsts, graph)

    let gen_ht_vt muclp =
      let ht_vt = init_ht_vt muclp in
      let consts, nonconsts, graph = get_vargraph muclp in
      if false then
        printf "nonconsts: %s\n"
          (String.concat_map_list ~sep:" "
             ~f:(fun (pvar, tvar) ->
               sprintf "(%s, %s)" (Ident.name_of_pvar pvar)
                 (Ident.name_of_tvar tvar))
             nonconsts);
      List.iter nonconsts ~f:(nonconst_update ht_vt graph);
      let queue = Queue.create () in
      let update_ht_vt pt const =
        let current_vt = vt_of_pt ht_vt pt in
        if Stdlib.(current_vt <> NonConst) then
          let new_vt = merge_vt current_vt const in
          if Stdlib.(new_vt <> current_vt) then (
            let pvar, tvar = pt in
            Hashtbl.Poly.set
              (Hashtbl.find_exn ht_vt pvar)
              ~key:tvar ~data:new_vt;
            if Stdlib.(new_vt = NonConst) then nonconst_update ht_vt graph pt
            else Queue.enqueue queue pt)
      in
      List.iter consts ~f:(fun (pvar, tvar, value) ->
          update_ht_vt (pvar, tvar) value);
      while Fn.non Queue.is_empty queue do
        let pt = Queue.dequeue_exn queue in
        let pvar, tvar = pt in
        if false then (
          printf "%s, %s: %s\n" (Ident.name_of_pvar pvar)
            (Ident.name_of_tvar tvar)
            (string_of_vt (vt_of_pt ht_vt pt));
          Out_channel.flush stdout);
        if Stdlib.(vt_of_pt ht_vt pt <> NonConst) then
          List.iter (Hashtbl.Poly.find_exn graph pt)
            ~f:(fun (nxt_pvar, nxt_tvar, term) ->
              let nxt_pt = (nxt_pvar, nxt_tvar) in
              let current_vt = vt_of_pt ht_vt nxt_pt in
              if Stdlib.(current_vt <> NonConst) then
                let env = Hashtbl.Poly.find_exn ht_vt pvar in
                (* it's ok *)
                match vt_of_term env term with
                | NonConst -> nonconst_update ht_vt graph nxt_pt
                | (ConstBool _ | ConstInt _ | ConstReal _) as con ->
                    update_ht_vt nxt_pt con
                | UnReached -> ())
      done;
      ht_vt

    let filter_nonconst_args tvars_of_pvar ht_vt =
      Formula.map_atom ~f:(function
        | Atom.App (Predicate.Var (pvar, sorts), args, info) ->
            let ht_vt_of_tvar = Hashtbl.Poly.find_exn ht_vt pvar in
            let args, sorts =
              List.zip_exn (List.zip_exn args sorts) (tvars_of_pvar pvar)
              |> List.filter
                   ~f:
                     (snd
                     >> Hashtbl.Poly.find_exn ht_vt_of_tvar
                     >> is_const >> not)
              |> List.map ~f:fst |> List.unzip
            in
            Formula.mk_atom @@ Atom.mk_pvar_app pvar sorts args ~info
        | atm -> Formula.mk_atom atm)

    let optimize ?record muclp =
      if false then (
        printf "[ReplaceConstVariables]\n";
        printf "Input: %s\n\n" (Problem.str_of muclp));
      let ht_vt = gen_ht_vt muclp in
      let tvars_of_pvar = tvars_of_pvar_of_muclp muclp in
      let query =
        filter_nonconst_args tvars_of_pvar ht_vt muclp.Problem.query
      in
      let preds =
        List.map muclp.Problem.preds ~f:(fun pred ->
            let ht_vt_of_tvar = Hashtbl.Poly.find_exn ht_vt pred.name in
            let subst =
              List.fold_left pred.args ~init:Map.Poly.empty
                ~f:(fun tsub (tvar, _) ->
                  match Hashtbl.Poly.find_exn ht_vt_of_tvar tvar with
                  | ConstBool x ->
                      Map.Poly.set tsub ~key:tvar ~data:(T_bool.make x)
                  | ConstInt x ->
                      Map.Poly.set tsub ~key:tvar ~data:(T_int.mk_int x)
                  | ConstReal x ->
                      Map.Poly.set tsub ~key:tvar ~data:(T_real.mk_real x)
                  | _ -> tsub)
            in
            Option.iter record ~f:(fun r ->
                Map.Poly.iteri subst ~f:(fun ~key ~data ->
                    r := (pred.name, key, data) :: !r));
            let kept (x, _) =
              not (is_const (Hashtbl.Poly.find_exn ht_vt_of_tvar x))
            in
            {
              pred with
              args = List.filter pred.args ~f:kept;
              (* the name table follows the positions when it describes them
                 one to one (the transition-system route's): without this a
                 predicate that lost a constant position kept a table one
                 longer than its arguments, and a consumer pairing the two
                 dropped the predicate *)
              arg_original_names =
                (if List.length pred.arg_original_names = List.length pred.args
                 then
                   List.filteri pred.arg_original_names ~f:(fun i _ ->
                       kept (List.nth_exn pred.args i))
                 else pred.arg_original_names);
              body =
                filter_nonconst_args tvars_of_pvar ht_vt
                @@ Formula.subst subst pred.body;
            })
      in
      Problem.make preds query
  end

  (* Removal of irrelevant argument positions.

     A set [irr] of argument positions [(P, k)] is irrelevant when, for each of them, the
     formal parameter [x_k] of [P] occurs free in [P]'s body only inside argument terms at
     positions that are themselves in [irr].  The greatest such set is computed by starting
     from every position and removing, until nothing changes, each position whose formal
     occurs free anywhere else (a constraint, a call at a kept position).

     Exactness, for least and greatest fixpoints alike and for any nesting: call an
     interpretation of the predicates invariant when each [P] gives the same truth value to
     two argument tuples that differ only at positions in [irr].  The invariant
     interpretations contain the least and the greatest interpretation and are closed under
     arbitrary pointwise meets and joins, so they form a complete sublattice; and the body
     operator maps invariant interpretations to invariant ones, because under an invariant
     interpretation a body's value does not depend on a formal that occurs only at
     irrelevant positions.  Hence every fixpoint approximant, and every nested fixpoint of
     the hierarchical solution, is invariant: an invariant [P] is determined by its value
     at the kept positions (every sort is nonempty), and the system that drops the
     positions, with each call's arguments at them removed, has exactly those restrictions
     as its solution.  A quantifier whose variables no longer occur after the removal is
     then vacuous over a nonempty sort and is dropped.

     The pass removes what quantifier erasure would otherwise reach by making a fresh
     predicate: a loop's self-call quantified over havocked variables that nothing reads
     becomes an unquantified call of a smaller predicate, so no copy of the recursion is
     made beside the original.

     It declines (returns the problem unchanged) on any formula it does not cover
     syntactically: a [let], a [let rec], a fixpoint predicate inside a formula, a random
     binder, or a predicate application inside an argument term.  It must run before any
     consumer that relies on the original arities, which is what [elim_pvar_args] guards. *)
  module EraseIrrelevantArgs : sig
    val optimize : Problem.t -> Problem.t
  end = struct
    exception Unsupported

    let dropped irr pvar =
      match Map.Poly.find irr pvar with Some s -> s | None -> Set.Poly.empty

    (* the free variables of [fml] that occur outside the argument terms at positions in
       [irr] *)
    let rec relevant irr fml =
      match fml with
      | Formula.Atom (Atom.App (Predicate.Var (pvar, _), args, _), _) ->
          let drop = dropped irr pvar in
          List.foldi args ~init:Set.Poly.empty ~f:(fun i acc arg ->
              if not (Set.is_empty (Term.pvs_of arg)) then raise Unsupported;
              if Set.mem drop i then acc else Set.union acc (Term.tvs_of arg))
      | Formula.Atom (Atom.App (Predicate.Fixpoint _, _, _), _) ->
          raise Unsupported
      | Formula.Atom (atm, _) ->
          if not (Set.is_empty (Atom.pvs_of atm)) then raise Unsupported;
          Atom.tvs_of atm
      | Formula.UnaryOp (_, f, _) -> relevant irr f
      | Formula.BinaryOp (_, f1, f2, _) ->
          Set.union (relevant irr f1) (relevant irr f2)
      | Formula.Bind ((Formula.Forall | Formula.Exists), bounds, f, _) ->
          Set.diff (relevant irr f) (Set.Poly.of_list (List.map ~f:fst bounds))
      | _ -> raise Unsupported

    let rec rewrite irr fml =
      match fml with
      | Formula.Atom (Atom.App (Predicate.Var (pvar, sorts), args, info), _) ->
          let drop = dropped irr pvar in
          if Set.is_empty drop then fml
          else
            let kept =
              List.filteri (List.zip_exn sorts args) ~f:(fun i _ ->
                  not (Set.mem drop i))
            in
            let sorts, args = List.unzip kept in
            Formula.mk_atom (Atom.mk_pvar_app ~info pvar sorts args)
      | Formula.Atom _ -> fml
      | Formula.UnaryOp (op, f, info) -> Formula.mk_unop ~info op (rewrite irr f)
      | Formula.BinaryOp (op, f1, f2, info) ->
          Formula.mk_binop ~info op (rewrite irr f1) (rewrite irr f2)
      | Formula.Bind (((Formula.Forall | Formula.Exists) as b), bounds, f, info)
        ->
          let f = rewrite irr f in
          let fvs = Formula.tvs_of f in
          let bounds = List.filter bounds ~f:(fun (x, _) -> Set.mem fvs x) in
          Formula.mk_bind_if_bounded ~info b bounds f
      | _ -> raise Unsupported

    (* the greatest set of irrelevant positions, as a map from a predicate to its
       irrelevant indices (0-based) *)
    let irrelevant muclp =
      let preds = muclp.Problem.preds in
      let init =
        Map.Poly.of_alist_exn
        @@ List.map preds ~f:(fun p ->
            (p.Pred.name, Set.Poly.of_list (List.init (List.length p.args) ~f:Fn.id)))
      in
      let rec loop irr =
        let irr' =
          List.fold preds ~init:irr ~f:(fun irr p ->
              let rel = relevant irr p.Pred.body in
              let drop = dropped irr p.name in
              let drop' =
                Set.filter drop ~f:(fun i ->
                    not (Set.mem rel (fst (List.nth_exn p.args i))))
              in
              Map.Poly.set irr ~key:p.name ~data:drop')
        in
        if
          List.for_all preds ~f:(fun p ->
              Set.length (dropped irr p.Pred.name)
              = Set.length (dropped irr' p.name))
        then irr
        else loop irr'
      in
      ignore (relevant init muclp.Problem.query : Ident.tvar_set);
      loop init

    let optimize muclp =
      try
        let irr = irrelevant muclp in
        if Map.Poly.for_all irr ~f:Set.is_empty then muclp
        else
          let preds =
            List.map muclp.Problem.preds ~f:(fun p ->
                let drop = dropped irr p.Pred.name in
                let keep i _ = not (Set.mem drop i) in
                {
                  p with
                  args = List.filteri p.args ~f:keep;
                  arg_original_names =
                    (if List.length p.arg_original_names = List.length p.args
                     then List.filteri p.arg_original_names ~f:keep
                     else p.arg_original_names);
                  body = rewrite irr p.body;
                })
          in
          Problem.make preds (rewrite irr muclp.Problem.query)
      with Unsupported -> muclp
  end

  let print_log = false

  (* With COAR_OPTIMIZER_STEP_TRACE set, every step prints one line to stderr saying
     whether its output prints differently from its input; set to [dump], a step that
     changes the problem also prints its input and its output; unset, [step] is the
     step. *)
  let step_trace = Option.is_some (Sys.getenv "COAR_OPTIMIZER_STEP_TRACE")

  let step_dump =
    Option.exists (Sys.getenv "COAR_OPTIMIZER_STEP_TRACE") ~f:(String.equal "dump")

  let step name g muclp =
    if step_trace then (
      let res = g muclp in
      let before = Problem.str_of muclp and after = Problem.str_of res in
      let same = String.equal before after in
      Out_channel.eprintf "[optimizer-step] %s %s\n%!" name
        (if same then "same" else "changed");
      if step_dump && not same then
        Out_channel.eprintf "[optimizer-step] %s before:\n%s\n[optimizer-step] %s after:\n%s\n%!"
          name before name after;
      res)
    else g muclp

  let f ?(id = None) ?(elim_forall = true) ?(elim_exists = true)
      ?(elim_pvar_args = true) ?erased_constants muclp =
    let simplify =
      Problem.map_formula
        Formula.(elim_redundant_quantifiers >> elim_let (*ToDo*))
    in
    Debug.set_id id;
    if config.enable then
      muclp
      |> step "one-point"
           (if config.one_point_quantifiers then OnePoint.problem else Fn.id)
      |> step "simplify" simplify
      |> (fun muclp ->
      if print_log then
        Debug.print @@ lazy ("simplified: " ^ Problem.str_of muclp);
      muclp)
      |> step "inline"
           (InlineExtension.optimize
              ~cycle_passthrough:config.inline_cycle_passthrough
              ~quantified:(fun m ->
                (* the predicates the quantifier erasure makes a quantified copy
                   of, in an erasure of the problem the next steps build without
                   this inlining, taking every same-component erasure: a
                   quantifier the
                   irrelevant-argument step or the erasure removes (a havoc
                   nothing reads, an assignment written as a quantified
                   equation) withholds nothing *)
                match config.quantifier_erasure with
                | Erase { keep_query_binder; same_scc_calls; made_bodies } ->
                    let m =
                      if config.elim_irrelevant_args && elim_pvar_args then
                        EraseIrrelevantArgs.optimize m
                      else m
                    in
                    (* every same-component erasure taken, so a quantifier the
                       configured rule would decline is still seen as a copy *)
                    ignore same_scc_calls;
                    (* the probe draws fresh predicate names; the counter is put
                       back so the problem built afterwards gets the names it
                       gets without the probe (the optimizer runs before any
                       solver domain starts, so nothing else draws meanwhile) *)
                    let names = Atomic.get Ident.pvar_count in
                    let _, report =
                      EraseQuantifiers.optimize_report ~keep_query_binder
                        ~same_scc_calls:Opt.Erase_same_scc ~made_bodies
                        ~elim_forall ~elim_exists m
                    in
                    Atomic.set Ident.pvar_count names;
                    let withheld =
                      Set.Poly.of_list
                        (List.concat_map report.made ~f:(fun r ->
                             [ r.EraseQuantifiers.source; r.origin ]))
                    in
                    Debug.print
                    @@ lazy
                         (sprintf "inline: withheld pass-through candidates: %s"
                            (String.concat ~sep:" "
                               (List.map ~f:Ident.name_of_pvar
                                  (Set.to_list withheld))));
                    withheld
                | No_erasure -> InlineExtension.quantified_occurrences m))
      |> (fun muclp ->
      if print_log then
        Debug.print @@ lazy ("\ninlined: " ^ Problem.str_of muclp);
      muclp)
      |> step "irrelevant-args"
           (if config.elim_irrelevant_args && elim_pvar_args then
              EraseIrrelevantArgs.optimize
            else Fn.id)
      |> step "erase-quantifiers" (match config.quantifier_erasure with
         | Erase { keep_query_binder; same_scc_calls; made_bodies } ->
             EraseQuantifiers.optimize ~keep_query_binder ~same_scc_calls
               ~made_bodies ~elim_forall ~elim_exists
         | No_erasure -> Fn.id)
      |> (fun muclp ->
      if print_log then
        Debug.print @@ lazy ("\nquantifiers eliminated: " ^ Problem.str_of muclp);
      muclp)
      |> step "unreached" EraseUnreachedPredicates.optimize
      |> step "const-args"
           (if elim_pvar_args then EraseConstVariables.optimize ?record:erased_constants
            else Fn.id)
      |> step "top-bot" (CheckAndReplaceToTopOrBot.optimize ~id)
      |> step "simplify-final" Problem.simplify
      |> step "inline-final"
           (InlineExtension.optimize
              ~cycle_passthrough:config.inline_cycle_passthrough)
    else muclp |> simplify
end

let make (config : Config.t) =
  (module Make (struct
    let config = config
  end) : OptimizerType)
