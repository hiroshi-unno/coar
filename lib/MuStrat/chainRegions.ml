(* The chain pairs a counter-play gives a ranking key, and the regions around
   them.  A play is the ground derivation a backend's counterexample records;
   a chain pair is the pair of states of two visits of a ranked predicate on
   one path of it with no reset between them, and its region is the set of
   pairs joined by a path of the same shape, by model-based projection of the
   path's clause instances (see [MbpRegion]).  The functions take what the
   strategy check holds per problem as arguments: [pred_index] maps each
   predicate's reduced name to its position in the equation list, [print] is
   the check's trace, and the two booleans are its configuration's choices. *)

open Core
open Common.Ext
open Ast

(* The ground play a Spacer derivation records: each node is the conclusion
   the derivation derives there (a predicate application to ground terms) and
   its premises.  Read only for the conclusions, so the clause structure that
   [analyze_cex] builds is not repeated here. *)
type play_node = {
  pvar : Ident.pvar;
  args : LogicOld.Term.t list;
  children : play_node list;
  clause : LogicOld.Formula.t;
      (** the clause the derivation applied to derive this node, as the
          derivation states it (universally closed, premises in the order of
          [children]) *)
}

(* A table keyed by a play node compared physically, hashed on its
   conclusion; per walk, never across walks. *)
let play_node_hash n = Stdlib.Hashtbl.hash_param 100 1000 (n.pvar, n.args)

(* The reduction's name of the predicate the ranking key [WF_P_] ranks, as
   it occurs in the checked side's clauses; [None] for a key not so named. *)
let rank_target_of wf_key =
  match
    String.chop_prefix (Ident.name_of_tvar wf_key) ~prefix:"WF_"
    |> Option.bind ~f:(String.chop_suffix ~suffix:"_")
  with
  | Some p -> Some (Ident.name_of_pvar @@ Ident.uninterp_pvar (Ident.Pvar p))
  | None -> None

(* The play [tree] with every revisit cut out, and the number of cuts.  A
   node whose [state_of] is [Some s] and below which, with no [resets] node
   in between, another node has state [s] is replaced by the lowest such
   node on the first branch that has one; the search repeats from the node
   put in its place, which has no [s] below it in its segment, and then
   descends.

   Contract.  (1) Every root-to-leaf path of the result is a subsequence of
   a path of [tree] that removes only a stretch between two visits at one
   state with no reset in it, so the reset structure of the pairs that
   remain is unchanged and the pairs read from the result are a subset of
   those read from [tree].  (2) On every path of the result, the states of
   the nodes between two consecutive resets are pairwise distinct.  (3) The
   result is a subtree-replacement of [tree]: a node's children are those
   of some node of [tree].  When the two visits carry the same ground atom
   (not only the same state) the result is again a derivation of the same
   conclusion; otherwise it is the play the ranked side makes by taking, at
   a repeated state, the move of its last visit there, which the real game
   admits because a call's position is its arguments.

   Why.  A ranking is disjunctively well-founded, so it contains no (s, s);
   and a path s, t, s with no reset asks it for (s, t) and (t, s), which no
   well-founded relation holds, so a one-piece ranking cannot be found and a
   union can be found only by splitting the cycle between two pieces. *)
let splice_revisits ~state_of ~resets tree =
  let cuts = ref 0 in
  (* the lowest node below [node] with state [st] on the first branch that
     has one, not crossing a reset *)
  let rec find_revisit st node =
    List.find_map node.children ~f:(fun child ->
        if resets child then None
        else
          match state_of child with
          | Some st' when Stdlib.( = ) st st' -> (
              match find_revisit st child with
              | Some lower -> Some lower
              | None -> Some child)
          | _ -> find_revisit st child)
  in
  let rec go node =
    match state_of node with
    | Some st -> (
        match find_revisit st node with
        | Some lower ->
            incr cuts;
            go lower
        | None -> { node with children = List.map node.children ~f:go })
    | None -> { node with children = List.map node.children ~f:go }
  in
  let tree = go tree in
  (tree, !cuts)

let chain_pairs_of ?nearest_only ~print ~pred_index ~splice_chain_revisits tree
    ~wf_key ~arity =
  let n = arity / 2 in
  match rank_target_of wf_key with
  | None -> []
  | Some target ->
      let state_of node =
        if
          String.(Ident.name_of_pvar node.pvar = target)
          && List.length node.args >= n
        then Some (List.drop node.args (List.length node.args - n))
        else None
      in
      let target_index = Hashtbl.find pred_index target in
      let resets node =
        match
          (target_index, Hashtbl.find pred_index (Ident.name_of_pvar node.pvar))
        with
        | Some ti, Some i -> i < ti
        | _ -> false
      in
      let tree =
        if splice_chain_revisits then (
          let tree, cuts = splice_revisits ~state_of ~resets tree in
          if cuts > 0 then
            print
            @@ lazy
                 (sprintf "## %d revisit(s) of %s cut out of the play" cuts
                    (Ident.name_of_tvar wf_key));
          tree)
        else tree
      in
      (* Without the cut, a pair (s, s) is a revisit, which no ranking
         contains; it is dropped and the rest of the cycle stays asked for.
         After the cut no path repeats a state within a segment, and the
         filter removes nothing. *)
      ChainPairs.pairs ?nearest_only
        ~children:(fun node -> node.children)
        ~hash:play_node_hash ~state_of ~resets tree

(* For the ranking key [wf_key], the chain pairs of the play [tree] (as
   [chain_pairs_of] reads them, without the revisit cut) each stated as a
   REGION: the list of [((s, t), (vars, region))], where [vars] are fresh
   variables for the two states (the upper visit's first, then the lower
   visit's, [arity] of them in all, in the key's parameter order) and
   [region] a quantifier-free formula over [vars].

   How a region is formed.  Let [u = n_0, n_1, .., n_k = v] be the path of
   the derivation from the visit at [s] down to the visit at [t].  Each
   [n_i] ([i < k]) was derived by one clause instance whose head is [n_i]'s
   atom and one of whose premises is [n_{i+1}]'s; the conjunction of these
   instances, with fresh variables [x_i] for every node's arguments, is the
   path condition.  A premise off the path is dropped, except that when it
   is an application of one of [decisions] (the dummies naming the ranked
   side's own decisions, whose last argument is the value decided) that
   value is fixed at the one the play took, so the region is the steps the
   ranked side makes by repeating its move, under every choice of the
   checked side's universals.  The path condition is then projected onto
   the states of [x_0] and [x_k] by model-based projection, at the model
   assigning every [x_i] the play's arguments.  [passed ~visit node x_i]
   adds, for each [n_i] ([i < k]; [visit] says whether [n_i] is a visit of
   the ranked predicate), conditions over [x_i] that hold at the play's
   arguments of [n_i] (the losing conditions of the alternatives the ranked
   side passed over there, see [PassedChoices]); they only narrow the path
   condition, so the region they give is a subset of the one without them
   and still contains [(s, t)].

   Contract.  (1) [region] holds at [(s, t)]: a region the ground pair does
   not satisfy is discarded, which the projection's own postcondition makes
   unreachable.  (2) [region] implies the existential closure of the path
   condition, so every pair in it is joined by a path of this shape.  (3) A
   pair whose path cannot be read (a clause not of the implication shape,
   premises not matching the node's children), whose projection raises, or
   whose region is [true] or mentions no variable, gets no entry: its
   ground pair is still asked by the caller.  Nothing here decides an
   answer: the regions only constrain a copy the strategy check judges.

   With [by_mbp] the side premises are kept instead of dropped: a premise
   off the path that is not a named decision contributes the clause
   instances of its whole derivation in the play (fresh variables for each
   node's arguments, the play's arguments for them in the model), up to
   [side_node_budget] nodes per segment, past which it is dropped as
   without [by_mbp]; and [passed] is read only at the visits of the ranked
   predicate.  Then (2) strengthens to: every pair of [region] is the pair
   of end states of a fragment of a derivation in the check's clauses whose
   named decisions take the play's values -- a step a play of the check
   can make -- whenever no side derivation was dropped, since the
   projection's input is then the full conjunction of the instances of a
   derivation fragment and the projection implies its existential
   closure. *)
(* Under [chain_pair_regions_by_mbp]: the most nodes of side derivations
   one region's segment takes in; a side premise whose derivation would pass
   it is dropped from that region, as without the field every side premise
   is.  The derivations seen are a few nodes each (named decisions and term
   alternatives are leaves or one clause above one); the bound only keeps a
   deep side derivation from making one projection the cost of the
   refinement. *)
let side_node_budget = 64

(* [chain_regions_of ... tree ~wf_key ~arity]: per chain pair of [tree] for
   the ranking key [wf_key], the pair and its region [(vars, region, cert)]:
   the two visits' states [vars] (the upper visit first), a quantifier-free
   formula over them, and [cert], [None] for a region with a linear ranking
   (or one the test does not decide), or, under [multiphase_depth] above 1,
   [Some (len, fs)] for a region with no linear ranking that has a nested
   ranking [fs] (see [RankingCheck.region_nested_ranking]) of the least
   depth up to [multiphase_depth], [len] being the number of steps of the
   segment the region was read from.  A region with neither is left out. *)
(* One line on stderr per firing of a warehouse repair, when
   COAR_MUSTRAT_TIMELINE is set: what proves a run read the field, printed
   at once since a run stopped at its budget runs no exit handler *)
let repair_log =
  let on = Option.is_some (Sys.getenv "COAR_MUSTRAT_TIMELINE") in
  fun msg -> if on then eprintf "mustrat-repairs: %s\n%!" msg

(* Two hooks for a measurement instrument, both absent on every solving
   path.  [bind_decision phi child], when given, states a premise naming one
   of [decisions] instead of fixing its value at the play's: [Some fs] puts
   [fs] in the path condition (the instrument binds the decision to the
   strategy's terms at the premise's arguments).  [observe], when given,
   receives each segment's ground pair, the two visits' state variables and
   its path condition, before any projection, and the segment then gets no
   region: the function returns the empty list and asks no projection.
   [bind_step node i xs xs'], when given, may state a whole step of the path
   instead of the clause instance that derived [node]: [Some fs] puts [fs]
   in the path condition in place of [node]'s head equations over [xs], its
   pure part, its side premises and its [i]-th premise's equations with the
   next node's variables [xs'] (the instrument states the ranked side's
   choice between alternative clauses there); [None] keeps the instance. *)
let chain_regions_of ~print ~pred_index ~drop_implied
    ?(passed = fun ~visit:_ _ _ -> []) ?(by_mbp = false)
    ?(problem_sides_only = false) ?(multiphase_depth = 1) ?(window = 0)
    ?(window_min_pairs = 0) ?(window_key = false) ?bind_decision ?bind_step
    ?observe ~decisions tree ~wf_key ~arity =
  let open Ast.LogicOld in
  let n = arity / 2 in
  match rank_target_of wf_key with
  | None -> []
  | Some target ->
      let state_of node =
        if
          String.(Ident.name_of_pvar node.pvar = target)
          && List.length node.args >= n
        then Some (List.drop node.args (List.length node.args - n))
        else None
      in
      let target_index = Hashtbl.find pred_index target in
      let resets node =
        match
          (target_index, Hashtbl.find pred_index (Ident.name_of_pvar node.pvar))
        with
        | Some ti, Some i -> i < ti
        | _ -> false
      in
      (* every chain pair with the path segment that asks it, upper visit
         first, each node with its index among its parent's children (see
         [ChainPairs.pair_segments]); the same traversal as
         [chain_pairs_of] *)
      let skipped = ref 0 in
      let t0 = Common.Clock.now_float () in
      let segments_of window =
        let segments, sk =
          ChainPairs.pair_segments ~window_key ~window
            ~children:(fun node -> node.children)
            ~hash:play_node_hash ~state_of ~resets tree
        in
        skipped := !skipped + sk;
        segments
      in
      (* [window_min_pairs] above 0: the window is used only when the play
         asks more distinct chain pairs than that.  On a short play every
         region costs little, and the long cubes the window drops can be
         the demand that steers the fit (a three-visit segment fitted over
         its adjacent cubes alone gave a ranking that lost the next check
         and cost two more rounds).  The traversal without the window
         builds no region, so the count costs one walk of the play. *)
      let window =
        ChainPairs.effective_window ~window ~min_pairs:window_min_pairs
          ~pairs:(lazy (List.length (segments_of 0)))
      in
      let segments = segments_of window in
      (* [certify xs ys region]: the ranking tests of a projected region
         ([xs] the upper visit's state variables, [ys] the lower one's, the
         region's free variables among them): [`Plain] when the region is not
         shown to have no linear ranking, otherwise [`Nested (Some fs)] for
         the least depth from 2 up to [multiphase_depth] with a nested
         ranking [fs], or [`Nested None] when there is none.  Both tests read
         the region positionally (the coefficients of [fs] are by position
         in [xs]), so the outcome is a function of the region with [xs] and
         [ys] renamed to their positions, and it is computed once per such
         region in this call.  Why: on a deterministic loop each visit's
         region is the loop's step at another point of one long play, and
         1,500 regions of one play were 2 regions up to that renaming, where
         each test is a linear program asked of Z3 (3,000 questions, 12 s).
         A test that does not decide in its budget is not asked again, which
         a recomputation might decide; either answer is sound, since a region
         only adds a demand to the ranking search. *)
      let certified = Common.Ext.Hashtbl.PolyDeep.create () in
      let certify xs ys region =
        let kept = xs @ ys in
        let key =
          ( List.map kept ~f:snd,
            Formula.rename
              (Map.Poly.of_alist_exn
                 (List.mapi kept ~f:(fun i (v, _) ->
                      (v, Ident.Tvar (sprintf "#region_pos%d" i)))))
              region )
        in
        match Hashtbl.find certified key with
        | Some outcome -> outcome
        | None ->
            let outcome =
              if
                Stdlib.( = )
                  (RankingCheck.region_has_linear_ranking xs ys region)
                  (Some false)
              then
                (* the least depth from 2 with a nested ranking, if any *)
                let rec nested d =
                  if d > multiphase_depth then None
                  else
                    match
                      RankingCheck.region_nested_ranking ~depth:d xs ys region
                    with
                    | `Ranking fs -> Some fs
                    | `Infeasible | `Undecided -> nested (d + 1)
                in
                `Nested (nested 2)
              else `Plain
            in
            Hashtbl.set certified ~key ~data:outcome;
            outcome
      in
      let region_of steps =
        (* [steps]: the segment's nodes, each with its index among its
           parent's children; the next node of the path is the premise at
           that index (two children of a node can be one shared node, so
           the index, not the node, says which premise the path takes) *)
        let path = List.map steps ~f:fst in
        (* Under [by_mbp], the side derivations below the path are kept:
           their nodes' fresh variables and the play's arguments for them,
           filled in by [instances] and read by the model below. *)
        let side_model = ref [] in
        let side_budget = ref side_node_budget in
        let vars =
          List.map path ~f:(fun node ->
              List.map node.args ~f:(fun arg ->
                  ( Ident.mk_fresh_tvar ~prefix:(Some "GP_") (),
                    Term.sort_of arg )))
        in
        let eqs ts vs =
          List.map2_exn ts vs ~f:(fun t (v, s) -> Formula.eq t (Term.mk_var v s))
        in
        let atom_args phi =
          match fst (Formula.let_atom phi) with
          | Atom.App (Predicate.Var (pvar, _), args, _) -> (pvar, args)
          | _ -> raise Exit
        in
        (* the clause instance that derived [node], its variables renamed
           apart: the head's equations with [xs] and the pure conjuncts, and
           the premises paired with the children that derived them.  A fact
           stated as a bare atom has no premise and no pure part. *)
        let parts node xs =
          let senv, body =
            if Formula.is_forall node.clause then
              let senv, body, _ = Formula.let_forall node.clause in
              (senv, body)
            else ([], node.clause)
          in
          let body =
            Formula.rename
              (Map.Poly.of_alist_exn
              @@ List.map senv ~f:(fun (x, _) ->
                  (x, Ident.mk_fresh_tvar ~prefix:(Some "GC_") ())))
              body
          in
          let ant, con =
            if Formula.is_imply body then
              let ant, con, _ = Formula.let_imply body in
              (Formula.conjuncts_list_of ant, con)
            else if by_mbp && Formula.is_atom body then ([], body)
            else raise Exit
          in
          let premises, pure =
            List.partition_tf ant ~f:(fun phi ->
                Formula.is_atom phi
                && Atom.is_pvar_app (fst (Formula.let_atom phi)))
          in
          if List.length premises <> List.length node.children then
            raise Exit;
          let _, head_args = atom_args con in
          if List.length head_args <> List.length xs then raise Exit;
          (eqs head_args xs, pure, List.zip_exn premises node.children)
        in
        (* a premise naming one of the ranked side's decisions: its result
           fixed at the value the play took, [None] for any other premise *)
        let decision_eq phi child =
          let pvar, args = atom_args phi in
          if
            Set.mem decisions (Ident.name_of_pvar pvar)
            && (not (List.is_empty args))
            && List.length args = List.length child.args
          then
            match bind_decision with
            | None ->
                Some
                  [ Formula.eq (List.last_exn args) (List.last_exn child.args) ]
            | Some bind -> bind phi child
          else None
        in
        (* Under [by_mbp]: the instances of the whole derivation of [child]
           (a side premise [phi] off the path), with fresh variables for
           every node's arguments, recorded in [side_model] with the play's
           values.  Raises [Exit] past the node budget; the caller then
           drops the premise. *)
        (* The checked side's strategy values kept as variables in one
           clause instance ([FreedValues]): the variables of the last
           argument of each premise that defines one.  A premise naming a
           value's definition is dropped from a region, so the value ranges
           freely; and so is every other side premise whose arguments
           mention such a value, since its derivation holds only at the
           value the play took (a branch closed by a base case at the
           opponent's constant) and kept, it would fix the value again.
           Both are empty without the field, which draws no definition. *)
        let is_tag child = FreedValues.is_tag (Ident.name_of_pvar child.pvar) in
        let freed_of prems =
          Set.Poly.union_list
            (List.filter_map prems ~f:(fun (phi, child) ->
                 if is_tag child then
                   Option.map (List.last (snd (atom_args phi))) ~f:Term.tvs_of
                 else None))
        in
        let mentions freed phi =
          (not (Set.is_empty freed))
          && List.exists (snd (atom_args phi)) ~f:(fun t ->
                 not (Set.is_empty (Set.inter (Term.tvs_of t) freed)))
        in
        let freed_drops = ref 0 in
        let rec side freed phi child =
          match decision_eq phi child with
          | Some fixed -> fixed
          | None when is_tag child || mentions freed phi ->
              incr freed_drops;
              []
          | None
            when problem_sides_only
                 && not
                      (Hashtbl.mem pred_index (Ident.name_of_pvar child.pvar))
            ->
              (* an auxiliary node (a term alternative's name, a Skolem
                 dummy): its clause bodies hold the checked side's strategy
                 constants, which would bound the region at the play's
                 values; the premise is dropped as without [by_mbp] *)
              []
          | None ->
              if !side_budget <= 0 then raise Exit;
              decr side_budget;
              let _, args = atom_args phi in
              if List.length args <> List.length child.args then raise Exit;
              let zs =
                List.map child.args ~f:(fun arg ->
                    ( Ident.mk_fresh_tvar ~prefix:(Some "GS_") (),
                      Term.sort_of arg ))
              in
              side_model :=
                List.map2_exn zs child.args ~f:(fun (v, _) t -> (v, t))
                @ !side_model;
              let head_eqs, pure, prems = parts child zs in
              let freed' = freed_of prems in
              eqs args zs @ head_eqs @ pure
              @ List.concat_map prems ~f:(fun (phi', grand) ->
                  side freed' phi' grand)
        in
        let rec instances = function
          | ((node, _), xs) :: (((_, next_idx), xs') :: _ as rest) -> (
              match
                Option.bind bind_step ~f:(fun f -> f node next_idx xs xs')
              with
              | Some fs -> fs @ instances rest
              | None ->
              let head_eqs, pure, prems = parts node xs in
              let freed = freed_of prems in
              let premise_eqs =
                List.concat_mapi prems ~f:(fun i (phi, child) ->
                    if i = next_idx then (
                      let _, args = atom_args phi in
                      if List.length args <> List.length xs' then raise Exit;
                      eqs args xs')
                    else
                      match decision_eq phi child with
                      | Some fixed -> fixed
                      | None when is_tag child || mentions freed phi ->
                          incr freed_drops;
                          []
                      | None when by_mbp -> (
                          let saved = !side_model in
                          try side freed phi child
                          with Exit ->
                            side_model := saved;
                            print
                            @@ lazy
                                 (sprintf
                                    "## a side derivation of %s past the \
                                     node budget is dropped from a region"
                                    (Ident.name_of_tvar wf_key));
                            [])
                      | None -> [])
              in
              (* [by_mbp] reads the passed-over alternatives only at the
                 visits of the ranked predicate: at an auxiliary node (a
                 term alternative's name) the conditions are the checked
                 side's strategy constants, which slice the region *)
              let visit = Option.is_some (state_of node) in
              let passed_here =
                if by_mbp && not visit then [] else passed ~visit node xs
              in
              (head_eqs @ premise_eqs @ pure @ passed_here) @ instances rest)
          | _ -> []
        in
        let phi = Formula.and_of (instances (List.zip_exn steps vars)) in
        let states xs = List.drop xs (List.length xs - n) in
        let kept = states (List.hd_exn vars) @ states (List.last_exn vars) in
        let model =
          Map.Poly.of_alist_exn
          @@ !side_model
          @ List.concat
              (List.map2_exn path vars ~f:(fun node xs ->
                   List.map2_exn xs node.args ~f:(fun (v, _) t -> (v, t))))
        in
        (* A region the ranking must contain is useless when it is not
           well-founded itself: the re-synthesis then has no solution and
           its budget is spent before the ground attempt runs.  Projection
           can drop the floor that made the play's chain finite, so a region
           with no linear ranking is dropped (the ground pair stays asked). *)
        let xs = states (List.hd_exn vars) and ys = states (List.last_exn vars) in
        match observe with
        | Some f ->
            f (List.hd_exn path, List.last_exn path) xs ys phi;
            None
        | None ->
        if by_mbp then
          print
          @@ lazy
               (sprintf "## a region of %s over %d side-derivation node(s)"
                  (Ident.name_of_tvar wf_key)
                  (side_node_budget - !side_budget));
        let result =
        match MbpRegion.project ~model ~kept phi with
        | None ->
            print @@ lazy "## region dropped (not a region)";
            None
        | Some region ->
            (* [chain_pair_region_drop_implied]: the same set of pairs,
               stated by fewer conjuncts *)
            let region =
              if drop_implied then (
                let before = List.length (Formula.conjuncts_list_of region) in
                let region' = MbpRegion.drop_implied region in
                let after = List.length (Formula.conjuncts_list_of region') in
                repair_log
                  (sprintf "region %s conjuncts %d kept %d"
                     (Ident.name_of_tvar wf_key) before after);
                print
                @@ lazy
                     (sprintf "## region of %s: %d conjunct(s), %d kept"
                        (Ident.name_of_tvar wf_key) before after);
                region')
              else region
            in
            match certify xs ys region with
            | `Nested (Some fs) -> (
                  print
                  @@ lazy
                       (sprintf
                          "## region with no linear ranking kept with a \
                           multiphase ranking of depth %d (%s): %s"
                          (List.length fs)
                          (RankingCheck.str_of_components fs)
                          (Formula.str_of region));
                  Some (kept, region, Some (List.length path - 1, fs)))
            | `Nested None ->
                  print
                  @@ lazy
                       (sprintf
                          "## region dropped (no linear ranking, or not a \
                           region): %s"
                          (Formula.str_of region));
                  None
            | `Plain -> Some (kept, region, None)
        in
        if !freed_drops > 0 then
          FreedValues.log
            (sprintf "region key=%s premises=%d %s"
               (Ident.name_of_tvar wf_key) !freed_drops
               (if Option.is_some result then "kept" else "dropped"));
        result
      in
      let regions =
        List.filter_map segments ~f:(fun (pair, path) ->
            match region_of path with
            | Some r -> Some (pair, r)
            | None -> None
            | exception exn_ when not (Common.Timer.is_async exn_) ->
                print
                @@ lazy
                     (sprintf "## no region for a chain pair of %s: %s"
                        (Ident.name_of_tvar wf_key) (Exn.to_string exn_));
                None)
      in
      ChainPairs.log
        (sprintf "regions key=%s window=%d segments=%d skipped=%d kept=%d secs=%.2f"
           (Ident.name_of_tvar wf_key) window (List.length segments) !skipped
           (List.length regions)
           (Time_float.Span.to_sec (Time_float.diff (Common.Clock.now_float ()) t0)));
      regions

