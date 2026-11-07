open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld

(* What an argument position that a reduction PREPENDS to a predicate holds.
   The disjunctively well-founded reduction of a least-fixpoint predicate [P]
   gives [P] and the members of its component a fresh copy of [P]'s parameters
   (the remembered earlier visit, one [Copy] per parameter), and a member called
   from outside the component also a Boolean flag ([Flag], true once [P] has
   been visited since the component was entered).  The copy is chosen by the
   refuting side among the visited states, so it is not a function of the play
   history; the flag is.  Positions a predicate had before the reduction are not
   listed: they are always the LAST ones, in their original order. *)
type prefix_entry = Copy | Flag

(* The rewrites [elim_nu] applies to each equation and to the query -- the
   simplifier and the clausal form -- recorded as pairs (formula before,
   conjunction of the universally closed clauses after) while
   [with_recorded_rewrites] runs, so that a caller can check each pair is an
   equivalence instead of trusting the two rewrites.  The recorder is one
   process-wide slot: only a caller in a single domain may use it, and a
   reduction run in another domain meanwhile would add its pairs too (which
   would only add questions, never remove one). *)
let rewrite_recorder : (Formula.t * Formula.t) list ref option ref = ref None

let record_rewrite before after_clauses =
  Option.iter !rewrite_recorder ~f:(fun r ->
      r := (before, Formula.and_of after_clauses) :: !r)

(* [with_recorded_rewrites f]: [f ()] and the rewrites recorded while it ran,
   in the order they were made. *)
let with_recorded_rewrites f =
  let r = ref [] in
  let saved = !rewrite_recorder in
  rewrite_recorder := Some r;
  Exn.protect
    ~finally:(fun () -> rewrite_recorder := saved)
    ~f:(fun () ->
      let res = f () in
      (res, List.rev !r))

module Config = struct
  (* When a component's loop-hierarchy priorities ([loop_levels]) take effect. *)
  type loop_levels_from =
    | Reduction
        (** from the start: the component's family is generated with the
            loop-hierarchy priorities *)
    | First_shape_failure
        (** the family starts with alternation depth's priorities and moves to
            the loop-hierarchy ones the first time the search finds no
            relation of the template's shape and would grow it; the move takes
            the place of that growth.  The examples learned so far are kept:
            on a component with no greatest fixpoint a cycle of the family's
            tags is refuted under the one priority function exactly when it is
            under the other, and every other example is a fact of the clauses.
            A component whose two priority functions coincide does not move.
            The intent: alternation depth's single component wins where one
            strict decrease per call suffices or where a refutation is found
            early with it, the loop levels where a nested loop needs a
            component per level; a family that fails its first shape is of the
            second kind more often than not, and loses only the first round's
            search when it is not. *)
    | First_rankable_shape_failure
        (** as [First_shape_failure], except that a shape failure takes the
            move only while the component's transitions, read off the
            clauses with every other unknown dropped, are not known to lack a
            lexicographic linear ranking function under the loop-hierarchy
            priorities' strictness; when they lack one the family keeps
            alternation depth's priorities for the whole run.  What the loop
            levels add is a ranking component per nested loop, which helps
            only a ranking the transitions can carry; a component whose bare
            transitions carry none needs invariants they do not have, or does
            not terminate, and moving it to the wider template delays the
            search alternation depth was making (on a non-terminating input
            the refutation it would have found).  The test is exact for its
            class and reads the clauses only, so it is asked once per family. *)
    | Reduction_unless_unrankable
        (** as [Reduction] (the loop-hierarchy priorities from the start),
            except that a family whose transitions, read off the clauses with
            every other unknown dropped, are known to lack a lexicographic
            linear ranking function under those priorities' strictness is
            moved to alternation depth's priorities before its first
            template, and keeps them for the run.  The test is
            [First_rankable_shape_failure]'s, asked at the start instead of
            at a shape failure: it reads the clauses only, so its answer
            does not depend on the search, and asking it early spares a
            rankable family the rounds alternation depth's narrower template
            spends before its first shape failure (a nested loop that needs
            a component per level fails alternation depth's first shape and
            then starts its search again), while an unrankable family -- one
            whose ranking needs invariants, or that does not terminate --
            keeps the single component in which the refutation is found
            earliest.  A family whose two priority functions coincide carries
            no switch and is the [Reduction] family. *)
  [@@deriving yojson]

  type fixpoint_reduction =
    | Wf_reduction of {
        restrict_ranking_to_cycles : bool; [@default true]
        record_on_head : bool; [@default false]
        one_relation_per_block : bool; [@default false]
      }
        (** one well-foundedness unknown per least-fixpoint predicate [pred], with copies
            of [pred]'s arguments threaded through the predicates that may call it back.
            The predicates already reduced (by now all greatest fixpoints) are its
            candidate callees; the graph the field consults is the call graph restricted
            to [pred] and them, its transitive closure taken, the one
            within which the reduction ranks a path from [pred] back to [pred] in either
            mode (a call from any other predicate re-enters [pred] unranked in both).

            [restrict_ranking_to_cycles] uses the ranking machinery only for what lies on
            a cycle with [pred] in that graph; the graph is not decomposed into strongly
            connected components (that is the parity progress measure's [use_scc]).  It
            has three effects, each of which removes only machinery no path from [pred]
            back to [pred] uses, so the reduced problem is equisatisfiable with the one
            [false] builds (an argument, not a written proof):
            - only the predicates mutually reachable with [pred] (its own component)
              receive the copies and are treated as mutually recursive with it: a
              callee that cannot reach [pred], or that [pred] cannot reach, is on no
              such path, so the copies it would carry are never compared;
            - the well-foundedness unknown (and, under [use_dwf], [pred]'s own copies)
              is added only when [pred] lies on a cycle: otherwise no call of [pred] is
              reached from [pred] itself, the unknown is constrained only under a
              call-origin flag that is false at every call, and the least and greatest
              fixpoints of a definition that does not recurse through [pred] coincide;
            - a member of the component that is not called from outside it (from the
              query, from the predicates not yet eliminated, or from a predicate off the
              component) gets no call-origin Boolean argument: every call to it carries
              [pred]'s current arguments, so the flag would be true at every call and
              the guard it enables holds unconditionally.
            [false] treats every earlier predicate as mutually recursive with [pred],
            adds the unknown always and passes the flag to every member.

            [record_on_head] keeps the copies of [pred]'s arguments on [pred] itself
            whenever [pred] alone cuts every cycle of its component, that is, when the
            members' calls among themselves form no cycle (read only with
            [restrict_ranking_to_cycles] and without [use_dwf]).  The members' definitions
            are then unfolded into [pred]'s body until only calls of [pred] and of
            predicates off the component remain, each call of [pred] carrying the
            well-foundedness guard between [pred]'s own parameters and the call's
            arguments; the members keep their original definitions and arities, which
            is what the members called with a false flag computed.  No predicate carries
            a copy or a flag, so no unknown left after predicate elimination can carry a
            dummy copy from an entry that bypassed [pred], and [pred], the only predicate
            left on the cycle, cannot be resolved away.  Equivalent to the flagged
            encoding: unfolding a definition into another equation of the same
            greatest-fixpoint block changes no solution, and the flag is true at every
            call [pred]'s body makes.  When the members do form a cycle the flagged
            encoding is used.  The unfolded body is a copy of every path through the
            members, so its size is the number of such paths.

            [one_relation_per_block] reduces a maximal run of consecutive
            least-fixpoint equations (a block) at once whenever at least two of
            them must keep a ranking, with ONE well-foundedness unknown over
            tagged records instead of one unknown per ranked predicate: the
            record of a ranked predicate's state is an integer tag naming the
            predicate followed by its arguments, sorted into per-sort slots as
            many as the widest ranked predicate has of that sort, unused slots
            holding a constant.  A member of the block's component then carries
            one flag and one record instead of one flag and one copy list per
            ranked predicate whose component holds it.  This is the shape of a
            parity progress measure (one coordinate per priority, not per
            predicate).  Read only with [restrict_ranking_to_cycles], without
            [use_dwf] and when greatest fixpoints are not converted; a block
            with fewer than two ranked predicates is reduced as without it, so
            [record_on_head] still applies there.  See [ufp_of_block] for the
            encoding and why it is sound. *)
    | Parity_progress_measure of {
        use_scc : bool; [@default true]
            (** decompose the call graph into strongly connected components and build
                one ranking family per component, rather than one for the whole
                problem *)
        alternation_depth : bool; [@default true]
            (** compare a priority only with the priorities of the same alternation depth,
                rather than all of them in one ranking *)
        pack_rank_components : bool; [@default true]
            (** with [alternation_depth], pack the ranking components in pairs, so that a
                family compares ceil((amax+1)/2) components and a priority [p] is compared at
                component ceil(p/2) (Kura and Unno, "Solving First-Order Fixed-Point Logics
                via a Least-to-Greatest Transformation Based on Game Semantics", Def. 7.8).
                Expressiveness is unchanged; acceptance is still decided by the parity of
                [p].  On by default, matching that definition; [false] is the unpacked form
                (Def. 7.7, one component per priority).  Read only when [alternation_depth]
                holds. *)
        loop_levels : bool; [@default true]
            (** with [alternation_depth], a component with no greatest-fixpoint
                predicate takes its priorities from its loop hierarchy instead: the
                first least-fixpoint predicate of a nested strongly connected
                component is its head and decreases strictly within as many ranking
                components as its nesting depth, and the other predicates of that
                component only non-strictly.  Alternation depth gives such a component
                one ranking component with a strict decrease on every call, so a nested
                loop needed the template's own lexicographic growth; this gives it a
                component per nesting level from the start.  It departs from the
                published reassignment (Kura and Unno, Def. 7.7-7.8): on by default, and a
                configuration that is to run that paper's method states [false]. *)
        loop_levels_from : loop_levels_from; [@default Reduction]
            (** when [loop_levels]'s priorities take effect; read only when
                [alternation_depth] and [loop_levels] both hold *)
      }
        (** the parity progress measure: one ranking over the priorities *)
  [@@deriving yojson]

  type t = {
    verbose : bool; [@default false]
    use_dwf : bool; [@default false]
        (** state disjunctive well-foundedness rather than well-foundedness of the copied
            arguments; read only by [Wf_reduction].  Set by a caller, not by a configuration
            file. *)
    reduction : fixpoint_reduction;
        [@default
          Wf_reduction
            {
              restrict_ranking_to_cycles = true;
              record_on_head = false;
              one_relation_per_block = false;
            }]
  }
  [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  include MakeExtFile (struct
    type nonrec t = t

    let of_yojson = of_yojson
    let to_yojson = to_yojson
    let name = "Reducer"

    (* a leaf: no nested config to load *)
    let instantiate = Or_error.return
  end)
end

(* [call_graph_sccs preds]: the strongly connected components of the call
   graph of [preds], where vertex [i] stands for the [i]-th predicate and
   there is an edge from [i] to [j] when the [j]-th predicate occurs in the
   body of the [i]-th.  Each component is a list of indices.  Only the
   predicates that call or are called by one of [preds] are vertices: a
   predicate with neither is in no component (the parity reduction keeps
   such a predicate through its separate list of predicates that call none).
   Every vertex is in exactly one component, and the result depends on
   [preds] alone, so concurrent calls from several domains -- the primal and
   dual tasks of a parallel solver reduce at the same time -- cannot disturb
   one another. *)
let call_graph_sccs (preds : Pred.t list) : int list list =
  let graph = IntDigraph.create ~size:(List.length preds) () in
  List.iteri preds ~f:(fun i predi ->
      let pvs_body = Formula.pvs_of predi.Pred.body in
      List.iteri preds ~f:(fun j predj ->
          if Set.mem pvs_body predj.Pred.name then IntDigraph.add_edge graph i j));
  IntDigraph.Components.scc_list graph

module Make (Cfg : Config.ConfigType) = struct
  let config = Cfg.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  (* [psub_of_psenv psenv bpvs] maps each predicate of [psenv] outside
     [bpvs] to its uninterpreted copy applied to fresh formals.  The fresh
     names are drawn in ascending order of [(pvar, sorts)], the order a set's
     fold visits; the map is built directly rather than through a set of
     (name, replacement) pairs, which ordered those pairs by the generic
     comparison.  Raises when [psenv] gives one name two sort lists, as the
     conversion of that set into a map did. *)
  let psub_of_psenv psenv bpvs =
    Set.fold (Set.diff psenv bpvs) ~init:Map.Poly.empty
      ~f:(fun psub (pvar, sorts) ->
        let params = mk_fresh_sort_env_list sorts in
        Map.Poly.add_exn psub ~key:pvar
          ~data:
            ( params,
              Formula.mk_atom
              @@ Atom.mk_pvar_app (Ident.uninterp_pvar pvar) sorts
              @@ Term.of_sort_env params ))

  let rec elim_nu_aux (*?(id=None)*) psenv bpvs query = function
    | [] ->
        let before = Formula.subst_preds (psub_of_psenv psenv bpvs) query in
        let after =
          before |> Evaluator.simplify |> Formula.to_cnf
          |> Set.Poly.map
               ~f:
                 (Formula.rm_quant ~forall:true
                 >> Tuple2.map_fst ~f:Map.of_set_exn
                 >> Formula.reduce_sort_map)
        in
        record_rewrite before
          (List.map (Set.to_list after) ~f:(fun (senv, phi) ->
               Formula.forall (Map.Poly.to_alist senv) phi));
        (after, Set.Poly.empty)
    | pred :: preds
      when Stdlib.( = ) pred.Pred.kind Predicate.Nu
           || Stdlib.( = ) pred.Pred.kind Predicate.MuOrNu ->
        let pvar' = Ident.uninterp_pvar pred.name in
        let bounds, phi = LogicOld.Formula.rm_quant ~forall:true pred.body in
        (*let bounds(* ToDo: this should be empty *) =
          Set.Poly.filter_map (Formula.tvs_of phi)
          ~f:(fun x -> if List.Assoc.mem ~equal:Stdlib.(=) args x then None else Some (x, LogicOld.T_int.SInt))
          in*)
        let uni_senv =
          Map.of_set_exn @@ Set.union (Set.Poly.of_list pred.args) bounds
        in
        let queries, clauses = elim_nu_aux psenv bpvs query preds in
        let before =
          phi
          |> Formula.subst_preds (psub_of_psenv psenv bpvs)
          |> Formula.mk_imply
               (Formula.mk_atom @@ Atom.pvar_app_of_senv pvar' pred.args)
        in
        let cnf = before |> Evaluator.simplify |> Formula.to_cnf in
        (* the clauses share the implication's variables, so the pair is an
           equivalence of open formulas read under one assignment *)
        record_rewrite before (Set.to_list cnf);
        ( queries,
          cnf
          |> Set.Poly.map ~f:(Tuple2.curry Formula.reduce_sort_map uni_senv)
          |> Set.union clauses )
    | _ ->
        failwith "every mu predicate must be eliminated before applying elim_nu"

  let elim_nu (*?(id=None)*) query preds unknowns =
    let psenv = Pred.pred_sort_env_of_list preds in
    ( elim_nu_aux psenv
        (Map.to_set @@ Kind.pred_sort_env_map_of unknowns)
        query preds,
      Kind.add_pred_env_set unknowns Kind.Ord
      @@ Set.Poly.map psenv ~f:(Tuple2.map_fst ~f:Ident.uninterp_pvar) )

  (* Dependency Graph for optimization of pfwCSP generation *)
  (* e.g.
        given muCLP (P_1 =mu P_2; P_2 =mu P_3; P_3 =mu P_1 /\ P_4; P_4 =mu P_2),
        we generate the following dependency graph G with two types of edges => and --> that
        respectively represent forward and backawrd calls:
          _____________
         |       ______|_____
         |      |      |     |
        P_1 => P_2 => P3 => P_4

     where
      level(P_1) < level(P_2) < level(P_3) < level(P_4)
      P => P' iff P calls P' and level(P) < level(P')
      P --> P' iff P calls P' and level(P) >= level(P')

     for each P,
     - the arguments of P are extended with b and args(P')
       for each inductive predicate P' such that level(P') < level(P)
       if and only if P' (=> | -->)+ P (=> | -->)+ P' in G(level(P'))

     - call to inductive predicate P' in P such that level(P') <= level(P) is replaced by
       - P' and WF_P' if P' (=> | -->)* P in G(level(P')),
       - P' otherwise

     Here, G(l) represents the subgraph of G obtained by eliminating the nodes with the level less than l. *)
  module DepGraph = struct
    type pvars = Ident.pvar_set

    type attr = {
      level : int;
      forward : pvars; (* => *)
      forward_reachable : pvars; (* =>+ *)
      backward : pvars; (* --> *)
      reachable : pvars; (* (=> | -->)+ *)
    }

    type t = (Ident.pvar, attr) Map.Poly.t

    let ( => ) a b (g : t) =
      Set.mem
        (try Map.Poly.find_exn g a
         with exn_ when not (Common.Timer.is_async exn_) ->
           failwith ("not found: " ^ Ident.name_of_pvar a))
          .forward
        b

    let ( --> ) a b (g : t) =
      Set.mem
        (try Map.Poly.find_exn g a
         with exn_ when not (Common.Timer.is_async exn_) ->
           failwith ("not found: " ^ Ident.name_of_pvar a))
          .backward
        b

    let ( =-> ) a b (g : t) =
      let attr =
        try Map.Poly.find_exn g a
        with exn_ when not (Common.Timer.is_async exn_) ->
          failwith ("not found: " ^ Ident.name_of_pvar a)
      in
      Set.mem attr.backward b || Set.mem attr.forward b

    let ( =>+ ) a b (g : t) =
      Set.mem
        (try Map.Poly.find_exn g a
         with exn_ when not (Common.Timer.is_async exn_) ->
           failwith ("not found: " ^ Ident.name_of_pvar a))
          .forward_reachable
        b

    let ( =>* ) a b (g : t) = Stdlib.(a = b) || (a =>+ b) g

    let reach_set_of g pvar =
      (try Map.Poly.find_exn g pvar
       with exn_ when not (Common.Timer.is_async exn_) ->
         failwith ("not found: " ^ Ident.name_of_pvar pvar))
        .reachable

    let ( =->+ ) a b (g : t) = Set.mem (reach_set_of g a) b
    let ( =->* ) a b (g : t) = Stdlib.(a = b) || (a =->+ b) g

    let rev_reach_set_of pvars (g : t) pvar =
      Set.filter pvars ~f:(fun pvar' -> (pvar' =->+ pvar) g)

    let level g a =
      try (Map.Poly.find_exn g a).level
      with exn_ when not (Common.Timer.is_async exn_) ->
        if true then -1
        (* uninterpreted pvars are of level -1*) else
          failwith ("not found: " ^ Ident.name_of_pvar a)

    let gen_init_graph (query : Formula.t) (preds : Pred.t list) : t =
      let pvars = List.mapi preds ~f:(fun i pred -> (pred.name, i)) in
      let level_of =
        let map = Map.Poly.of_alist_exn pvars in
        fun p ->
          match Map.Poly.find map p with
          | None -> -1 (* uninterpreted pvars are of level -1*)
          | Some i -> i
      in
      let occurrences_in pvar =
        List.find_map_exn preds ~f:(fun pred ->
            if Stdlib.( = ) pvar pred.name then Some (Formula.pvs_of pred.body)
            else None)
      in
      let query_node =
        ( Ident.Pvar "#query",
          {
            level = -1;
            forward = Formula.pvs_of query;
            backward = Set.Poly.empty;
            forward_reachable = Set.Poly.empty;
            reachable = Set.Poly.empty;
          } )
      in
      Map.Poly.of_alist_exn
      @@ query_node
         :: List.map pvars ~f:(fun (pvar, level) ->
             let forward, backward =
               Set.partition_tf (occurrences_in pvar) ~f:(fun pvar' ->
                   level < level_of pvar')
             in
             ( pvar,
               {
                 level;
                 forward;
                 backward;
                 forward_reachable = Set.Poly.empty;
                 reachable = Set.Poly.empty;
               } ))

    let restrict_to pvs =
      Map.Poly.filter_keys ~f:(Set.mem pvs)
      >> Map.Poly.map ~f:(fun attr ->
          {
            attr with
            forward = Set.inter attr.forward pvs;
            backward = Set.inter attr.backward pvs;
          })

    (* [transitive_closure g]: each node's [forward_reachable] becomes the
       nodes reachable from it by one or more [forward] edges, and its
       [reachable] those reachable by one or more [forward] or [backward]
       edges, a path continuing only through nodes of [g].

       Computed by one search per node.  It is the fixpoint the iteration
       [transitive_closure_by_rounds] below reaches -- each round adds to a
       node's set the sets of its members that are nodes of [g], starting from
       its direct successors -- since that fixpoint is the least assignment
       containing the direct successors and closed under the round, which is
       the set of path ends just described.  The rounds took a set union per
       member per node per round, quadratic in the nodes per round, and
       [ufp_of] closes a graph once per predicate it eliminates. *)
    let transitive_closure (g : t) : t =
      let reach direct =
        let seen = Hash_set.Poly.create () in
        let rec visit p =
          if not (Hash_set.mem seen p) then (
            Hash_set.add seen p;
            match Map.Poly.find g p with
            | Some attr -> Set.iter (direct attr) ~f:visit
            | None -> ())
        in
        fun attr ->
          Set.iter (direct attr) ~f:visit;
          Set.Poly.of_list (Hash_set.to_list seen)
      in
      Map.Poly.map g ~f:(fun attr ->
          {
            attr with
            forward_reachable = reach (fun a -> a.forward) attr;
            reachable = reach (fun a -> Set.union a.forward a.backward) attr;
          })

    (* the fixpoint iteration [transitive_closure] replaces, kept as the
       reference it is checked against *)
    let transitive_closure_by_rounds g =
      let rec inner g =
        let g' =
          Map.Poly.map g ~f:(fun attr ->
              let forward_reachable =
                Set.fold attr.forward_reachable ~init:attr.forward_reachable
                  ~f:(fun forward_reachable p' ->
                    try
                      Set.union forward_reachable
                        (Map.Poly.find_exn g p').forward_reachable
                    with exn_ when not (Common.Timer.is_async exn_) -> forward_reachable)
              in
              let reachable =
                Set.fold ~init:attr.reachable attr.reachable
                  ~f:(fun reachable p' ->
                    try Set.union reachable (Map.Poly.find_exn g p').reachable
                    with exn_ when not (Common.Timer.is_async exn_) -> reachable)
              in
              { attr with forward_reachable; reachable })
        in
        if
          Map.Poly.equal
            (fun attr1 attr2 ->
              Set.equal attr1.forward_reachable attr2.forward_reachable
              && Set.equal attr1.reachable attr2.reachable)
            g g'
        then g'
        else inner g'
      in
      inner
      @@ Map.Poly.map g ~f:(fun attr ->
          {
            attr with
            forward_reachable = attr.forward;
            reachable = Set.union attr.forward attr.backward;
          })

    let k_transitive_closure g k =
      let rec inner g =
        let g' =
          Map.Poly.map g ~f:(fun attr ->
              let reachable =
                Set.fold ~init:attr.reachable attr.reachable
                  ~f:(fun reachable p' ->
                    try Set.union reachable (Map.Poly.find_exn g p').reachable
                    with exn_ when not (Common.Timer.is_async exn_) -> reachable)
              in
              { attr with reachable })
        in
        if
          Map.Poly.equal
            (fun attr1 attr2 -> Set.equal attr1.reachable attr2.reachable)
            g g'
        then g'
        else inner g'
      in
      inner
      @@ Map.Poly.map g ~f:(fun attr ->
          {
            attr with
            reachable =
              Set.filter ~f:(fun pvar -> level g pvar > k)
              @@ Set.union attr.forward attr.backward;
          })

    let str_of (g : t) =
      String.concat_map_list (Map.Poly.to_alist g) ~sep:";\n"
        ~f:(fun (Ident.Pvar pname, attr) ->
          String.paren
          @@ sprintf "%s, %d, [%s], [%s], [%s], [%s]" pname attr.level
               (Ident.str_of_pvars ~sep:";" attr.forward)
               (Ident.str_of_pvars ~sep:";" attr.forward_reachable)
               (Ident.str_of_pvars ~sep:";" attr.backward)
               (Ident.str_of_pvars ~sep:";" attr.reachable))
  end

  (* [layout], when given, receives for every predicate this step extends the
     entries it prepends ([prefix_entry]), in front of those an earlier step
     prepended.  It changes nothing the reduction builds. *)
  let ufp_of ?(id = None) ?(is_nu = false) ?layout ?(record_on_head = false)
      (use_dwf, restrict_ranking_to_cycles) dg0
      unknowns query (pred : Pred.t) (nu_only : Pred.t list) rest =
    let dg =
      let relevant_pvs =
        Set.Poly.of_list
          (pred.name :: List.map nu_only ~f:(fun pred -> pred.name))
      in
      DepGraph.transitive_closure @@ DepGraph.restrict_to relevant_pvs dg0
    in
    Debug.print ~id
    @@ lazy
         (sprintf "************ Filtered DepGraph for %s:\n%s"
            (Ident.name_of_pvar pred.name)
            (DepGraph.str_of dg));
    let indirect_rec_called, non_rec_called =
      List.partition_tf nu_only ~f:(fun pred' ->
          let open DepGraph in
          (not restrict_ranking_to_cycles)
          || ((pred.name =->+ pred'.name) dg && (pred'.name =->+ pred.name) dg))
    in
    let is_called_outside =
      let seed =
        Set.remove
          (Set.Poly.union_list
          @@ Formula.pvs_of query
             :: List.map (non_rec_called @ rest) ~f:(fun p ->
                 Formula.pvs_of p.body))
          pred.name
      in
      fun pvar ->
        Set.exists seed ~f:(fun pvar' ->
            let open DepGraph in
            Ident.pvar_equal pvar pvar'
            || (Map.Poly.mem dg pvar' && (pvar' =->+ pvar) dg))
    in
    (* Invariant: a member of [indirect_rec_called] that is not called outside
       is called only from [pred]'s body and from the bodies of members that
       are not called outside either.  So neither [sigma_1] (which rewrites
       the query, [rest] and [non_rec_called]) nor [sigma_5] (which rewrites
       the members that are called outside) ever meets such a member, and the
       flagless arm of [ext_arg] is reached only from [sigma_4] (from
       [sigma_2] without [use_dwf], where [sigma_3] takes [sigma_5]'s place).
       Why it holds: a call from the query, [rest] or [non_rec_called] puts the
       callee in [seed] by construction; and if a member [q1] that is called
       outside, by a witness [s] of [seed] with [s = q1] or [s =->+ q1], calls
       [q], then [q] is a callee of [q1] inside the restricted graph, so the
       transitive closure gives [s =->+ q] and [q] is called outside too.
       The check changes no behaviour; it costs one [pvs_of] per body. *)
    if restrict_ranking_to_cycles then begin
      let non_out =
        Set.Poly.of_list
        @@ List.filter_map indirect_rec_called ~f:(fun (p : Pred.t) ->
            if is_called_outside p.name then None else Some p.name)
      in
      let calls_non_out phi =
        not (Set.is_empty (Set.inter (Formula.pvs_of phi) non_out))
      in
      assert (
        (not (calls_non_out query))
        && List.for_all (rest @ non_rec_called) ~f:(fun (p : Pred.t) ->
            not (calls_non_out p.body))
        && List.for_all indirect_rec_called ~f:(fun (p : Pred.t) ->
            (not (is_called_outside p.name)) || not (calls_non_out p.body)))
    end;
    let bot, top = (T_bool.mk_false (), T_bool.mk_true ()) in
    let bi_term, bi_param =
      let bi_name = Ident.mk_fresh_tvar () in
      (Term.mk_var bi_name T_bool.SBool, (bi_name, T_bool.SBool))
    in
    let xs_sorts = List.map ~f:snd pred.args in
    let ext_arg b xs_terms =
      List.map indirect_rec_called ~f:(fun pred' ->
          let ys_sorts = List.map ~f:snd pred'.args in
          let ys_params = mk_fresh_sort_env_list ys_sorts in
          let ys_terms = Term.of_sort_env ys_params in
          let phi =
            Formula.mk_atom
            @@ Tuple2.uncurry (Atom.mk_pvar_app pred'.name)
            @@
            if (not restrict_ranking_to_cycles) || is_called_outside pred'.name then
              ((T_bool.SBool :: xs_sorts) @ ys_sorts, (b :: xs_terms) @ ys_terms)
            else (xs_sorts @ ys_sorts, xs_terms @ ys_terms)
          in
          (pred'.name, (ys_params, phi)))
    in
    let xs_params = mk_fresh_sort_env_list xs_sorts in
    let xs_terms = Term.of_sort_env xs_params in
    let dir_rec = DepGraph.(pred.name =->+ pred.name) dg in
    let unknowns' =
      if (not restrict_ranking_to_cycles) || dir_rec then
        Kind.add_pred_env_set unknowns
          (if is_nu then Kind.Ord else if use_dwf then Kind.DWF else Kind.WF)
          (Set.Poly.singleton
             (Ident.wfpred_pvar pred.name, xs_sorts @ xs_sorts))
      else unknowns
    in
    let sigma_1 =
      (* calls unrelated to recursive calls of pred *)
      Formula.subst_preds @@ Map.Poly.of_alist_exn
      @@
      let dummy_args = List.map xs_sorts ~f:Term.mk_dummy in
      if use_dwf && ((not restrict_ranking_to_cycles) || dir_rec) then
        let ys_params = mk_fresh_sort_env_list xs_sorts in
        let ys_terms = Term.of_sort_env ys_params in
        ( pred.name,
          ( ys_params,
            Formula.mk_atom
            @@ Atom.mk_pvar_app pred.name (xs_sorts @ xs_sorts)
                 (ys_terms @ ys_terms) ) )
        :: ext_arg bot dummy_args
      else ext_arg bot dummy_args
    in
    let emb_wfp check_bi =
      let ys_params = mk_fresh_sort_env_list xs_sorts in
      let ys_terms = Term.of_sort_env ys_params in
      let phi =
        Formula.and_of
          [
            (* (co-)recursion *)
            Formula.mk_atom @@ Atom.mk_pvar_app pred.name xs_sorts ys_terms;
            (* guard *)
            (if check_bi then Formula.mk_imply (Formula.eq bi_term top)
             else Fn.id)
            @@ Formula.mk_atom
            @@ Atom.mk_pvar_app
                 (Ident.wfpred_pvar pred.name)
                 (xs_sorts @ xs_sorts) (xs_terms @ ys_terms);
          ]
      in
      (pred.name, (ys_params, phi))
    in
    let sigma_2 =
      (* direct recursive calls to pred *)
      Formula.subst_preds @@ Map.Poly.of_alist_exn
      @@ (emb_wfp false :: ext_arg top xs_terms)
    in
    let sigma_3 =
      (* indirect recursive calls to pred *)
      Formula.subst_preds @@ Map.Poly.of_alist_exn
      @@ (emb_wfp true :: ext_arg bi_term xs_terms)
    in
    let sigma_4 =
      (* direct recursive calls to pred *)
      Formula.subst_preds @@ Map.Poly.of_alist_exn
      @@
      let ys_params = mk_fresh_sort_env_list xs_sorts in
      let ys_terms = Term.of_sort_env ys_params in
      let phi =
        Formula.and_of
          [
            (* (co-)recursion *)
            Formula.mk_atom
            @@ Atom.mk_pvar_app pred.name (xs_sorts @ xs_sorts)
                 (ys_terms @ ys_terms);
            (* (co-)recursion *)
            Formula.mk_atom
            @@ Atom.mk_pvar_app pred.name (xs_sorts @ xs_sorts)
                 (xs_terms @ ys_terms);
            (* guard *)
            Formula.mk_atom
            @@ Atom.mk_pvar_app
                 (Ident.wfpred_pvar pred.name)
                 (xs_sorts @ xs_sorts) (xs_terms @ ys_terms);
          ]
      in
      (pred.name, (ys_params, phi)) :: ext_arg top xs_terms
    in
    let sigma_5 =
      (* indirect recursive calls to pred *)
      Formula.subst_preds @@ Map.Poly.of_alist_exn
      @@
      let ys_params = mk_fresh_sort_env_list xs_sorts in
      let ys_terms = Term.of_sort_env ys_params in
      let phi =
        Formula.and_of
          [
            (* (co-)recursion *)
            Formula.mk_atom
            @@ Atom.mk_pvar_app pred.name (xs_sorts @ xs_sorts)
                 (ys_terms @ ys_terms);
            Formula.mk_imply (Formula.eq bi_term top)
            @@ Formula.and_of
                 [
                   (* (co-)recursion *)
                   Formula.mk_atom
                   @@ Atom.mk_pvar_app pred.name (xs_sorts @ xs_sorts)
                        (xs_terms @ ys_terms);
                   (* guard *)
                   Formula.mk_atom
                   @@ Atom.mk_pvar_app
                        (Ident.wfpred_pvar pred.name)
                        (xs_sorts @ xs_sorts) (xs_terms @ ys_terms);
                 ];
          ]
      in
      (pred.name, (ys_params, phi)) :: ext_arg bi_term xs_terms
    in
    (* [record_on_head]: [pred]'s body with every member of its component
       unfolded, or [None] when the flagged encoding below is to be used.
       Assumes: [indirect_rec_called] are exactly the members of [pred]'s
       component (by [restrict_ranking_to_cycles]), and the member call graph
       is acyclic (checked here), so the unfolding stops after at most as many
       rounds as there are members.  Guarantees: the body mentions no member;
       every call of [pred] in it -- [pred]'s own direct calls and those the
       unfolded members made -- is [pred ys /\ WF_pred xs ys] with [xs]
       [pred]'s own parameters, exactly what the flagged encoding builds for a
       call made with the flag true and the copies [xs], which is the flag and
       the copies [pred]'s body passes to every member it calls.  The members
       themselves stay as they were: every other caller passes them a false
       flag, under which their calls of [pred] are unguarded and the copies
       never read. *)
    let head_unfolded =
      let member_names =
        Set.Poly.of_list
        @@ List.map indirect_rec_called ~f:(fun (p : Pred.t) -> p.name)
      in
      let calls_of (p : Pred.t) =
        Set.inter (Formula.pvs_of p.body) member_names
      in
      let members_acyclic () =
        let succ =
          Map.Poly.of_alist_exn
          @@ List.map indirect_rec_called ~f:(fun (p : Pred.t) ->
              (p.name, calls_of p))
        in
        (* depth-first search: [on_path] the current path, [finished] the
           members all of whose paths were explored without a cycle *)
        let finished = Hash_set.Poly.create () in
        let rec visit on_path p =
          if Set.mem on_path p then false
          else if Hash_set.mem finished p then true
          else
            let ok =
              Set.for_all
                (Option.value (Map.Poly.find succ p) ~default:Set.Poly.empty)
                ~f:(visit (Set.add on_path p))
            in
            if ok then Hash_set.add finished p;
            ok
        in
        Set.for_all member_names ~f:(visit Set.Poly.empty)
      in
      if
        record_on_head && (not use_dwf) && restrict_ranking_to_cycles && dir_rec
        && (not (List.is_empty indirect_rec_called))
        && members_acyclic ()
      then begin
        let msub =
          Map.Poly.of_alist_exn
          @@ List.map indirect_rec_called ~f:(fun (p : Pred.t) ->
              (p.name, (p.args, p.body)))
        in
        let rec unfold rounds phi =
          if Set.is_empty (Set.inter (Formula.pvs_of phi) member_names) then
            phi
          else if rounds <= 0 then
            failwith "record_on_head: the unfolding of an acyclic component did not stop"
          else unfold (rounds - 1) (Formula.subst_preds msub phi)
        in
        let unfolded = unfold (List.length indirect_rec_called) pred.body in
        let ys_params = mk_fresh_sort_env_list xs_sorts in
        let ys_terms = Term.of_sort_env ys_params in
        let guarded_call =
          Formula.and_of
            [
              Formula.mk_atom @@ Atom.mk_pvar_app pred.name xs_sorts ys_terms;
              Formula.mk_atom
              @@ Atom.mk_pvar_app
                   (Ident.wfpred_pvar pred.name)
                   (xs_sorts @ xs_sorts)
                   (Term.of_sort_env pred.args @ ys_terms);
            ]
        in
        let body =
          Formula.subst_preds
            (Map.Poly.singleton pred.name (ys_params, guarded_call))
            unfolded
        in
        Debug.print ~id
        @@ lazy
             (sprintf
                "record_on_head: %s keeps its ranking copies, %d member(s) \
                 unfolded (body of %d nodes, was %d)"
                (Ident.name_of_pvar pred.name)
                (List.length indirect_rec_called)
                (Formula.ast_size body) (Formula.ast_size pred.body));
        Some body
      end
      else None
    in
    match head_unfolded with
    | Some body ->
        (unknowns', query, { pred with kind = Predicate.Nu; body } :: nu_only, rest)
    | None ->
    let query' = sigma_1 query in
    let rest' =
      List.map rest ~f:(fun pred -> { pred with body = sigma_1 pred.body })
    in
    let nu_only' =
      (if use_dwf then
         if (not restrict_ranking_to_cycles) || dir_rec then
           {
             pred with
             kind = Predicate.Nu;
             args = xs_params @ pred.args;
             body = sigma_4 pred.body;
           }
         else
           { pred with kind = Predicate.Nu; args = pred.args; body = pred.body }
       else
         {
           pred with
           kind = Predicate.Nu;
           args = pred.args;
           body =
             Formula.rename (ren_of_sort_env_list xs_params pred.args)
             @@ sigma_2 pred.body;
         })
      :: List.map nu_only ~f:(fun pred' ->
          if
            let open DepGraph in
            (not restrict_ranking_to_cycles)
            || ((pred.name =->+ pred'.name) dg && (pred'.name =->+ pred.name) dg)
          then
            if use_dwf then
              if (not restrict_ranking_to_cycles) || is_called_outside pred'.name then
                {
                  pred' with
                  args = (bi_param :: xs_params) @ pred'.args;
                  body = sigma_5 pred'.body;
                }
              else
                {
                  pred' with
                  args = xs_params @ pred'.args;
                  body = sigma_4 pred'.body;
                }
            else if (not restrict_ranking_to_cycles) || is_called_outside pred'.name then
              {
                pred' with
                args = (bi_param :: xs_params) @ pred'.args;
                body = sigma_3 pred'.body;
              }
            else
              {
                pred' with
                args = xs_params @ pred'.args;
                body = sigma_2 pred'.body;
              }
          else { pred' with body = sigma_1 pred'.body })
    in
    (match layout with
    | None -> ()
    | Some tbl ->
        let copies = List.map xs_params ~f:(fun _ -> Copy) in
        let prepend name entries =
          Hashtbl.update tbl name ~f:(fun old ->
              entries @ Option.value old ~default:[])
        in
        if use_dwf && ((not restrict_ranking_to_cycles) || dir_rec) then prepend pred.name copies;
        List.iter indirect_rec_called ~f:(fun pred' ->
            if (not restrict_ranking_to_cycles) || is_called_outside pred'.name then
              prepend pred'.name (Flag :: copies)
            else prepend pred'.name copies));
    (unknowns', query', nu_only', rest')

  (* [ufp_of_block ?layout unknowns query block nu_only rest]: the reduction
     of a whole block of least fixpoints with one well-foundedness unknown
     ([one_relation_per_block]), or [None] when fewer than two of the block's
     predicates must keep a ranking, in which case the caller reduces the
     block one predicate at a time as without the switch.

     Assumes: [block] is a maximal run of consecutive [Mu] equations, listed
     innermost first; [nu_only] are the equations after it, all greatest
     fixpoints by now (the block's scope is [block @ nu_only]); [rest] are the
     equations before it, which, like [query], are only rewritten.  Names are
     unique across the three lists.

     The encoding.  The ranked predicates ("heads") are an inclusion-minimal
     set [heads] of the block's predicates meeting every cycle of the call
     graph restricted to the scope that passes through the block: start from
     the block's predicates that lie on such a cycle and drop, innermost first,
     each whose every cycle through it in the scope meets another head.  The
     other predicates of the block become greatest fixpoints with no ranking:
     a predicate on no cycle of its scope has the same solution as a least and
     as a greatest fixpoint, permuting the equations of one block changes no
     solution (Bekic's principle), so moving the heads to the front of the
     block and then flipping the others is exact, each flipped one lying on no
     cycle of its new scope because the heads cut every cycle through the
     block.  A head [k] with parameters [xs] gets the record
     [rec(k, xs) = (tag_k, slots)]: [tag_k] an integer naming [k], [slots] per
     sort as many positions as the head with most arguments of that sort has,
     [k]'s arguments of that sort in order and a constant after them.  The
     members are the predicates after the heads (the flipped ones included) on
     a path from a head to a head through non-heads.  Then, with [WF] the one
     new unknown over pairs of records:
     - every head becomes a greatest fixpoint and keeps its arity; in its body
       a call [k' ys] of a head becomes [k' ys /\ WF (rec(k, xs), rec(k', ys))]
       and a call of a member passes [(true, rec(k, xs))];
     - a member gets a Boolean flag [b] and a record [r] as new leading
       arguments; in its body a call [k' ys] becomes
       [k' ys /\ (b => WF (r, rec(k', ys)))] and a call of a member passes
       [(b, r)] on;
     - a member every one of whose callers is a head or a flagless member gets
       no flag (it would be true at every call), and its guard is unconditional;
     - every other call of a member (from [query], [rest], or a predicate after
       the heads that is not a member) passes [false] and a constant record.

     Why it is sound.  Let the record map be any map of head instances into a
     set and [WF] any well-founded relation on it.  The greatest solution of the
     reduced block lies pointwise below the original block's least solution:
     for heads by well-founded induction on the record (every head-to-head
     step inside a head, and every one a member takes under a true flag,
     decreases it), for members under a true flag because they form a
     post-fixpoint of the original greatest-fixpoint equations with the heads
     already bounded, and for the false-flag members and the remaining
     predicates by the same post-fixpoint argument.  Least and greatest
     fixpoints are monotone in a pointwise smaller operator, so composing the
     steps from the innermost block outwards, a valid reduced problem with
     its well-founded relations fixed implies a valid original.  With the
     outer predicates fixed the step is also complete: the record map here is
     injective, so ordering records by the stage at which the instance enters
     the least fixpoint's approximation gives a well-founded relation under
     which the original solution is a post-fixpoint of the reduced block.
     Completeness across blocks whose outer equations include a least
     fixpoint is not established.  The one-predicate encoding is the case of a
     single head with [rec(k, xs) = xs]. *)
  let ufp_of_block ?(id = None) ?layout unknowns query (block : Pred.t list)
      (nu_only : Pred.t list) rest =
    let scope = block @ nu_only in
    let scope_names =
      Set.Poly.of_list @@ List.map scope ~f:(fun (p : Pred.t) -> p.name)
    in
    let succ =
      let tbl =
        Map.Poly.of_alist_exn
        @@ List.map scope ~f:(fun (p : Pred.t) ->
            (p.name, Set.inter (Formula.pvs_of p.body) scope_names))
      in
      fun p -> Option.value (Map.Poly.find tbl p) ~default:Set.Poly.empty
    in
    (* is there a cycle through [v] whose other vertices avoid [avoid]? *)
    let on_cycle_avoiding avoid v =
      let seen = Hash_set.Poly.create () in
      let rec visit p =
        Set.exists (succ p) ~f:(fun q ->
            Ident.pvar_equal q v
            || (not (Set.mem avoid q))
               && (not (Hash_set.mem seen q))
               && (Hash_set.add seen q;
                   visit q))
      in
      visit v
    in
    let heads =
      List.fold block
        ~init:
          (Set.Poly.of_list
          @@ List.filter_map block ~f:(fun (p : Pred.t) ->
              if on_cycle_avoiding Set.Poly.empty p.name then Some p.name
              else None))
        ~f:(fun heads (p : Pred.t) ->
          if
            Set.mem heads p.name
            && not (on_cycle_avoiding (Set.remove heads p.name) p.name)
          then Set.remove heads p.name
          else heads)
    in
    if Set.length heads < 2 then None
    else
      (* the heads in equation order, outermost first, and their tags *)
      let head_preds =
        List.rev @@ List.filter block ~f:(fun (p : Pred.t) -> Set.mem heads p.name)
      in
      let tag_of =
        let tbl =
          Map.Poly.of_alist_exn
          @@ List.mapi head_preds ~f:(fun i (p : Pred.t) -> (p.name, i))
        in
        Map.Poly.find_exn tbl
      in
      let non_heads =
        List.filter_map scope ~f:(fun (p : Pred.t) ->
            if Set.mem heads p.name then None else Some p.name)
        |> Set.Poly.of_list
      in
      (* per-sort slots, sorts in order of first appearance among the heads *)
      let slots =
        List.fold head_preds ~init:[] ~f:(fun slots (p : Pred.t) ->
            let sorts = List.map p.args ~f:snd in
            let slots =
              List.fold sorts ~init:slots ~f:(fun slots s ->
                  if List.exists slots ~f:(fst >> Stdlib.( = ) s) then slots
                  else slots @ [ (s, 0) ])
            in
            List.map slots ~f:(fun (s, n) ->
                (s, max n (List.count sorts ~f:(Stdlib.( = ) s)))))
      in
      let rec_sorts =
        T_int.SInt
        :: List.concat_map slots ~f:(fun (s, n) -> List.init n ~f:(fun _ -> s))
      in
      let rec_of k (args : Term.t list) sorts =
        T_int.from_int (tag_of k)
        :: List.concat_map slots ~f:(fun (s, n) ->
            let mine =
              List.filter_map (List.zip_exn args sorts) ~f:(fun (t, s') ->
                  if Stdlib.( = ) s s' then Some t else None)
            in
            mine @ List.init (n - List.length mine) ~f:(fun _ -> Term.mk_dummy s))
      in
      (* The unknown's name must not be the well-foundedness name of any
         predicate: MuVal's exchange of partial solutions between the primal
         and the dual attributes an unknown [WF_p_] to the predicate [p] by its
         name alone, and decides from that attribution which violated clauses
         a candidate for [p] may ignore.  Named after one head, the shared
         unknown made a violated clause of another head look like a clause of
         the first, a candidate that violated it was sent to the other side as
         a bound, and the other side refuted a valid problem.  An unknown
         attributed to no predicate only adds clauses a candidate must satisfy. *)
      let wf_name =
        let taken =
          Set.Poly.of_list
          @@ List.map (scope @ rest) ~f:(fun (p : Pred.t) ->
              Ident.name_of_pvar p.name)
        in
        let rec fresh key =
          if Set.mem taken key then fresh (key ^ "_") else key
        in
        Ident.wfpred_pvar
        @@ Ident.Pvar
             (fresh
                ("block_" ^ Ident.name_of_pvar (List.hd_exn head_preds).name))
      in
      (* members: after the heads, reached from a head and reaching a head,
         through non-heads only *)
      let reach_from starts next =
        let seen = Hash_set.Poly.create () in
        let rec visit p =
          if Set.mem non_heads p && not (Hash_set.mem seen p) then (
            Hash_set.add seen p;
            Set.iter (next p) ~f:visit)
        in
        Set.iter starts ~f:visit;
        Set.Poly.of_list (Hash_set.to_list seen)
      in
      let from_heads next =
        Set.Poly.union_list (List.map (Set.to_list heads) ~f:next)
      in
      let fwd = reach_from (from_heads succ) succ in
      let preds_of =
        let tbl =
          List.fold scope ~init:Map.Poly.empty ~f:(fun m (p : Pred.t) ->
              Set.fold (succ p.name) ~init:m ~f:(fun m q ->
                  Map.Poly.update m q ~f:(function
                    | None -> Set.Poly.singleton p.name
                    | Some s -> Set.add s p.name)))
        in
        fun p -> Option.value (Map.Poly.find tbl p) ~default:Set.Poly.empty
      in
      let bwd = reach_from (from_heads preds_of) preds_of in
      let members = Set.inter fwd bwd in
      (* flagged members: called from outside the heads and members, or from
         a flagged member *)
      let flagged =
        let direct =
          Set.inter members
          @@ Set.Poly.union_list
          @@ Formula.pvs_of query
             :: List.map rest ~f:(fun (p : Pred.t) -> Formula.pvs_of p.body)
          @ List.filter_map scope ~f:(fun (p : Pred.t) ->
              if Set.mem heads p.name || Set.mem members p.name then None
              else Some (Formula.pvs_of p.body))
        in
        let seen = Hash_set.Poly.create () in
        let rec visit p =
          if Set.mem members p && not (Hash_set.mem seen p) then (
            Hash_set.add seen p;
            Set.iter (succ p) ~f:visit)
        in
        Set.iter direct ~f:visit;
        Set.Poly.of_list (Hash_set.to_list seen)
      in
      let bot, top = (T_bool.mk_false (), T_bool.mk_true ()) in
      let b_name = Ident.mk_fresh_tvar () in
      let b_term = Term.mk_var b_name T_bool.SBool in
      let r_params = mk_fresh_sort_env_list rec_sorts in
      let r_terms = Term.of_sort_env r_params in
      let sorts_of =
        Map.Poly.of_alist_exn
        @@ List.map scope ~f:(fun (p : Pred.t) ->
            (p.name, List.map p.args ~f:snd))
      in
      (* the rewrite of a body whose calls of a member pass [flag] and [recs],
         and whose calls of a head are guarded by [guard] (or not at all) *)
      let rewrite ~flag ~recs ~guard =
        Formula.subst_preds @@ Map.Poly.of_alist_exn
        @@ (match guard with
           | None -> []
           | Some guard ->
               List.map head_preds ~f:(fun (k' : Pred.t) ->
                   let ys_sorts = List.map k'.args ~f:snd in
                   let ys_params = mk_fresh_sort_env_list ys_sorts in
                   let ys_terms = Term.of_sort_env ys_params in
                   ( k'.name,
                     ( ys_params,
                       Formula.and_of
                         [
                           Formula.mk_atom
                           @@ Atom.mk_pvar_app k'.name ys_sorts ys_terms;
                           guard
                           @@ Formula.mk_atom
                           @@ Atom.mk_pvar_app wf_name (rec_sorts @ rec_sorts)
                                (recs @ rec_of k'.name ys_terms ys_sorts);
                         ] ) )))
        @ List.filter_map (Set.to_list members) ~f:(fun m ->
            if Option.is_none flag && not (Set.mem flagged m) then None
            else
              let zs_sorts = Map.Poly.find_exn sorts_of m in
              let zs_params = mk_fresh_sort_env_list zs_sorts in
              let zs_terms = Term.of_sort_env zs_params in
              let prefix_sorts, prefix_terms =
                if Set.mem flagged m then
                  ( T_bool.SBool :: rec_sorts,
                    Option.value flag ~default:bot :: recs )
                else (rec_sorts, recs)
              in
              Some
                ( m,
                  ( zs_params,
                    Formula.mk_atom
                    @@ Atom.mk_pvar_app m (prefix_sorts @ zs_sorts)
                         (prefix_terms @ zs_terms) ) ))
      in
      (* calls from outside: a false flag and a constant record, heads
         unguarded *)
      let rewrite_outside =
        rewrite ~flag:None
          ~recs:(List.map rec_sorts ~f:Term.mk_dummy)
          ~guard:None
      in
      let rewrite_pred (p : Pred.t) =
        if Set.mem heads p.name then
          let xs_sorts = List.map p.args ~f:snd in
          {
            p with
            kind = Predicate.Nu;
            body =
              rewrite ~flag:(Some top)
                ~recs:(rec_of p.name (Term.of_sort_env p.args) xs_sorts)
                ~guard:(Some Fn.id) p.body;
          }
        else if Set.mem flagged p.name then
          {
            p with
            kind = Predicate.Nu;
            args = ((b_name, T_bool.SBool) :: r_params) @ p.args;
            body =
              rewrite ~flag:(Some b_term) ~recs:r_terms
                ~guard:(Some (Formula.mk_imply (Formula.eq b_term top)))
                p.body;
          }
        else if Set.mem members p.name then
          {
            p with
            kind = Predicate.Nu;
            args = r_params @ p.args;
            body =
              rewrite ~flag:(Some top) ~recs:r_terms ~guard:(Some Fn.id) p.body;
          }
        else { p with kind = Predicate.Nu; body = rewrite_outside p.body }
      in
      let unknowns' =
        Kind.add_pred_env_set unknowns Kind.WF
          (Set.Poly.singleton (wf_name, rec_sorts @ rec_sorts))
      in
      let query' = rewrite_outside query in
      let rest' =
        List.map rest ~f:(fun (p : Pred.t) ->
            { p with body = rewrite_outside p.body })
      in
      let nu_only' =
        List.rev_map block ~f:rewrite_pred @ List.map nu_only ~f:rewrite_pred
      in
      (match layout with
      | None -> ()
      | Some tbl ->
          let copies = List.map rec_sorts ~f:(fun _ -> Copy) in
          Set.iter members ~f:(fun m ->
              Hashtbl.update tbl m ~f:(fun old ->
                  (if Set.mem flagged m then Flag :: copies else copies)
                  @ Option.value old ~default:[])));
      Debug.print ~id
      @@ lazy
           (sprintf
              "one_relation_per_block: block of %d, heads [%s] ranked by %s \
               over records of width %d; %d member(s), %d flagged"
              (List.length block)
              (String.concat_map_list head_preds ~sep:"; " ~f:(fun (p : Pred.t) ->
                   Ident.name_of_pvar p.name))
              (Ident.name_of_pvar wf_name) (List.length rec_sorts)
              (Set.length members) (Set.length flagged));
      Some (unknowns', query', nu_only', rest')

  (* [one_relation_per_block] reduces each block of least fixpoints with
     [ufp_of_block] when that applies; a block it declines, and every block
     without the switch, is reduced one predicate at a time, innermost first.
     [MuOrNu] predicates are greatest fixpoints here, so they end a block. *)
  let elim_mu_bra ?(id = None) ?(conv_nu = false) ?layout ?(record_on_head = false)
      ?(one_relation_per_block = false)
      (use_dwf, restrict_ranking_to_cycles) (query : Formula.t) (preds : Pred.t list)
      unknowns =
    let (dg0 : DepGraph.t) = DepGraph.gen_init_graph query preds in
    Debug.print ~id
    @@ lazy (sprintf "************ Initial DepGraph:
%s" (DepGraph.str_of dg0));
    let block_mode =
      one_relation_per_block && restrict_ranking_to_cycles && (not use_dwf)
      && not conv_nu
    in
    let is_mu (p : Pred.t) =
      match p.kind with Predicate.Mu -> true | _ -> false
    in
    (* [at_block_start]: [pred] is the innermost equation of its block (the
       previous one processed was not a [Mu]) *)
    let rec inner ~at_block_start unknowns query nu_only = function
      | [] -> ((query, nu_only), unknowns)
      | pred :: rest -> (
          match pred.Pred.kind with
          | Predicate.(Nu | MuOrNu) ->
              if conv_nu then
                let unknowns', query', nu_only', rest' =
                  ufp_of ~id ~is_nu:true ?layout ~record_on_head (use_dwf, restrict_ranking_to_cycles) dg0 unknowns
                    query pred nu_only rest
                in
                inner ~at_block_start:true unknowns' query' nu_only' rest'
              else
                inner ~at_block_start:true unknowns query
                  ({ pred with kind = Predicate.Nu } :: nu_only)
                  rest
          | Predicate.Mu -> (
              let shared =
                if block_mode && at_block_start then
                  let block_rest, outer = List.split_while rest ~f:is_mu in
                  ufp_of_block ~id ?layout unknowns query (pred :: block_rest)
                    nu_only outer
                else None
              in
              match shared with
              | Some (unknowns', query', nu_only', rest') ->
                  inner ~at_block_start:true unknowns' query' nu_only' rest'
              | None ->
                  let unknowns', query', nu_only', rest' =
                    ufp_of ~id ~is_nu:false ?layout ~record_on_head (use_dwf, restrict_ranking_to_cycles) dg0 unknowns
                      query pred nu_only rest
                  in
                  inner ~at_block_start:false unknowns' query' nu_only' rest'))
    in
    inner ~at_block_start:true unknowns query [] @@ List.rev preds

  (* [loop_level_priorities ~id ~query ~all_preds preds]: a priority function
     for one strongly connected component [preds] of [all_preds] in which no
     predicate is a greatest fixpoint (each is [Mu] or [MuOrNu]), built from its
     loop hierarchy rather than from alternation depth.  The component is the
     root node, at depth 1.  At a node of depth [d], the head -- the first [Mu]
     predicate of the node, in the order of [preds], among those entered from
     outside the node (called by [query] or by a predicate of [all_preds] not in
     the node), or the first [Mu] predicate when none is entered so -- gets the
     odd priority [2d - 1]; the node minus its head
     is split into strongly connected components, each with a cycle becoming a
     child node at depth [d + 1], and every other predicate of the node (on no
     cycle once the head is removed) gets the even priority [2d].  A node
     without a [Mu] predicate gives all its predicates [2d].

     Why a parity relation for these priorities is one for the component, with
     [Mu] read as rejecting and [MuOrNu] as accepting (the reading the reduction
     gives [MuOrNu] everywhere): an infinite walk inside the component eventually
     stays in some node [H] and in none of its children, since the nodes are
     nested and finitely many.  If [H] has a head, the walk meets it infinitely
     often -- a walk in [H] that avoids the head eventually stays in one
     strongly connected component of [H] minus the head, which would be a child
     it stays in -- and every predicate of [H] has a priority at least the
     head's [2 d(H) - 1], so the least recurring priority is that odd one: the
     walk is rejected, which is what an all-[Mu] (or [Mu]-headed) recurrence
     must be.  If [H] has no head, the walk eventually visits [MuOrNu] predicates
     only, every one with priority [2 d(H)], even: accepted, as the
     reduction's own reading of [MuOrNu] accepts it.  So the relation is at least
     as strong as the parity condition requires.

     Any choice of head is sound; the choice decides which loop is the outer
     one.  An entry is taken because a loop is entered at its header: on a
     component of two predicates that each call themselves and each other
     (two nested loops sharing their heads' calls), the equation order put the
     inner loop's predicate first on one input and the outer one's on another,
     and with the inner one as head the outer loop's decrease was demanded at
     the second component only.

     With packing a head of depth [d] decreases strictly within the first [d]
     components and any other predicate of its node keeps them non-increasing:
     the lexicographic ranking of nested loops, a component per nesting level,
     with the strict decrease only where a cycle is closed.  The relation of
     alternation depth gives all the predicates of such a component priority 1
     (one component, a strict decrease on every call); that relation is the
     one this gives with every component after the first held constant, except
     that a non-head may now decrease non-strictly. *)
  let loop_level_priorities ~id ~(query : Formula.t) ~(all_preds : Pred.t list)
      (preds : Pred.t list) : Ident.pvar -> int =
    let pri = Hashtbl.Poly.create () in
    let query_pvs = Formula.pvs_of query in
    let bodies_pvs =
      List.map all_preds ~f:(fun p -> (p.Pred.name, Formula.pvs_of p.Pred.body))
    in
    let entered_from_outside (node : Pred.t list) (v : Pred.t) =
      Set.mem query_pvs v.name
      || List.exists bodies_pvs ~f:(fun (q, pvs) ->
          Set.mem pvs v.name
          && not
               (List.exists node ~f:(fun p -> Ident.pvar_equal p.Pred.name q)))
    in
    let is_mu (pred : Pred.t) =
      match pred.kind with Predicate.Mu -> true | _ -> false
    in
    let calls_itself (pred : Pred.t) =
      Set.mem (Formula.pvs_of pred.body) pred.name
    in
    let set d (pred : Pred.t) =
      Hashtbl.Poly.set pri ~key:pred.name ~data:d;
      Debug.print ~id
      @@ lazy
           (sprintf "%s has the loop level priority %d"
              (Ident.name_of_pvar pred.name)
              d)
    in
    (* [node]: a strongly connected list of predicates in the order of
       [preds], with a cycle *)
    let rec decompose depth (node : Pred.t list) =
      let head =
        match
          List.find node ~f:(fun p -> is_mu p && entered_from_outside node p)
        with
        | Some h -> Some h
        | None -> List.find node ~f:is_mu
      in
      match head with
      | None -> List.iter node ~f:(set (2 * depth))
      | Some head ->
          set ((2 * depth) - 1) head;
          let rest =
            List.filter node ~f:(fun p ->
                not (Ident.pvar_equal p.Pred.name head.name))
          in
          let comps = call_graph_sccs rest in
          let in_comp = Hash_set.Poly.create () in
          List.iter comps ~f:(fun comp ->
              let comp =
                List.map (List.sort comp ~compare:Int.compare)
                  ~f:(List.nth_exn rest)
              in
              List.iter comp ~f:(fun p -> Hash_set.add in_comp p.Pred.name);
              match comp with
              | [ p ] when not (calls_itself p) -> set (2 * depth) p
              | _ -> decompose (depth + 1) comp);
          List.iter rest ~f:(fun p ->
              if not (Hash_set.mem in_comp p.Pred.name) then set (2 * depth) p)
    in
    decompose 1 preds;
    fun p -> Hashtbl.Poly.find_exn pri p

  (* [alternation_depths ~id dg0 preds]: the alternation depth of every
     predicate of [preds] (a list in equation order; [dg0] is
     [DepGraph.gen_init_graph] of the query and [preds]) and their maximum.
     Visiting the predicates from the last equation to the first, the depth of
     [P_i] is 1, or the largest of [a_j] (same fixpoint kind) and [a_j + 1]
     (different kind) over the later predicates [P_j] such that [P_i] and [P_j]
     lie on a common cycle of the dependency graph restricted to the
     predicates after [P_i] (and [P_i] itself) -- [DepGraph.k_transitive_closure]
     at [i].  [Mu] and [Nu] are two kinds; [mu_or_nu] says how a [MuOrNu]
     predicate compares: [`As_nu] (the default) reads it as [Nu], and
     [`Either] as the same kind as whichever predicate it is compared with, so
     that it never adds an alternation.

     [`As_nu] is the reading of a system with every [MuOrNu] set to [Nu], which
     has the same solution when every [MuOrNu] predicate meets its cut-point
     condition (every cycle through it passes an earlier [Mu] or [Nu]
     predicate), so the priorities the reduction derives from it are sound.
     [`Either] is invariant under swapping every [Mu] and [Nu] (the dual keeps
     [MuOrNu]), as the alternation depth of a system should be, and is what
     the statistics report; but it is not the depth of any one setting of the
     [MuOrNu] kinds, and priorities derived from it can be unsound: in a
     component [X1 : Nu], [X2 : Mu], [X3 : MuOrNu] with edges [X1 -> X2],
     [X2 -> X3], [X3 -> X1] and [X3 -> X2], it gives [X2] and [X3] depth 1 and
     [X1] depth 2, hence priorities 3 to [X2] (odd, [Mu]) and 2 to [X3] (even),
     and the walk cycling through [X2] and [X3] alone -- rejected, since its
     least predicate [X2] is [Mu] -- has even least priority.  Assumes [preds]
     is non-empty (the maximum of no depths is undefined); guarantees every
     depth is at least 1. *)
  let alternation_depths ?(mu_or_nu = `As_nu) ~id (dg0 : DepGraph.t)
      (preds : Pred.t list) =
    let same_kind k1 k2 =
      match (mu_or_nu, k1, k2) with
      | `Either, Predicate.MuOrNu, _ | `Either, _, Predicate.MuOrNu -> true
      | _ ->
          let is_mu = function Predicate.Mu -> true | _ -> false in
          Bool.equal (is_mu k1) (is_mu k2)
    in
    let pvs = Set.Poly.of_list @@ List.map preds ~f:(fun pred -> pred.name) in
    let rec loop alt_dep = function
      | [] -> alt_dep
      | (name_i, kind_i, i) :: pvars' ->
          let ai =
            let dg = DepGraph.k_transitive_closure dg0 i in
            Debug.print ~id
            @@ lazy
                 (sprintf "************ k-reachability analysis:\n%s"
                    (DepGraph.str_of dg));
            Integer.max_list
            @@ 1
               :: List.filter_map alt_dep ~f:(fun (name_j, kind_j, aj) ->
                   let open DepGraph in
                   if
                     Set.exists pvs ~f:(fun k ->
                         (name_i =->* k) dg && (k =-> name_j) dg)
                     && Set.exists pvs ~f:(fun k ->
                         (name_j =->* k) dg && (k =-> name_i) dg)
                   then
                     if same_kind kind_i kind_j then Some aj
                     else Some (1 + aj)
                   else None)
          in
          Debug.print ~id
          @@ lazy
               (sprintf "%s has the alternation depth of %d"
                  (Ident.name_of_pvar name_i)
                  ai);
          loop ((name_i, kind_i, ai) :: alt_dep) pvars'
    in
    let res =
      List.map ~f:(fun (name_i, _, ai) -> (name_i, ai))
      @@ loop [] @@ List.rev
      @@ List.mapi preds ~f:(fun i pred -> (pred.name, pred.kind, i))
    in
    (Map.Poly.of_alist_exn res, Integer.max_list @@ List.map ~f:snd res)

  let elim_mu_ppm_scc ?(id = None) ~(all_preds : Pred.t list)
      (use_alt_dep, pack_rank_components, loop_levels, loop_levels_from)
      (query : Formula.t) (preds : Pred.t list) scc_i =
    let (dg0 : DepGraph.t) = DepGraph.gen_init_graph query preds in
    Debug.print ~id
    @@ lazy
         (sprintf "************ DepGraph for the %s SCC:\n%s"
            (Ordinal.string_of (Ordinal.make (scc_i + 1)))
            (DepGraph.str_of dg0));
    let sorts_map =
      Hashtbl.Poly.of_alist_exn
      @@ List.map preds ~f:(fun pred ->
          ( Ident.pvar_to_tvar pred.name,
            List.map ~f:(snd >> Logic.ExtTerm.of_old_sort) pred.args ))
    in
    let nwf =
      if use_alt_dep then (
        let alt_dep, amax = alternation_depths ~id dg0 preds in
        Debug.print ~id @@ lazy (sprintf "amax = %d" amax);
        (* [pri0]: the priority of Def. 7.7's reassignment, [2 + amax - alpha]
           lowered to the parity of the predicate's kind (odd for a least
           fixpoint, even otherwise) *)
        let pri0 =
          Map.Poly.of_alist_exn
          @@ List.map preds ~f:(fun pred ->
              let pri = 2 + amax - Map.Poly.find_exn alt_dep pred.Pred.name in
              ( pred.Pred.name,
                match pred.Pred.kind with
                | Predicate.(Nu | MuOrNu) -> if pri mod 2 = 0 then pri else pri - 1
                | Predicate.Mu -> if pri mod 2 = 0 then pri - 1 else pri ))
        in
        let use_loop_levels =
          loop_levels
          && List.for_all preds ~f:(fun pred ->
              match pred.Pred.kind with Predicate.Nu -> false | _ -> true)
        in
        (* [priorities_of ~what ~floor pri_of]: the family's priorities for
           the priority function [pri_of] -- the number of ranking components,
           the priority of each predicate, the truncation and the accepting
           set -- where [floor] is a lower bound on the largest priority
           ([amax + 1] for alternation depth, so that its accepting set is
           Def. 7.7's even numbers up to [amax + 1]) *)
        let priorities_of ~what ~floor pri_of : Kind.priorities =
          (* the largest priority actually assigned: [amax + 1] from
             alternation depth, or twice the depth of the loop hierarchy *)
          let pmax =
            Integer.max_list
            @@ floor :: List.map preds ~f:(fun pred -> pri_of pred.Pred.name)
          in
          (* [max_pri] is the number of ranking components and [trunc] maps a
             priority to how many of them it compares: all [pmax] with the
             identity (Def. 7.7), or packed in pairs, ceil(pmax/2) and
             ceil(p/2) (Def. 7.8).  The priorities and the accepting set are
             the same either way, so every consumer must test acceptance on
             the priority and use [trunc] only for the component count. *)
          let max_pri =
            if pack_rank_components then
              if pmax mod 2 = 0 then pmax / 2 else (pmax + 1) / 2
            else pmax
          in
          Debug.print ~id @@ lazy (sprintf "#ord%s = %d" what max_pri);
          let trunc =
            if pack_rank_components then fun sigma_i ->
              if sigma_i mod 2 = 0 then sigma_i / 2 else (sigma_i + 1) / 2
            else Fn.id
          in
          let sigma =
            Map.Poly.of_alist_exn
            @@ List.map preds ~f:(fun pred ->
                let pri = pri_of pred.Pred.name in
                Debug.print ~id
                @@ lazy
                     (sprintf "%s has the priority of %d |-> #%d%s"
                        (Ident.name_of_pvar pred.name)
                        pri (trunc pri) what);
                (Ident.pvar_to_tvar pred.name, pri))
          in
          (* the even priorities up to [pmax]: from alternation depth these
             are those up to [amax + 1], as in Def. 7.7 *)
          let acc_set =
            Set.Poly.of_list @@ List.init (pmax / 2) ~f:(fun i -> 2 * (i + 1))
          in
          Debug.print ~id
          @@ lazy
               (sprintf "acc_set%s: %s" what
                  (String.concat_map_set ~sep:"," acc_set ~f:string_of_int));
          (max_pri, sigma, trunc, acc_set)
        in
        let ad_priorities () =
          priorities_of ~what:"" ~floor:(amax + 1) (Map.Poly.find_exn pri0)
        in
        let loop_priorities ~what =
          priorities_of ~what ~floor:1
            (loop_level_priorities ~id ~query ~all_preds preds)
        in
        (* With [First_shape_failure] the family starts with alternation
           depth's priorities and carries the loop-hierarchy ones as its
           switch.  The pair meets the switch's contract (see
           [Kind.priority_switch]): both priority functions are sound for a
           component with no [Nu] predicate, and a closed walk of such a
           component has a rejecting least priority under either exactly when
           it visits a [Mu] predicate -- alternation depth gives every [Mu]
           predicate 1 and every [Fix] one 2, and under the loop levels a
           closed walk meets the head of the smallest node holding it, odd and
           least in that node, whenever the node has a [Mu] predicate.  Two
           equal priority functions (a hierarchy giving every [Mu] predicate 1
           and every [Fix] one 2) carry no switch: a single self-recursive
           least fixpoint is the common case. *)
        let (max_pri, sigma, trunc, acc_set), priority_switch =
          if not use_loop_levels then (ad_priorities (), None)
          else
            match loop_levels_from with
            | Config.Reduction -> (loop_priorities ~what:"", None)
            | Config.Reduction_unless_unrankable ->
                (* the [Reduction] family, carrying alternation depth's
                   priorities as a switch the template takes before its first
                   generation when the family's bare transitions are known
                   to be unrankable; the pair meets the switch's contract as
                   below, the contract being symmetric in the two priority
                   functions *)
                let ((max_pri0, sigma0, _, acc0) as initial) =
                  loop_priorities ~what:""
                in
                let ((max_pri1, sigma1, _, acc1) as target) = ad_priorities () in
                if
                  max_pri0 = max_pri1
                  && Map.Poly.equal Int.equal sigma0 sigma1
                  && Map.Poly.for_all sigma0 ~f:(fun p ->
                      Bool.equal (Set.mem acc0 p) (Set.mem acc1 p))
                then (initial, None)
                else
                  ( initial,
                    Some
                      Kind.
                        {
                          target;
                          switched = Stdlib.Atomic.make false;
                          gate = Kind.Unrankable_at_start;
                        } )
            | (Config.First_shape_failure | Config.First_rankable_shape_failure)
              as from ->
                let gate =
                  match from with
                  | Config.First_rankable_shape_failure ->
                      Kind.Rankable_shape_failure
                  | _ -> Kind.Any_shape_failure
                in
                let ((max_pri0, sigma0, _, acc0) as initial) =
                  ad_priorities ()
                in
                let ((max_pri1, sigma1, _, acc1) as target) =
                  loop_priorities ~what:" after the switch"
                in
                (* equal as the template and the labeler read them: the
                   component count, and per predicate its priority and whether
                   that priority accepts (the accepting sets themselves may
                   differ in priorities no predicate has) *)
                if
                  max_pri0 = max_pri1
                  && Map.Poly.equal Int.equal sigma0 sigma1
                  && Map.Poly.for_all sigma0 ~f:(fun p ->
                      Bool.equal (Set.mem acc0 p) (Set.mem acc1 p))
                then (initial, None)
                else
                  ( initial,
                    Some
                      Kind.
                        {
                          target;
                          switched = Stdlib.Atomic.make false;
                          gate;
                        } )
        in
        if Option.is_some priority_switch then
          Debug.print ~id
          @@ lazy (sprintf "PR%d carries a priority switch" scc_i);
        Kind.
          {
            name = Ident.Tvar ("PR" ^ string_of_int scc_i);
            sorts_shared = [];
            sorts_map;
            max_pri;
            sigma;
            trunc;
            acc_set;
            priority_switch;
          })
      else
        let max_pri = List.length preds in
        Debug.print ~id @@ lazy (sprintf "#ord = %d" max_pri);
        let trunc = Fn.id in
        let sigma =
          Map.Poly.of_alist_exn
          @@ List.mapi preds ~f:(fun i pred ->
              let pri = i + 1 in
              Debug.print ~id
              @@ lazy
                   (sprintf "%s has the priority of %d |-> #%d"
                      (Ident.name_of_pvar pred.name)
                      pri (trunc pri));
              (Ident.pvar_to_tvar pred.name, pri))
        in
        let acc_set =
          Set.Poly.of_list
          @@ List.filter_map preds ~f:(fun pred ->
              match pred.Pred.kind with
              | Predicate.(Nu | MuOrNu) ->
                  Some (Map.Poly.find_exn sigma (Ident.pvar_to_tvar pred.name))
              | Predicate.Mu -> None)
        in
        Debug.print ~id
        @@ lazy
             (sprintf "acc_set: %s"
                (String.concat_map_set ~sep:"," acc_set ~f:string_of_int));
        Kind.
          {
            name = Ident.Tvar ("PR" ^ string_of_int scc_i);
            sorts_shared = [];
            sorts_map;
            max_pri;
            sigma;
            trunc;
            acc_set;
            priority_switch = None;
          }
    in
    let rec inner nu_only wfpvs = function
      | [] ->
          ( nu_only,
            Set.fold ~init:(Map.Poly.empty, Map.Poly.empty) wfpvs
              ~f:(fun acc (l, r) ->
                let wftvar = Kind.parity_tvar_of_nwf nwf l r in
                Kind.add_pred_env_set acc
                  (Kind.Parity (nwf, (l, r)))
                  (Set.Poly.singleton
                     ( Ident.tvar_to_pvar wftvar,
                       List.map ~f:Logic.ExtTerm.to_old_sort
                       @@ Hashtbl.Poly.find_exn nwf.sorts_map l
                       @ Hashtbl.Poly.find_exn nwf.sorts_map r ))) )
      | (pred : Pred.t) :: rest ->
          let sigma =
            Set.Poly.filter_map ~f:(fun (pvar_r, sorts_r) ->
                if
                  List.for_all preds ~f:(fun pred ->
                      not @@ Ident.pvar_equal pvar_r pred.name)
                then None
                else
                  let params_r = mk_fresh_sort_env_list sorts_r in
                  let phi =
                    let terms_r = Term.of_sort_env params_r in
                    let wftvar =
                      Ident.mk_parity_tvar nwf.name
                        (Ident.Tvar
                           (Ident.name_of_pvar pred.name
                           ^ "@" ^ string_of_int
                           @@ Map.Poly.find_exn nwf.sigma
                           @@ Ident.pvar_to_tvar pred.name))
                        (Ident.Tvar
                           (Ident.name_of_pvar pvar_r ^ "@" ^ string_of_int
                           @@ Map.Poly.find_exn nwf.sigma
                           @@ Ident.pvar_to_tvar pvar_r))
                    in
                    Formula.and_of
                      [
                        (* (co-)recursion *)
                        Formula.mk_atom
                        @@ Atom.mk_pvar_app pvar_r sorts_r terms_r;
                        (* guard *)
                        Formula.mk_atom
                        @@ Atom.mk_pvar_app
                             (Ident.tvar_to_pvar wftvar)
                             (List.map ~f:snd pred.args @ sorts_r)
                             (Term.of_sort_env pred.args @ terms_r);
                      ]
                  in
                  Some (pvar_r, (params_r, phi)))
            @@ Set.filter
                 ~f:(fst >> Ident.pvar_to_tvar >> Hashtbl.Poly.mem sorts_map)
            @@ Formula.pred_sort_env_of pred.body
          in
          let wfpvs' =
            Set.union wfpvs
              (Set.Poly.map sigma ~f:(fun (pvar_r, _) ->
                   (Ident.pvar_to_tvar pred.name, Ident.pvar_to_tvar pvar_r)))
          in
          let nu_only' =
            {
              pred with
              kind = Predicate.Nu;
              body = Formula.subst_preds (Map.of_set_exn sigma) pred.body;
            }
            :: nu_only
          in
          inner nu_only' wfpvs' rest
    in
    inner [] Set.Poly.empty (List.rev preds)

  let elim_mu_ppm ?(id = None)
      ( use_scc,
        use_alt_dep,
        pack_rank_components,
        loop_levels,
        loop_levels_from )
      (query : Formula.t) (preds : Pred.t list) unknowns =
    let sccs =
      if use_scc then call_graph_sccs preds
      else [ List.init (List.length preds) ~f:Fn.id ]
    in
    let all_preds = preds in
    let predss, res =
      List.unzip
      @@ List.mapi sccs ~f:(fun scc_i scc ->
          let preds =
            List.filter_mapi preds ~f:(fun i pred ->
                if List.mem scc i ~equal:Int.equal then Some pred else None)
          in
          if
            List.for_all preds ~f:(fun pred ->
                match pred.Pred.kind with Predicate.Mu -> false | _ -> true)
          then (preds, (Map.Poly.empty, Map.Poly.empty))
          else
            elim_mu_ppm_scc
              (use_alt_dep, pack_rank_components, loop_levels, loop_levels_from)
              ~id ~all_preds query preds scc_i)
    in
    ( ( query,
        List.concat
        @@ List.filter_map preds ~f:(fun pred ->
               let pvs_body = Formula.pvs_of pred.body in
               if
                 List.for_all preds ~f:(fun pred' ->
                     not @@ Set.mem pvs_body pred'.name)
               then Some { pred with kind = Predicate.Nu }
               else None)
           :: predss ),
      let senvs, kind_maps = List.unzip res in
      ( Map.force_merge_list @@ (fst unknowns :: senvs),
        Map.force_merge_list @@ (snd unknowns :: kind_maps) ) )

  (* [layout] is filled by [Wf_reduction] only (see [ufp_of]); the parity progress
     measure prepends no copy. *)
  let elim_mu ?(id = None) ?(conv_nu = false) ?layout (muclp : Problem.t)
      unknowns =
    (match config.reduction with
    | Parity_progress_measure
        {
          use_scc;
          alternation_depth;
          pack_rank_components;
          loop_levels;
          loop_levels_from;
        } ->
        elim_mu_ppm ~id
          ( use_scc,
            alternation_depth,
            pack_rank_components,
            loop_levels,
            loop_levels_from )
    | Wf_reduction
        { restrict_ranking_to_cycles; record_on_head; one_relation_per_block } ->
        elim_mu_bra ~id ~conv_nu ?layout ~record_on_head ~one_relation_per_block
          (config.use_dwf, restrict_ranking_to_cycles))
      muclp.query muclp.preds unknowns

  (* [scc_alternation_depths ~id muclp]: the strongly connected components
     the parity-progress-measure reduction with [use_scc] decomposes
     [muclp]'s predicates into, with the alternation depth it assigns
     priorities from.  One entry per component of the call graph
     ([call_graph_sccs]: an edge from [P] to [Q] when [Q] occurs in [P]'s
     body), in that function's order, as
     [(size, cyclic, has_mu, amax, amax_as_nu)]: [cyclic] when the component
     has a cycle (two or more predicates, or one that calls itself), [has_mu]
     when it holds a [Mu] predicate (the components the reduction ranks, when
     cyclic), [amax] the largest [alternation_depths ~mu_or_nu:`Either] of its
     predicates (a [MuOrNu] predicate adds no alternation, so the value is the
     same on a problem and its dual), and [amax_as_nu] the largest with
     [MuOrNu] read as [Nu], the depth [elim_mu_ppm_scc] assigns priorities
     from; both are computed on the component alone, as [elim_mu_ppm_scc]
     computes them.  Reads [muclp] only; reduces nothing. *)
  let scc_alternation_depths ?(id = None) (muclp : Problem.t) =
    let preds = muclp.preds in
    List.map (call_graph_sccs preds) ~f:(fun scc ->
        let comp =
          List.filter_mapi preds ~f:(fun i pred ->
              if List.mem scc i ~equal:Int.equal then Some pred else None)
        in
        let cyclic =
          match comp with
          | [ p ] -> Set.mem (Formula.pvs_of p.Pred.body) p.Pred.name
          | _ -> true
        in
        let has_mu =
          List.exists comp ~f:(fun p ->
              match p.Pred.kind with Predicate.Mu -> true | _ -> false)
        in
        let dg = DepGraph.gen_init_graph muclp.query comp in
        let _, amax = alternation_depths ~mu_or_nu:`Either ~id dg comp in
        let _, amax_as_nu = alternation_depths ~mu_or_nu:`As_nu ~id dg comp in
        (List.length comp, cyclic, has_mu, amax, amax_as_nu))

  (* [layout], when given, receives the prepended argument positions of every
     predicate the reduction extends, keyed by the predicate's name in [muclp]
     (see [prefix_entry]); a predicate it does not hold was not extended. *)
  (* [name_multiplied_parts ~bound (exi_senv, kind_map) clauses]: every clause
     of [clauses] (a universal environment and a quantifier-free formula, as
     [elim_nu] returns them) whose clausal form is predicted to have more than
     [bound] clauses is replaced by the clauses of
     [DefinitionalCnf.split], and the fresh unknowns it introduces are added to
     the environment as ordinary unknowns and registered with
     [PCSP.Parser.add_premise_names], so that no preprocessing step resolves
     one away (which would substitute the named conjunction back and rebuild
     the product).  A clause within the bound is returned as it was.

     Why: a muCLP whose predicate bodies compose every loop-free path between
     two cut points of a transition system is a conjunction over branches of
     [guard => successor] on the proving side, whose clausal form is linear;
     its dual is the disjunction over branches of [guard /\ successor], with
     each existential choice skolemised into a disjunction [not FN(..) \/ ..]
     inside, and the clausal form of a disjunction of conjunctions is the
     product of theirs.  On one integer transition system with 425 locations
     one dual clause of 22,835 nodes had about 2 x 10^10 clauses, and every
     pass that put the problem in clausal form (the function reconstruction,
     the witness seeds, the predicate elimination) never finished.

     Sound both ways in every model of the theory ([DefinitionalCnf.split]):
     the problem with the fresh unknowns is satisfiable iff the original is,
     and a solution restricted to the original unknowns solves the original,
     so a verdict and every partial solution exchanged over the original
     predicates mean what they meant.  The kinds of the original unknowns are
     untouched. *)
  (* [~gain]: [DefinitionalCnf.split ~gain] -- a disjunct is named only where
     naming it shortens the clausal form, and a clause in which nothing is
     then named is returned as it was (its clausal form is the plain one,
     within the bound times its size) *)
  let name_multiplied_parts ?(gain = false) ?(shared_args = false) ~bound
      (exi_senv, kind_map) clauses =
    let unknowns = Map.key_set exi_senv in
    let added = ref Map.Poly.empty in
    let fresh () =
      Ident.tvar_to_pvar
      @@ Ident.mk_fresh_tvar_avoiding ~prefix:"Dmu"
           ~taken:(fun v ->
             Map.Poly.mem exi_senv v || Map.Poly.mem !added v
             || Set.exists clauses ~f:(fun (senv, _) -> Map.Poly.mem senv v))
           ()
    in
    let clauses =
      Set.concat_map clauses ~f:(fun (senv, phi) ->
          let body = Formula.nnf_of phi in
          if DefinitionalCnf.predicted_cnf_clauses unknowns body <= bound then
            Set.Poly.singleton (senv, phi)
          else
            let phis, defs =
              DefinitionalCnf.split ~fewest:true ~gain ~shared_args ~bound
                ~unknowns ~universals:(Map.to_set senv) ~fresh body
            in
            if gain && List.is_empty defs then Set.Poly.singleton (senv, phi)
            else (
              List.iter defs ~f:(fun (pvar, sorts) ->
                  added :=
                    Map.Poly.set !added ~key:(Ident.pvar_to_tvar pvar)
                      ~data:(pvar, sorts));
              Set.Poly.of_list @@ List.map phis ~f:(fun phi -> (senv, phi))))
    in
    if Map.Poly.is_empty !added then ((exi_senv, kind_map), clauses)
    else (
      PCSP.Parser.add_premise_names (Map.Poly.key_set !added);
      ( Kind.add_pred_env_set (exi_senv, kind_map) Kind.Ord
          (Set.Poly.of_list (Map.Poly.data !added)),
        clauses ))

  (* [factor_exclusive_guards (exi_senv, _) clauses]: every clause (a
     universal environment and a formula, as [elim_nu] returns them) put in
     negation normal form and through [ExclusiveGuards.factor], which rewrites
     each disjunction of conjunctions whose pure parts are pairwise exclusive
     into the conjunction of the pure parts' disjunction and one [not guard \/
     rest] per branch; a clause it does not change is returned as it was.

     Exact: each rewritten clause is equivalent to the original at every
     valuation, in every model of the theory and under every interpretation of
     the unknowns, over the same atoms, with no fresh symbol, so the problem's
     solutions, kinds, verdict and every partial solution exchanged between
     the two sides are the original's.  What changes is the clausal form later
     passes build: the dual of a transition system's muCLP is, at each
     location, a disjunction over the outgoing transitions of [guard /     successor], and where the guards exclude one another (an if-then-else)
     the factored form's clausal form is the sum of the branches' instead of
     their product. *)
  let factor_exclusive_guards (exi_senv, _) clauses =
    let unknowns = Map.key_set exi_senv in
    let trace = Option.is_some (Stdlib.Sys.getenv_opt "COAR_EXCLUSIVE_GUARDS") in
    Set.Poly.map clauses ~f:(fun (senv, phi) ->
        match
          ExclusiveGuards.factor_with_stats ~unknowns (Formula.nnf_of phi)
        with
        | None, _ -> (senv, phi)
        | Some phi', st ->
            if trace then
              Stdlib.Printf.eprintf
                "[exclusive-guards] rewritten=%d grouped=%d predicted %d -> %d\n%!"
                st.ExclusiveGuards.rewritten st.grouped st.before st.after;
            (senv, phi'))

  (* [merge_witnesses (exi_senv, kind_map) queries clauses]: every clause and
     query put in negation normal form and through
     [ExclusiveGuards.merge_witness_copies], repeated until it renames nothing
     (a renaming can make two atoms' leading arguments equal), for the
     functional unknowns that occur only negatively in the queries and
     clauses together; a formula it does not change is returned as it was.

     Equisatisfiable per model, verdict and the other unknowns' solutions
     unchanged: a functional unknown that occurs only negatively may be read
     single-valued, and then the copies of its witness variable in one clause
     denote the same value (the contract of [merge_witness_copies]).  What
     changes is the problem's shape: branches that test one choice test one
     variable, so [factor_exclusive_guards] after it sees their guards
     exclude one another.  Only [FN] unknowns are read, so the result is the
     input on a problem without them. *)
  let merge_witnesses (exi_senv, kind_map) queries clauses =
    let fn_pvars =
      Map.Poly.fold kind_map ~init:Set.Poly.empty ~f:(fun ~key ~data acc ->
          if Kind.is_fn data && Map.Poly.mem exi_senv key then
            Set.add acc (Ident.tvar_to_pvar key)
          else acc)
    in
    if Set.is_empty fn_pvars then (queries, clauses)
    else
      let nnf = Set.Poly.map ~f:(fun (senv, phi) -> (senv, Formula.nnf_of phi)) in
      let queries = nnf queries and clauses = nnf clauses in
      (* the unknowns applied positively anywhere, read on negation normal
         forms: an atom not directly under a negation *)
      let positive =
        let acc = ref Set.Poly.empty in
        let rec go = function
          | Formula.Atom (Atom.App (Predicate.Var (p, _), _, _), _) ->
              acc := Set.add !acc p
          | Formula.UnaryOp (Not, Formula.Atom _, _) -> ()
          | Formula.UnaryOp (_, phi, _) -> go phi
          | Formula.BinaryOp (_, a, b, _) -> go a; go b
          | Formula.Bind (_, _, phi, _) -> go phi
          | Formula.LetRec _ as phi ->
              (* not read: every unknown under it counts as positive *)
              acc := Set.union !acc (Formula.pvs_of phi)
          | Formula.LetFormula (_, _, _, phi, _) -> go phi
          | Formula.Atom _ -> ()
        in
        Set.iter (Set.union queries clauses) ~f:(fun (_, phi) -> go phi);
        !acc
      in
      let fns = Set.diff fn_pvars positive in
      let trace = Option.is_some (Stdlib.Sys.getenv_opt "COAR_EXCLUSIVE_GUARDS") in
      let one (senv, phi) =
        let rec loop phi total =
          match ExclusiveGuards.merge_witness_copies ~fns phi with
          | None -> (phi, total)
          | Some (phi', n) -> loop phi' (total + n)
        in
        let phi', n = loop phi 0 in
        if n > 0 && trace then
          Stdlib.Printf.eprintf "[merge-witnesses] renamed=%d\n%!" n;
        (senv, phi')
      in
      if Set.is_empty fns then (queries, clauses)
      else (Set.Poly.map queries ~f:one, Set.Poly.map clauses ~f:one)

  let f ?(id = None) ?(conv_nu = false) ?layout ?(factor_guards = false)
      ?(merge_witness_vars = false) ?name_bound ?name_gain ?name_shared_args
      ~exchange
      ~messenger (muclp : Problem.t) unknowns =
    (*Debug.set_id id;*)
    Debug.print ~id @@ lazy "**************** elim_mu ***********";
    let (query', preds'), nu_wfs =
      elim_mu ~id ~conv_nu ?layout muclp (Map.Poly.empty, Map.Poly.empty)
    in
    Debug.print ~id @@ lazy (Problem.str_of @@ Problem.make preds' query');
    Debug.print ~id @@ lazy "**************** elim_nu ***********";
    let (queries, clauses), (exi_senv, kind_map) =
      elim_nu query' preds'
        ( Map.force_merge (fst nu_wfs) (fst unknowns),
          Map.force_merge (snd nu_wfs) (snd unknowns) )
    in
    let queries, clauses =
      if not merge_witness_vars then (queries, clauses)
      else
        Common.PhaseTime.with_phase "merge-witnesses" @@ fun () ->
        merge_witnesses (exi_senv, kind_map) queries clauses
    in
    let queries, clauses =
      if not factor_guards then (queries, clauses)
      else
        Common.PhaseTime.with_phase "factor-exclusive-guards" @@ fun () ->
        ( factor_exclusive_guards (exi_senv, kind_map) queries,
          factor_exclusive_guards (exi_senv, kind_map) clauses )
    in
    let (exi_senv, kind_map), clauses =
      match name_bound with
      | None -> ((exi_senv, kind_map), clauses)
      | Some bound ->
          Common.PhaseTime.with_phase "name-multiplied-parts" @@ fun () ->
          name_multiplied_parts ?gain:name_gain ?shared_args:name_shared_args
            ~bound
            (exi_senv, kind_map) clauses
    in
    let clauses, stable_clauses =
      if exchange then
        (* exchange learned clauses*)
        ( clauses,
          Set.concat_map queries ~f:(fun (param_senv, phi) ->
              let uni_senv = Logic.of_old_sort_env_map param_senv in
              phi |> Logic.ExtTerm.of_old_formula |> Logic.ExtTerm.nnf_of
              |> Logic.ExtTerm.cnf_of exi_senv uni_senv
              |> Set.Poly.map ~f:(fun (ps, ns, phi) -> (uni_senv, ps, ns, phi)))
        )
      else (Set.union clauses queries, Set.Poly.empty)
    in
    let params =
      let arg_original_names =
        Map.Poly.of_alist_exn
        @@ List.map muclp.preds ~f:(fun (pred : Pred.t) ->
            (pred.name, pred.arg_original_names))
      in
      (* Carry the datatype and function environments into the constraint
         problem this reduction produces.  A fixpoint-logic problem has nowhere
         to hold them -- it has no such field -- so between the two constraint
         problems they live only in the process-wide environments, and one
         built without them declares none to its consumers. *)
      PCSP.Params.make ~arg_original_names ~kind_map ~messenger ~id
        ~stable_clauses ~dtenv:(LogicOld.get_dtenv ())
        ~fenv:(LogicOld.get_fenv ()) exi_senv
    in
    (PCSP.Problem.of_old_formulas ~params clauses (* Insert metadata *), nu_wfs)
end
