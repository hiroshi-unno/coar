open Core
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

type examples = ClauseGraph.t

(* hypothesis space of function variables *)
type hspaces = (Ident.tvar, HypSpace.hspace) Hashtbl.Poly.t
type truth_table = TruthTable.t
type labeling = (Ident.pvar, (int, int) Map.Poly.t) Map.Poly.t * bool

type heat_map =
  (unit (*BMIsvm.Model.t*) * (string, int) Hashtbl.Poly.t) option ref

type fenv = FunEnv.t
type uenv = UTermEnv.t
type learned_clauses = Clause.t Hash_set.Poly.t
type lower_bounds = (Ident.tvar, Logic.term) Hashtbl.Poly.t
type upper_bounds = (Ident.tvar, Logic.term) Hashtbl.Poly.t

type t = {
  examples : examples;
  hspaces : hspaces;
  truth_table : truth_table;
  labelings : labeling list;
  heat_map : heat_map;
  fenv : fenv;
  uenv : uenv;
  oracle : PCSP.Problem.oracle;
  learned_clauses : learned_clauses;
  lower_bounds : lower_bounds; (* learned clauses by primal *)
  upper_bounds : upper_bounds; (* learned clauses by dual *)
  assumed_clauses : Clause.t Hash_set.Poly.t;
      (* learned clauses that came over the messenger: they are hard clauses
         for the solver but not consequences of the problem, so a refutation
         using them is conditional *)
  unsat_witness : UnsatWitness.t option ref;
      (* set by the component that concludes [State.Unsat]; read by the
         coordinator; shared by [{t with ...}] copies *)
  witness : WitnessConfig.t;
      (* what to record; every recording site checks it here *)
  kind_certs : (Ident.tvar, KindCert.t) Hashtbl.Poly.t;
      (* the kind certificates of the latest candidate, per predicate *)
  synthesis_stalled : bool ref;
      (* set by the synthesis phase when it gives up on a round without
         proposing anything, cleared when it proposes again; read by the phases
         after it, which is how a mechanism that is worth its cost only where
         the loop is stuck can be switched on just there.  It lives here rather
         than in a module-level reference because this record is per problem,
         where a global would be shared by every solver domain.  Shared by
         [{t with ...}] copies, like [unsat_witness] above. *)
}

let init ?(witness = WitnessConfig.default) oracle =
  {
    examples = ClauseGraph.create ();
    synthesis_stalled = ref false;
    hspaces = Hashtbl.Poly.create ();
    truth_table = TruthTable.create ();
    labelings = [ (Map.Poly.empty (*ToDo*), false (*ToDo*)) ];
    heat_map = ref None;
    fenv = Map.Poly.empty;
    uenv = UTermEnv.create ();
    oracle;
    learned_clauses = Hash_set.Poly.create ();
    lower_bounds = Hashtbl.Poly.create ();
    upper_bounds = Hashtbl.Poly.create ();
    assumed_clauses = Hash_set.Poly.create ();
    unsat_witness = ref None;
    witness;
    kind_certs = Hashtbl.Poly.create ();
  }

let clone t =
  {
    examples = ClauseGraph.clone t.examples;
    hspaces = Hashtbl.Poly.copy t.hspaces;
    truth_table = TruthTable.clone t.truth_table;
    labelings = t.labelings;
    heat_map = ref !(t.heat_map);
    fenv = t.fenv;
    uenv = UTermEnv.clone t.uenv;
    oracle = t.oracle;
    learned_clauses = Hash_set.Poly.copy t.learned_clauses;
    lower_bounds = Hashtbl.Poly.copy t.lower_bounds;
    upper_bounds = Hashtbl.Poly.copy t.upper_bounds;
    assumed_clauses = Hash_set.copy t.assumed_clauses;
    unsat_witness = t.unsat_witness;
    synthesis_stalled = t.synthesis_stalled;
    witness = t.witness;
    kind_certs = Hashtbl.copy t.kind_certs;
  }

let set_kind_certs t certs =
  List.iter certs ~f:(fun (pv, c) -> Hashtbl.set t.kind_certs ~key:pv ~data:c)

let set_unsat_witness t w = if t.witness.unsat then t.unsat_witness := Some w

(* [subst] is dropped unless [unsat_substitutions] is on (it is the only
   part of a witness whose cost grows with the number of examples) *)
let record_derivation ?(via = None) ?(premises = []) t ex ~rule ~subst =
  if t.witness.unsat then
    ClauseGraph.record_derivation ~via ~premises t.examples ex ~rule
      ~subst:(if t.witness.unsat_substitutions then subst else None)

(* the clauses an example was derived from, read off the clause graph;
   [Untracked] where the deriving component recorded no source *)
let sources_of_example t ex : UnsatWitness.source list =
  let v = ClauseGraph.Example ex in
  if not (ClauseGraph.G.mem_vertex t.examples.ClauseGraph.graph v) then
    [ UnsatWitness.Untracked ]
  else
    ClauseGraph.pred_clause_vertexs_of t.examples.ClauseGraph.graph v
    |> Set.to_list
    |> List.map ~f:(function
      | ClauseGraph.Clause ((_, ps, ns, _) as c) ->
          if
            Hash_set.exists t.assumed_clauses ~f:(fun (_, ps1, ns1, _) ->
                Set.equal ps ps1 && Set.equal ns ns1)
          then UnsatWitness.Assumed c
          else UnsatWitness.Clause c
      | ClauseGraph.Dummy | ClauseGraph.Example _ -> UnsatWitness.Untracked)

(* an example re-normalised after its derivation was recorded keeps it *)
let copy_derivation t ~from ~to_ =
  if t.witness.unsat then
    match ClauseGraph.derivation_of t.examples from with
    | Some d ->
        ClauseGraph.record_derivation ~via:d.ClauseGraph.via
          ~premises:d.ClauseGraph.premises t.examples to_
          ~rule:d.ClauseGraph.rule ~subst:d.ClauseGraph.subst
    | None -> ()

let witness_example t ex =
  UnsatWitness.
    {
      clause = ex;
      sources = sources_of_example t ex;
      derivation =
        Option.map (ClauseGraph.derivation_of t.examples ex) ~f:(fun d ->
            (d.ClauseGraph.rule, d.ClauseGraph.subst, d.ClauseGraph.via));
      parents =
        (let g = t.examples.ClauseGraph.graph in
         let v = ClauseGraph.Example ex in
         let from_graph =
           if ClauseGraph.G.mem_vertex g v then
             List.filter_map (ClauseGraph.G.pred g v) ~f:(function
               | ClauseGraph.Example e -> Some e
               | _ -> None)
           else []
         in
         (* the premises the deriving component named come first *)
         (match ClauseGraph.derivation_of t.examples ex with
           | Some d -> d.ClauseGraph.premises
           | None -> [])
         @ from_graph);
    }

let witness_examples t exs = List.map (Set.to_list exs) ~f:(witness_example t)
let examples_of t = ClauseGraph.examples_of t.examples
let pos_neg_und_examples_of t = ClauseGraph.pos_neg_und_examples_of t.examples

let hspace_of_pvar (Ident.Pvar name) t =
  match Hashtbl.Poly.find t.hspaces (Ident.Tvar name) with
  | Some cs -> cs
  | None ->
      let new_comp =
        HypSpace.
          {
            depth = -1;
            params = [];
            quals = Set.Poly.empty;
            qdeps = Map.Poly.empty;
            terms = Set.Poly.empty;
            consts = Set.Poly.empty;
          }
      in
      Hashtbl.Poly.add_exn t.hspaces ~key:(Ident.Tvar name) ~data:new_comp;
      new_comp

(* begin ParityPredicate / NWFPredicate *)

type parameter = {
  np : int;
  ndc : int;
  nl : int;
  depth : int;
  ubrc : Z.t option;
  ubrd : Z.t option;
  ubdc : Z.t option;
  ubdd : Z.t option;
  ds : Z.t Set.Poly.t;
}

type templ =
  | NWF of
      ((Ident.tvar, Term.t array array array) Hashtbl.t
      * (Ident.tvar, Term.t array array array) Hashtbl.t
      * (Ident.tvar, Term.t array array) Hashtbl.t)
  | Parity of
      ((Ident.tvar, Term.t array array array array) Hashtbl.t
      * (Ident.tvar, Term.t array array array array) Hashtbl.t
      * (Ident.tvar, Term.t array array) Hashtbl.t)

let shared_info :
    ( int option * Ident.tvar,
      (parameter ref * parameter ref)
      * (templ
        * (Ident.tvar, Formula.t Set.Poly.t * Term.t Set.Poly.t) Hashtbl.t) )
    Hashtbl.t =
  Hashtbl.Poly.create ()

let initialize_predicates id t kind_map (*quals_terms_map*) =
  Hashtbl.Poly.iteri t.hspaces ~f:(fun ~key ~data:_ ->
      match Map.Poly.find kind_map key with
      | Some (Kind.NWF (nwf, _)) -> (
          match Hashtbl.Poly.find shared_info (id, nwf.name) with
          | Some (_, (NWF (rcs, dcs, qds), qual_term_map)) ->
              Hashtbl.Poly.(
                clear rcs;
                clear dcs;
                clear qds;
                clear qual_term_map)
          | _ -> assert false)
      | Some (Kind.Parity (nwf, _)) -> (
          match Hashtbl.Poly.find shared_info (id, nwf.name) with
          | Some (_, (Parity (rcs, dcs, qds), qual_term_map)) ->
              Hashtbl.Poly.(
                clear rcs;
                clear dcs;
                clear qds;
                clear qual_term_map)
          | _ -> assert false)
      | _ -> ());
  Hashtbl.Poly.iteri t.hspaces ~f:(fun ~key ~data ->
      (*let ref_quals, ref_terms, _ref_consts =
        Map.Poly.find_exn quals_terms_map key
      in*)
      let quals0 = (*if true (*ToDo*) then !ref_quals else*) data.quals in
      let terms0 = (*if true (*ToDo*) then !ref_terms else*) data.terms in
      if false then (
        print_endline "qualifiers and terms for template generation:";
        print_endline
          (sprintf "quals: %s"
          @@ String.concat_map_set ~sep:"," quals0 ~f:Formula.str_of);
        print_endline
          (sprintf "terms: %s"
          @@ String.concat_map_set ~sep:"," terms0 ~f:Term.str_of));
      match Map.Poly.find kind_map key with
      | Some (Kind.NWF (nwf, (tag_l, tag_r))) ->
          let sorts_l = Hashtbl.Poly.find_exn nwf.sorts_map tag_l in
          let sorts_r = Hashtbl.Poly.find_exn nwf.sorts_map tag_r in
          let params_shared =
            LogicOld.sort_env_list_of_sorts ~pre:"" nwf.sorts_shared
          in
          let params_left =
            LogicOld.sort_env_list_of_sorts ~pre:""
              ~start:(List.length nwf.sorts_shared)
              sorts_l
          in
          let params_right =
            LogicOld.sort_env_list_of_sorts ~pre:""
              ~start:(List.length nwf.sorts_shared + List.length sorts_l)
              sorts_r
          in
          Hashtbl.Poly.update shared_info (id, nwf.name) ~f:(function
            | Some (params, (NWF templ, qual_term_map)) ->
                let _ =
                  let quals' =
                    Templ.quals_over_set quals0 (params_shared @ params_left)
                  in
                  let terms' =
                    Templ.terms_over_set terms0 (params_shared @ params_left)
                  in
                  Hashtbl.Poly.update qual_term_map tag_l ~f:(function
                    | Some (quals, terms) ->
                        (Set.union quals quals', Set.union terms terms')
                    | None -> (quals', terms'))
                in
                let ren =
                  ren_of_sort_env_list params_right
                    (LogicOld.sort_env_list_of_sorts ~pre:""
                       ~start:(List.length nwf.sorts_shared)
                       sorts_r)
                in
                let quals' =
                  Set.Poly.map ~f:(Formula.rename ren)
                  @@ Templ.quals_over_set quals0 (params_shared @ params_right)
                in
                let terms' =
                  Set.Poly.map ~f:(Term.rename ren)
                  @@ Templ.terms_over_set terms0 (params_shared @ params_right)
                in
                Hashtbl.Poly.update qual_term_map tag_r ~f:(function
                  | Some (quals, terms) ->
                      (Set.union quals quals', Set.union terms terms')
                  | None -> (quals', terms'));
                (params, (NWF templ, qual_term_map))
            | _ -> assert false)
      | Some (Kind.Parity (nwf, (tag_l, tag_r))) ->
          assert (List.is_empty nwf.sorts_shared);
          let sorts_l = Hashtbl.Poly.find_exn nwf.sorts_map tag_l in
          let sorts_r = Hashtbl.Poly.find_exn nwf.sorts_map tag_r in
          let params_left = LogicOld.sort_env_list_of_sorts ~pre:"" sorts_l in
          let params_right =
            LogicOld.sort_env_list_of_sorts ~pre:"" ~start:(List.length sorts_l)
              sorts_r
          in
          Hashtbl.Poly.update shared_info (id, nwf.name) ~f:(function
            | Some (params, (Parity templ, qual_term_map)) ->
                let _ =
                  let quals' = Templ.quals_over_set quals0 params_left in
                  let terms' = Templ.terms_over_set terms0 params_left in
                  if false then (
                    print_endline
                      (sprintf "quals0: %s"
                      @@ String.concat_map_set ~sep:"," quals0 ~f:Formula.str_of
                      );
                    print_endline
                      ("params_left: "
                      ^ String.concat_map_list ~sep:","
                          ~f:(fst >> Ident.name_of_tvar)
                          params_left);
                    print_endline
                      (sprintf "adding quals: %s"
                      @@ String.concat_map_set ~sep:"," quals' ~f:Formula.str_of
                      ));
                  Hashtbl.Poly.update qual_term_map tag_l ~f:(function
                    | Some (quals, terms) ->
                        (Set.union quals quals', Set.union terms terms')
                    | None -> (quals', terms'))
                in
                let ren =
                  ren_of_sort_env_list params_right
                    (LogicOld.sort_env_list_of_sorts ~pre:"" sorts_r)
                in
                let quals' =
                  Set.Poly.map ~f:(Formula.rename ren)
                  @@ Templ.quals_over_set quals0 params_right
                in
                let terms' =
                  Set.Poly.map ~f:(Term.rename ren)
                  @@ Templ.terms_over_set terms0 params_right
                in
                if false then (
                  print_endline
                    (sprintf "quals0: %s"
                    @@ String.concat_map_set ~sep:"," quals0 ~f:Formula.str_of);
                  print_endline
                    ("params_right: "
                    ^ String.concat_map_list ~sep:","
                        ~f:(fst >> Ident.name_of_tvar)
                        params_left);
                  print_endline
                    (sprintf "adding quals: %s"
                    @@ String.concat_map_set ~sep:"," quals' ~f:Formula.str_of));
                Hashtbl.Poly.update qual_term_map tag_r ~f:(function
                  | Some (quals, terms) ->
                      (Set.union quals quals', Set.union terms terms')
                  | None -> (quals', terms'));
                (params, (Parity templ, qual_term_map))
            | _ -> assert false)
      | _ -> ())

(* end ParityPredicate / NWFPredicate *)

let terms_of_pvar pvar t = (hspace_of_pvar pvar t).terms
let consts_of_pvar pvar t = (hspace_of_pvar pvar t).consts
let qdeps_of pvar t = (hspace_of_pvar pvar t).qdeps

let quals_map_of t =
  Hashtbl.Poly.map t.hspaces ~f:(fun h -> h.quals)
  |> Hashtbl.to_alist
  |> List.map ~f:(fun (v, q) -> (Ident.tvar_to_pvar v, q))
  |> Hashtbl.Poly.of_alist_exn

let terms_map_of t =
  Hashtbl.Poly.map t.hspaces ~f:(fun h -> h.terms)
  |> Hashtbl.to_alist
  |> List.map ~f:(fun (v, q) -> (Ident.tvar_to_pvar v, q))
  |> Hashtbl.Poly.of_alist_exn

(* A GATE THAT MEANS CHECK RATHER THAN PRINT, off unless the environment asks.
   The two switches this tree already has -- a config's [verbose] and a
   module-level [print_log] -- both decide whether to *say* something, and there
   was nowhere to put "verify the invariants" short of threading a config into
   modules that have none.  An environment variable is the same shape as the one
   that dumps solver queries. *)
let check_example_sorts = Stdlib.(Sys.getenv_opt "COAR_CHECK_SORTS" <> None)

(* Every example enters here, which is the property that makes this the place to
   check them.  Nothing in the term representation prevents an ill-sorted one --
   a variable carries whatever sort it was built with, a substitution is keyed by
   name and does not compare sorts, an equation does not either -- so a term that
   puts a list where a list's element belongs is an ordinary value until a solver
   sees it, and the run then ends in a sort mismatch on a constructor
   application, raised by the conversion far from the producer.

   Instrumenting the sites that *build* examples is the obvious move and it
   failed: four of them reported clean while the crash reproduced, because the
   producer was a fifth.  The call stack printed here named it on the first run
   that crashed.  Switching this on costs a traversal of every example, which is
   why it is off, and an instrumented run takes a different trajectory from a
   silent one -- so use it to find a producer, never to decide whether a repair
   made a file answer. *)
(* HOW OFTEN THE LOOP IS HANDED AN EXAMPLE IT ALREADY HOLDS, off unless the
   environment asks ([COAR_COUNT_EXAMPLES]).  A counterexample is a model of a
   violated clause, and nothing obliges two rounds' models to differ: on one
   array input a run produced 801 counterexamples of which 9 were distinct and
   767 were the same one -- the problem's own base fact, which every candidate
   ought to satisfy trivially and a candidate true at the sampled instances
   still violated at one more.  That ratio is the observable a learning-theory
   reading of the loop predicts from (the teaching dimension bounds the
   *distinct* count, so the gap is the oracle repeating itself), and it was
   obtained by counting printed trace lines by hand.  This counts it in the
   program: per round, the examples received so far, how many are distinct, and
   the multiplicity of the most repeated one, printed on stderr so that a run
   killed at its budget still leaves the last line.

   The key is the example's printed form.  An [ExClause.t] holds [Set.Poly]
   values whose comparator is a closure, so polymorphic equality on it raises
   and a hash of it sees the tree shape rather than the elements; two examples
   printing alike are the same example up to that printer, which is also the
   identification the hand count used.  Guarded and parametric examples keep
   their guard in the print, so two instances of one region under different
   guards count as two, which is the conservative direction here -- the figure
   can only understate the repetition. *)
let count_example_multiplicity =
  Stdlib.(Sys.getenv_opt "COAR_COUNT_EXAMPLES" <> None)

let example_multiplicity : (string, int) Hashtbl.t = Hashtbl.Poly.create ()
let example_total = ref 0

let count_examples examples =
  Set.iter examples ~f:(fun (ex, _) ->
      incr example_total;
      Hashtbl.Poly.update example_multiplicity (ExClause.str_of ex)
        ~f:(function None -> 1 | Some n -> n + 1));
  let distinct = Hashtbl.length example_multiplicity in
  let max_mult =
    Hashtbl.fold example_multiplicity ~init:0 ~f:(fun ~key:_ ~data acc ->
        max acc data)
  in
  Stdlib.prerr_endline
  @@ sprintf "[example-multiplicity] received=%d distinct=%d max=%d"
       !example_total distinct max_mult

(* HOW MANY SPELLINGS OF ONE EXAMPLE THE SETS HOLD, off unless the environment
   asks ([COAR_EXDEDUP_COUNT]).  Per call of [add_examples], on stderr:
   [offered] examples handed in, [nonnorm] of them not equal to their
   [ExClause.normalize] form, [distinct_nf] distinct normal forms among the
   offered, [new_stored] examples the sets gained, [twins] of those whose normal
   form the sets now hold under another spelling as well, and over the whole sets
   [stored] examples against [stored_nf] distinct normal forms.  [nonnorm_by]
   buckets the unnormalised offered examples by the rule their derivation record
   names ([none] when the producer recorded none).  The index is kept here, per
   process, so the figures describe a single-domain run; it normalises every
   stored example once, which costs time and may draw fresh names, so an
   instrumented run is not a measurement of anything but these counts. *)
let exdedup_count = Stdlib.(Sys.getenv_opt "COAR_EXDEDUP_COUNT" <> None)
let exdedup_nf : (ExClause.t, ExClause.t) Hashtbl.Poly.t =
  Hashtbl.Poly.create ()

let count_spellings t examples =
  let before = ClauseGraph.examples_of t.examples in
  fun () ->
    let nf_of ex =
      match Hashtbl.find exdedup_nf ex with
      | Some nf -> nf
      | None ->
          let nf = ExClause.normalize ex in
          Hashtbl.set exdedup_nf ~key:ex ~data:nf;
          nf
    in
    let offered = Set.length examples in
    let by_rule = Hashtbl.Poly.create () in
    let nonnorm = ref 0 in
    let offered_nf =
      Set.Poly.map examples ~f:(fun (ex, _) ->
          let ex = ExClause.canon ex in
          let nf = nf_of ex in
          if Stdlib.compare ex nf <> 0 then (
            incr nonnorm;
            let rule =
              match ClauseGraph.derivation_of t.examples ex with
              | Some d -> d.ClauseGraph.rule
              | None -> "none"
            in
            Hashtbl.Poly.update by_rule rule ~f:(function
              | None -> 1
              | Some n -> n + 1));
          nf)
    in
    let after = ClauseGraph.examples_of t.examples in
    let fresh = Set.diff after before in
    let twins = ref 0 in
    let held = Hashtbl.Poly.create () in
    Set.iter after ~f:(fun e ->
        Hashtbl.Poly.update held (nf_of e) ~f:(function
          | None -> [ e ]
          | Some l -> e :: l));
    Set.iter fresh ~f:(fun ex ->
        let nf = nf_of ex in
        let others =
          List.filter (Hashtbl.Poly.find_exn held nf) ~f:(fun e ->
              Stdlib.compare e ex <> 0)
        in
        if not (List.is_empty others) then (
          incr twins;
          if Stdlib.(Sys.getenv_opt "COAR_EXDEDUP_COUNT" = Some "2") then
            Stdlib.prerr_endline
            @@ sprintf "[exdedup-twin] %s\n  normal form %s\n  others %s"
                 (ExClause.str_of ex) (ExClause.str_of nf)
                 (String.concat ~sep:" | " @@ List.map others ~f:ExClause.str_of)));
    let stored_nf =
      Set.length @@ Set.Poly.map after ~f:nf_of
    in
    Stdlib.prerr_endline
    @@ sprintf
         "[exdedup-count] offered=%d nonnorm=%d distinct_nf=%d new_stored=%d \
          twins=%d stored=%d stored_nf=%d nonnorm_by=%s"
         offered !nonnorm (Set.length offered_nf) (Set.length fresh) !twins
         (Set.length after) stored_nf
         (String.concat ~sep:","
         @@ List.map ~f:(fun (r, n) -> sprintf "%s:%d" r n)
         @@ List.sort ~compare:Stdlib.compare
         @@ Hashtbl.to_alist by_rule)

let add_examples t examples =
  let report =
    if exdedup_count then Some (count_spellings t examples) else None
  in
  if check_example_sorts then
    Set.iter examples ~f:(fun (ex, _) ->
        List.iter
          (Set.to_list ex.ExClause.positive @ Set.to_list ex.ExClause.negative)
          ~f:(fun atm ->
            let _, cond, phi = ExAtom.to_old_formula_and_cond atm in
            match
              match ill_sorted_cons_in_formula cond with
              | Some m -> Some m
              | None -> ill_sorted_cons_in_formula phi
            with
            | None -> ()
            | Some m ->
                print_endline
                @@ sprintf "[ill-sorted example] %s\n%s" m
                @@ Stdlib.Printexc.raw_backtrace_to_string
                @@ Stdlib.Printexc.get_callstack 24));
  if count_example_multiplicity then count_examples examples;
  Set.iter examples ~f:(fun (ex, srcs) ->
      ClauseGraph.add_ex_from t.examples ex srcs);
  Option.iter report ~f:(fun f -> f ())

let set_examples examples t = { t with examples }
let set_pos_neg_und_examples examples t = { t with examples }
let set_hspace pvar hspace t = Hashtbl.Poly.set t.hspaces ~key:pvar ~data:hspace
let set_truth_table truth_table t = { t with truth_table }

let update_truth_table ~print ~id t =
  Hashtbl.Poly.iteri t.hspaces ~f:(fun ~key:(Ident.Tvar name) ~data ->
      TruthTable.update_map_with_qualifiers ~print ~id t.truth_table t.fenv
        data.qdeps ((*ToDo*) Ident.Pvar name) (data.params, data.quals));
  TruthTable.update_map_with_examples ~print ~id t.truth_table t.fenv t.hspaces
  @@ examples_of t

let set_labelings labelings t = { t with labelings }

let set_label ~print ~id t label labeling atom =
  match ExAtom.pvar_of atom with
  | None -> labeling
  | Some pvar -> (
      let ai =
        TruthTable.index_of_atom ~print ~id
          (TruthTable.get_table t.truth_table pvar)
          t.fenv (qdeps_of pvar t) atom
      in
      match Map.Poly.find labeling pvar with
      | None ->
          Map.Poly.add_exn labeling ~key:pvar
            ~data:(Map.Poly.singleton ai label)
      | Some l ->
          Map.Poly.set labeling ~key:pvar
            ~data:(Map.Poly.set l ~key:ai ~data:label))

let map ~f vs =
  let examples', labelings' =
    f ~examples:(examples_of vs) ~labelings:vs.labelings
  in
  set_labelings labelings' @@ set_examples examples' vs

let set_fenv fenv t = { t with fenv }
let update_uenv_by_model model t = UTermEnv.update_by_model t.uenv model
let lower_bound_of t = Hashtbl.Poly.find t.lower_bounds
let upper_bound_of t = Hashtbl.Poly.find t.upper_bounds

let add_learned_clause id t (uni_senv, ps, ns, phi) =
  match
    Hash_set.find t.learned_clauses ~f:(fun (_, ps1, ns1, _) ->
        Set.equal ps ps1 && Set.equal ns ns1)
  with
  | Some (uni_senv1, ps1, ns1, phi1) ->
      let uni_senv' = Map.force_merge uni_senv uni_senv1 in
      let phi' =
        Logic.ExtTerm.and_of [ phi1; phi ]
        |> Logic.ExtTerm.to_old_fml Map.Poly.empty uni_senv'
        |> Evaluator.simplify
        |> Z3Smt.Z3interface.z3_simplify ~id (LogicOld.get_fenv ())
        |> Logic.ExtTerm.of_old_formula
      in
      Hash_set.remove t.learned_clauses (uni_senv1, ps1, ns1, phi1);
      Hash_set.add t.learned_clauses (uni_senv', ps1, ns1, phi')
  | None -> Hash_set.Poly.add t.learned_clauses (uni_senv, ps, ns, phi)

let add_learned_clauses id t = Set.iter ~f:(add_learned_clause id t)

let add_lower_bound t (key, term) =
  Hashtbl.Poly.update t.lower_bounds key ~f:(function
    | None -> term
    | Some old_term ->
        let params =
          List.mapi ~f:(fun i (_, s) -> (Ident.Tvar (sprintf "x%d" (i + 1)), s))
          @@ fst @@ Logic.ExtTerm.let_lam term
        in
        let args = List.map params ~f:(fst >> Logic.ExtTerm.mk_var) in
        Logic.ExtTerm.mk_lambda params
        @@ Logic.ExtTerm.or_of
             [
               Logic.ExtTerm.beta_reduction (Logic.Term.mk_apps term args);
               Logic.ExtTerm.beta_reduction (Logic.Term.mk_apps old_term args);
             ])

let add_upper_bound t (key, term) =
  Hashtbl.Poly.update t.upper_bounds key ~f:(function
    | None -> term
    | Some old_term ->
        let params =
          List.mapi ~f:(fun i (_, s) -> (Ident.Tvar (sprintf "x%d" (i + 1)), s))
          @@ fst @@ Logic.ExtTerm.let_lam term
        in
        let args = List.map params ~f:(fst >> Logic.ExtTerm.mk_var) in
        Logic.ExtTerm.mk_lambda params
        @@ Logic.ExtTerm.and_of
             [
               Logic.ExtTerm.beta_reduction (Logic.Term.mk_apps term args);
               Logic.ExtTerm.beta_reduction (Logic.Term.mk_apps old_term args);
             ])

let add_bound_as_learned_clause ~print id pfwcsp vs pvar
    (arity, (param_senv, term)) upper =
  print
  @@ lazy
       (sprintf "*** a new %s bound of [%s]"
          (if upper then "upper" else "lower")
       @@ Ident.name_of_tvar pvar);
  match Map.Poly.find (PCSP.Problem.senv_of pfwcsp) pvar with
  | None -> ()
  | Some _ ->
      let args_log, sargs =
        Map.Poly.find_exn (PCSP.Problem.args_record_of pfwcsp)
        @@ Ident.tvar_to_pvar pvar
      in
      let params, uni_senv, term =
        let pred_params =
          List.mapi sargs ~f:(fun i s ->
              (Ident.Tvar (sprintf "x%d" (i + 1)), s))
        in
        let term =
          Logic.ExtTerm.beta_reduction
            (Logic.Term.mk_apps term
            @@ List.map ~f:(fst >> Logic.ExtTerm.mk_var)
            @@ List.drop pred_params (List.length pred_params - arity))
        in
        let aux_params =
          List.filter_mapi pred_params ~f:(fun i (v, s) ->
              if args_log.(i) then None else Some (v, Ident.mk_fresh_tvar (), s))
        in
        let pred_params =
          List.filteri pred_params ~f:(fun i _ -> args_log.(i))
        in
        let uni_senv =
          Map.force_merge param_senv @@ Map.Poly.of_alist_exn @@ pred_params
          @ List.map aux_params ~f:(fun (_, v2, s) -> (v2, s))
        in
        let sub =
          Map.Poly.of_alist_exn
          @@ List.map aux_params ~f:(fun (v1, v2, _) ->
              (v1, Logic.ExtTerm.mk_var v2))
        in
        (pred_params, uni_senv, Logic.ExtTerm.subst sub term)
      in
      let papp =
        Logic.ExtTerm.(mk_var_app pvar @@ List.map params ~f:(fst >> mk_var))
      in
      if upper then (
        print
        @@ lazy
             (sprintf "added a new learned clause: %s(%s) => %s"
                (Ident.name_of_tvar pvar)
                (String.concat_map_list ~sep:"," params
                   ~f:(fst >> Ident.name_of_tvar))
                (Logic.ExtTerm.str_of_formula
                   (PCSP.Problem.senv_of pfwcsp)
                   uni_senv term));
        add_upper_bound vs (pvar, term);
        Hash_set.add vs.assumed_clauses
          (uni_senv, Set.Poly.empty, Set.Poly.singleton papp, term);
        add_learned_clause id vs
          (uni_senv, Set.Poly.empty, Set.Poly.singleton papp, term))
      else (
        print
        @@ lazy
             (sprintf "added a new learned clause: %s => %s(%s)"
                (Logic.ExtTerm.str_of_formula
                   (PCSP.Problem.senv_of pfwcsp)
                   uni_senv term)
                (Ident.name_of_tvar pvar)
                (String.concat_map_list ~sep:"," params
                   ~f:(fst >> Ident.name_of_tvar)));
        add_lower_bound vs (pvar, term);
        Hash_set.add vs.assumed_clauses
          ( uni_senv,
            Set.Poly.singleton papp,
            Set.Poly.empty,
            Logic.BoolTerm.neg_of term );
        add_learned_clause id vs
          ( uni_senv,
            Set.Poly.singleton papp,
            Set.Poly.empty,
            Logic.BoolTerm.neg_of term ))

let str_of_hspace name (hspace : HypSpace.hspace) =
  sprintf
    "\n\
     ===== [%s](%s) =====\n\n\
     *** depth: %d\n\
     *** qualifiers (%d):\n\
     %s\n\
     *** param_qdeps (%d):\n\
     %s\n\
     *** terms (%d):\n\
     %s\n\
     *** consts (%d):\n\
     %s"
    name
    (str_of_sort_env_list Term.str_of_sort hspace.params)
    hspace.depth (Set.length hspace.quals)
    (String.concat_map_set ~sep:"\n" hspace.quals ~f:Formula.str_of)
    (Map.Poly.length hspace.qdeps)
    (String.concat_map_list ~sep:"\n" ~f:(snd >> QualDep.str_of)
    @@ Map.Poly.to_alist hspace.qdeps)
    (Set.length hspace.terms)
    (String.concat_map_set ~sep:"\n" hspace.terms ~f:Term.str_of)
    (Set.length hspace.consts)
    (String.concat_map_set ~sep:"\n" hspace.consts ~f:Term.str_of)

let str_of_examples (decided_pos, decided_neg, undecided) =
  "********* given example instances *********\n"
  ^ (sprintf "*** decided positive (%d): [\n" @@ Set.length decided_pos)
  ^ ExClauseSet.str_of decided_pos
  ^ (sprintf "]\n*** decided negative (%d): [\n" @@ Set.length decided_neg)
  ^ ExClauseSet.str_of decided_neg
  ^ (sprintf "]\n*** undecided (%d): [\n" @@ Set.length undecided)
  ^ ExClauseSet.str_of undecided
  ^ "]\n"

let str_of_number_of_examples (decided_pos, decided_neg, undecided) =
  sprintf "#decided_positive: %d, #decided_negative: %d, #undecided: %d"
    (Set.length decided_pos) (Set.length decided_neg) (Set.length undecided)

let str_of_learned_clauses exi_senv learned_clauses =
  "********* learned clauses *********\n"
  ^ (String.concat_map_list ~sep:"\n" ~f:(Clause.str_of exi_senv)
    @@ Hash_set.to_list learned_clauses)
  ^ "\n***********************************"

type ex = {
  positive : string list;
  negative : string list;
  undecided : string list;
}
[@@deriving to_yojson]

let to_yojson (decided_pos, decided_neg, undecided) =
  ex_to_yojson
    {
      positive = List.map ~f:ExClause.str_of @@ Set.to_list decided_pos;
      negative = List.map ~f:ExClause.str_of @@ Set.to_list decided_neg;
      undecided = List.map ~f:ExClause.str_of @@ Set.to_list undecided;
    }

(** BMI learning for CEGIS *)

let vec_of_exatom ?(enc_bool_to_float = 100.0) ?(ignore_bool_args = false) map a
    =
  match (ExAtom.pvar_of a, ExAtom.sorts_of a, ExAtom.args_of a) with
  | Some pvar, Some sorts, Some args ->
      ( List.mapi ~f:(fun i x -> (i, x))
        @@ List.filter_map ~f:Fn.id
        @@ List.map2_exn args sorts ~f:(fun t s ->
            match (s, Term.value_of t) with
            | T_bool.SBool, Value.Bool v ->
                if ignore_bool_args then None
                else if v then Some enc_bool_to_float
                else Some (-.enc_bool_to_float)
            | T_int.SInt, Value.Int v -> Some (Z.to_float v)
            | T_real.SReal, Value.Real v -> Some (Q.to_float v)
            | T_bv.SBV _, Value.BV (_, v) -> Some (Z.to_float v) (*ToDo*)
            | _ -> assert false),
        Hashtbl.find_exn map @@ Ident.name_of_pvar pvar )
  | _ -> assert false

let bag_of_exclause ?(enc_bool_to_float = 100.0) ?(ignore_bool_args = false) map
    (cl, weight) =
  ( List.map cl ~f:(fun (a, pol) ->
        (vec_of_exatom ~enc_bool_to_float ~ignore_bool_args map a, pol)),
    weight )

let add_vec vec1 vec2 = List.map2_exn vec1 vec2 ~f:Float.add
let sub_vec vec1 vec2 = List.map2_exn vec1 vec2 ~f:Float.sub
let div_vec vec sc = List.map vec ~f:(fun v -> v /. sc)

let average_of_vecs vecs =
  div_vec
    (List.fold ~init:(List.hd_exn vecs) (List.tl_exn vecs) ~f:add_vec)
    (float_of_int @@ List.length vecs)

let euclid_dist_sq vec1 vec2 =
  List.sum_float @@ List.map (sub_vec vec1 vec2) ~f:Float.square

let variance_of_vecs (pred_num, vecs) =
  let avg = average_of_vecs vecs in
  (pred_num, List.average_float @@ List.map vecs ~f:(euclid_dist_sq avg))

let variances_of_bags bags (* ToDo: fix *) =
  List.map ~f:variance_of_vecs
  @@ List.map ~f:(fun a ->
      ( snd @@ List.hd_exn a,
        List.map a ~f:(fun (vecs, _) -> List.map ~f:snd vecs) ))
  @@ List.classify (fun (_, pred_num1) (_, pred_num2) -> pred_num1 = pred_num2)
  @@ List.map ~f:fst
  @@ List.concat_map ~f:fst bags

(** assume that all predicate variable has at least one numeric argument *)
let update_heat_map ?((*~print*) enc_bool_to_float = 100.0)
    ?(ignore_bool_args_variance = false) senv wexs t : unit =
  ignore (enc_bool_to_float, ignore_bool_args_variance, senv, wexs, t);
  assert false
(*
  let map (* pvar name to index *) =
    let cnt = ref 0 in
    Map.Poly.fold senv ~init:(Hashtbl.Poly.create ()) ~f:(fun ~key ~data:_ map ->
        cnt := !cnt + 1;
        Hashtbl.Poly.add_exn map ~key:(Ident.name_of_tvar key) ~data:!cnt;
        map) in
  let ex =
    wexs
    |> List.map ~f:(fun (cl, weight) -> ExClause.instantiate cl, weight)
    |> List.map ~f:(fun (cl, weight) ->
        (cl.ExClause.positive |> Set.to_list |> List.map ~f:(fun a -> a, true)) @
        (cl.ExClause.negative |> Set.to_list |> List.map ~f:(fun a -> a, false)),
        weight)
  in
  let bags = List.map ex ~f:(bag_of_exclause ~enc_bool_to_float map) in
  let variances =
    if ignore_bool_args_variance then
      variances_of_bags (List.map ex ~f:(bag_of_exclause ~enc_bool_to_float ~ignore_bool_args:ignore_bool_args_variance map))
    else
      variances_of_bags bags
  in
  let model = BMIsvm.train ~c:20. ~gamma:(List.map variances ~f:(fun (pred_num, var) -> pred_num, 1.0 /. var)) bags in
  let indices = BMIsvm.Model.get_support_vector_indices model in
  let selectors = BMIsvm.Model.get_sel model in
  let svs_pos, svs_neg =
    List.partition_map ~f:(fun (sv, pol) -> if pol then First sv else Second sv) @@
    List.map indices ~f:(fun bag_index ->
        List.nth_exn (List.nth_exn ex bag_index) (List.nth_exn selectors bag_index)) in
  print ~id @@ lazy (sprintf "positive support vectors (%d): %s" (List.length svs_pos) (String.concat_map_list ~sep:"," ~f:ExAtom.str_of svs_pos));
  print ~id @@ lazy (sprintf "negative support vectors (%d): %s" (List.length svs_neg) (String.concat_map_list ~sep:"," ~f:ExAtom.str_of svs_neg));
  t.heat_map := Some (model, map)*)

let get_heat ?(enc_bool_to_float = 100.0) t atom =
  ignore (enc_bool_to_float, t, atom);
  assert false
(*
  match !(t.heat_map) with
  | None -> assert false
  | Some (model, map) ->
    let args, pvar_idx = vec_of_exatom ~enc_bool_to_float map atom in
    try Bmilearner.BMIsvm.decision_value_one_sparse model pvar_idx args with _ -> -100.*)
