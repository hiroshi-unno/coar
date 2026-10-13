open Core
open Graph
open Common.Ext
open Common.Combinator
open Logic

type vertex = Example of ExClause.t | Clause of Clause.t | Dummy
(* | Constr of Logic.sort_env_map * Logic.term *)

module V = struct
  type t = vertex

  let compare v1 v2 =
    match (v1, v2) with
    | Dummy, Dummy -> 0
    | Clause c1, Clause c2 -> Stdlib.compare c1 c2
    | Example e1, Example e2 -> Stdlib.compare e1 e2
    | Dummy, _ -> 1
    | _, Dummy -> -1
    | Clause _, _ -> -1
    | _, Clause _ -> 1

  let equal v1 v2 =
    match (v1, v2) with
    | Clause c1, Clause c2 -> Clause.equal c1 c2
    | Example e1, Example e2 -> ExClause.equal e1 e2
    | Dummy, Dummy -> true
    | _, _ -> false

  (* [Hashtbl.hash] stops after ten meaningful nodes, and on a clause or an
     example clause those ten are the set and map headers every vertex shares,
     so a solve's several hundred vertices fell into about a dozen buckets and
     every graph operation compared a bucket of forty vertices structurally.
     The hash below sees the whole vertex, and it is consistent with [equal],
     which compares the sets and the map extensionally: each collection is
     folded into a sum of its elements' hashes -- commutative, so the tree
     shape the collection happens to have does not enter -- and an element is
     hashed with a budget large enough to reach its leaves.  The maps and sorts
     that [equal] ignores in an example atom are left out too, so a coarser
     but never finer partition than equality. *)
  let hash_elem x = Hashtbl.hash_param 50 200 x
  let hash_terms ts = Set.fold ts ~init:0 ~f:(fun acc t -> acc + hash_elem t)

  let hash_atom = function
    | ExAtom.FCon (_, phi) -> hash_elem phi
    | PApp ((pvar, _), ts) -> hash_elem (pvar, ts)
    | PPApp ((_, phi), ((pvar, _), ts)) -> hash_elem (phi, pvar, ts)

  let hash_atoms atms =
    Set.fold atms ~init:0 ~f:(fun acc atm -> acc + hash_atom atm)

  let hash = function
    | Dummy -> 0
    | Clause (senv, ps, ns, phi) ->
        Hashtbl.hash
          ( Map.Poly.fold senv ~init:0 ~f:(fun ~key ~data acc ->
                acc + hash_elem (key, data)),
            hash_terms ps,
            hash_terms ns,
            hash_elem phi )
    | Example ex ->
        Hashtbl.hash
          (hash_atoms ex.ExClause.positive, hash_atoms ex.ExClause.negative)
end

let vstr_of_vertex senv _hide_vertexs v =
  String.concat ~sep:"\\\\" @@ String.split ~on:'\\' @@ "\""
  ^
  (* begin
     if Hash_set.mem hide_vertexs v then "(x)" else "(o)"
     end ^ *)
  match v with
  | Dummy -> "Dummy\""
  | Example ex -> sprintf "%s\"" (ExClause.str_of ex)
  | Clause cl -> sprintf "%s\"" (Clause.str_of senv cl)

module E = struct
  type lable = Hide | Normal
  type t = lable

  let default = Normal

  let compare e1 e2 =
    match (e1, e2) with Hide, Normal -> 1 | Normal, Hide -> -1 | _ -> 0
end

module G = Imperative.Digraph.ConcreteBidirectionalLabeled (V) (E)

module W = struct
  type t = int
  type edge = vertex * E.lable * vertex (* This is G.edge *)

  let zero = 0
  let add = ( + )
  let compare = Int.compare
  let weight _ = 1
end

module Dijkstra = Path.Dijkstra (G) (W)

let black = 0x000000
and white = 0xFFFFFF
and red = 0xFF0000
and green = 0x00FF00
and blue = 0x0000FF
and yellow = 0xFFFF00
and cyan = 0x00FFFF
and magenta = 0xFF00FF

module type EnvType = sig
  val senv : Logic.sort_env_map
  val hide_vertexs : vertex Hash_set.Poly.t
end

module Dot (Env : EnvType) = Graph.Graphviz.Dot (struct
  include G (* use the graph module from above *)

  let graph_attributes _ = [ `Rankdir `LeftToRight ]
  let default_vertex_attributes _ = []
  let vertex_name v = vstr_of_vertex Env.senv Env.hide_vertexs v

  let vertex_attributes v =
    (if Hash_set.mem Env.hide_vertexs v then [ `Color red ] else [])
    @
    match v with
    | Example _ -> [ `Shape `Box ]
    | _ -> [ `Shape `Oval; `Penwidth 3.0; `Style `Bold ]

  let get_subgraph _ = None
  let default_edge_attributes _ = []
  let edge_attributes _ = [ `Color 4711 ]
end)

(* how an example was obtained: the rule and, when known, the substitution
   applied to its source clause (validator: the countermodel; resolver: the
   unifier).  Kept beside the graph, keyed by the example, so that the edge
   structure is untouched. *)
type derivation = {
  rule : string;
  subst : LogicOld.TermSubst.t option;
  premises : ExClause.t list;
      (* the decided examples the deriving component used, when it names
         them (the graph's edges cite transitive sources) *)
  via : Clause.t option;
      (* the problem clause whose instance (under [subst]) the example was
         derived from, when the deriving component knows it *)
}

type t = {
  graph : G.t;
  hide_vertexs : vertex Hash_set.Poly.t;
  mutable pos : ExClauseSet.t;
  mutable neg : ExClauseSet.t;
  mutable und : ExClauseSet.t;
  derivations : (ExClause.t, derivation) Hashtbl.Poly.t;
  mutable dedup_normalized : bool;
      (* when set, [add_ex_from] stores at most one spelling of an example
         per [ExClause.normalize] form; see [spelling_of] *)
  mutable norm_index : (ExClause.t, ExClause.t) Map.Poly.t;
      (* maintained only while [dedup_normalized] is set: an example's
         normal form, and each spelling that arrived, mapped to the first
         spelling stored *)
}

let is_example = function Example _ -> true | _ -> false
let is_clause = function Clause _ -> true | _ -> false
let mk_example ex = Example ex
let mk_clause c = Clause c
let mk_dummy () = Dummy

let str_of_vertex senv = function
  | Dummy -> "V_Dummy"
  | Example ex -> sprintf "V_Ex(%s)" (ExClause.str_of ex)
  | Clause c -> sprintf "V_Cl(%s)" (Clause.str_of senv c)

let create () =
  {
    graph = G.create ();
    hide_vertexs = Hash_set.Poly.create ();
    pos = Set.Poly.empty;
    neg = Set.Poly.empty;
    und = Set.Poly.empty;
    derivations = Hashtbl.Poly.create ();
    dedup_normalized = false;
    norm_index = Map.Poly.empty;
  }

let examples_of_graph t =
  G.fold_vertex
    (fun v acc ->
      match v with
      | Example ex when not @@ Hash_set.Poly.mem t.hide_vertexs v ->
          if G.out_degree t.graph v = 0 || ExClause.is_unit ex then
            Set.add acc ex
          else acc
      | _ -> acc)
    t.graph Set.Poly.empty

let pos_neg_und_examples_of_graph t =
  G.fold_vertex
    (fun v (pos, neg, und) ->
      match v with
      | Example ex when not @@ Hash_set.Poly.mem t.hide_vertexs v ->
          if ExClause.is_unit_positive ex then (Set.add pos ex, neg, und)
          else if ExClause.is_unit_negative ex then (pos, Set.add neg ex, und)
          else (pos, neg, Set.add und ex)
      | _ -> (pos, neg, und))
    t.graph
    (Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)

let clone t =
  let pos, neg, und = pos_neg_und_examples_of_graph t in
  {
    graph = G.copy t.graph;
    hide_vertexs = Hash_set.copy t.hide_vertexs;
    pos;
    neg;
    und;
    derivations = Hashtbl.copy t.derivations;
    dedup_normalized = t.dedup_normalized;
    norm_index = t.norm_index;
  }

(* the first derivation recorded for an example is kept: one suffices for a
   certificate, and later ones would only differ in the route *)
let record_derivation ?(via = None) ?(premises = []) t ex ~rule ~subst =
  ignore
    (Hashtbl.add t.derivations ~key:ex ~data:{ rule; subst; premises; via })

let derivation_of t ex = Hashtbl.find t.derivations ex

(* the ancestor walks carry a visited set: since examples cite the examples
   they were derived from, two parametric variants of one example derived in
   different runs can cite each other, and the walk must not loop *)
let pred_clause_vertexs_of g v0 =
  let visited = Hash_set.Poly.create () in
  let rec go = function
    | (Dummy | Clause _) as v -> Set.Poly.singleton v
    | v ->
        if Hash_set.mem visited v then Set.Poly.empty
        else (
          Hash_set.add visited v;
          Set.Poly.union_list @@ List.map (G.pred g v) ~f:go)
  in
  go v0

let pred_clause_und_vertexs_of g v0 =
  let visited = Hash_set.Poly.create () in
  let rec go = function
    | (Dummy | Clause _) as v -> Set.Poly.singleton v
    | Example e as v when Fn.non ExClause.is_unit e -> Set.Poly.singleton v
    | v ->
        if Hash_set.mem visited v then Set.Poly.empty
        else (
          Hash_set.add visited v;
          Set.Poly.union_list @@ List.map (G.pred g v) ~f:go)
  in
  go v0

(* The example sets and the graph's vertex table are keyed on the clause or
   example clause itself, so a value that arrives in a non-canonical shape (see
   [Common.Ext.Set.canon]) would be a second member for one that is already
   present.  Every producer canonicalises; the three entry points below do it
   once more so that a value built by hand elsewhere cannot break the sets. *)
let add_example (t : t) = function
  | Example ex ->
      let ex = ExClause.canon ex in
      if ExClause.is_unit_positive ex then t.pos <- Set.add t.pos ex
      else if ExClause.is_unit_negative ex then t.neg <- Set.add t.neg ex
      else t.und <- Set.add t.und ex
  | _ -> ()

let remove_example_in_exset (t : t) = function
  | Example ex ->
      let ex = ExClause.canon ex in
      if ExClause.is_unit_positive ex then t.pos <- Set.remove t.pos ex
      else if ExClause.is_unit_negative ex then t.neg <- Set.remove t.neg ex
      else t.und <- Set.remove t.und ex
  | _ -> ()

let remove_vertex t v =
  remove_example_in_exset t v;
  Hash_set.remove t.hide_vertexs v;
  let preds = G.pred_e t.graph v in
  G.remove_vertex t.graph v;
  List.iter preds ~f:(fun (src, lable, _) ->
      match lable with
      | E.Hide when Hash_set.mem t.hide_vertexs src ->
          let succs = G.succ_e t.graph src in
          if
            List.for_all succs ~f:(function _, E.Hide, _ -> false | _ -> true)
          then (
            Hash_set.remove t.hide_vertexs src;
            add_example t src)
      | _ -> ())

let hide_vertex t v =
  remove_example_in_exset t v;
  Hash_set.add t.hide_vertexs v

let hide_und_example (t : t) = function
  | Example ex as v -> if Fn.non ExClause.is_unit ex then hide_vertex t v
  | _ -> ()

(* ONE SPELLING PER EXAMPLE.  [ExClause.normalize] simplifies and normalises
   every guard and argument, which preserves meaning exactly, and the labeler's
   unit propagation hands back every example it was given in that normal form.
   An example whose producer left it unnormalised -- a resolvent guarded by
   [0 = 0], an argument [-5 + x] that normalises to [x - 5] -- then came back as
   a different value, and the example sets, keyed on the value, kept both: the
   same fact twice, as two rows of the truth table and two propositional
   variables of the labeling that nothing ties together.  With
   [dedup_normalized] set, an arriving example is replaced by the spelling
   already stored for its normal form, if any, so the sets never hold two
   spellings of one example; the first spelling stored is kept, because the
   derivation record and the graph's edges are keyed on it.
   Lookup is by the arriving value itself and then by its normal form, so a
   twin that *is* the normal form is recognised even where [normalize] is not
   idempotent.  Nothing is indexed and nothing is normalised while the switch
   is off. *)
let spelling_of t ex =
  if not t.dedup_normalized then ex
  else
    match Map.Poly.find t.norm_index ex with
    | Some s -> s
    | None -> (
        let nf = ExClause.normalize ex in
        match Map.Poly.find t.norm_index nf with
        | Some s ->
            t.norm_index <- Map.Poly.set t.norm_index ~key:ex ~data:s;
            s
        | None ->
            t.norm_index <-
              Map.Poly.set
                (Map.Poly.set t.norm_index ~key:nf ~data:ex)
                ~key:ex ~data:ex;
            ex)

let set_dedup_normalized t b =
  if b && not t.dedup_normalized then (
    t.dedup_normalized <- true;
    Set.iter
      (Set.Poly.union_list [ t.pos; t.neg; t.und ])
      ~f:(fun ex -> ignore (spelling_of t ex)))
  else if not b then (
    t.dedup_normalized <- false;
    t.norm_index <- Map.Poly.empty)

let add_ex_from t ex srcs =
  let ex = spelling_of t @@ ExClause.canon ex in
  let v_ex = Example ex in
  (* "new" means absent from the example sets, not from the graph: an edge
     added earlier towards this example (a derived example citing it as a
     premise) creates its vertex implicitly, and testing the vertex
     would then skip the example and lose it for the solver *)
  let present = Set.mem t.pos ex || Set.mem t.neg ex || Set.mem t.und ex in
  if (not present) || Hash_set.Poly.mem t.hide_vertexs v_ex then (
    Hash_set.Poly.remove t.hide_vertexs v_ex;
    G.add_vertex t.graph v_ex;
    add_example t v_ex;
    Set.iter srcs ~f:(fun (src, hide_und) ->
        if not @@ V.equal src v_ex then
          match src with
          | Example ex when hide_und && (not @@ ExClause.is_unit ex) ->
              hide_vertex t src;
              G.add_edge_e t.graph (src, E.Hide, v_ex)
          | _ -> G.add_edge t.graph src v_ex))

let add_clause t clause = G.add_vertex t.graph (Clause (Clause.canon clause))

let add_clause_from t clause srcs =
  let v = Clause (Clause.canon clause) in
  G.add_vertex t.graph v;
  List.iter srcs ~f:(fun src ->
      if not @@ V.equal src v then G.add_edge t.graph src v)

let pos_neg_und_examples_of t = (t.pos, t.neg, t.und)
let examples_of t = Set.Poly.union_list [ t.pos; t.neg; t.und ]

let remove_succ senv t (v : vertex) =
  ignore senv;
  let rec dfs history = function
    | hd :: tl ->
        if Set.mem history hd then dfs history tl
        else
          let history' = Set.add history hd in
          let succs' = G.succ t.graph hd @ tl in
          dfs history' succs'
    | [] -> history
  in
  if G.mem_vertex t.graph v then
    let removed_vertexs = dfs Set.Poly.empty [ v ] in
    (* print_endline @@ sprintf "rm_succs(%s):%d" (str_of_vertex senv v) (Set.length removing_vertexs); *)
    Set.iter removed_vertexs ~f:(remove_vertex t)

let clauses_of t =
  G.fold_vertex
    (fun v acc ->
      match v with
      | Clause c when not @@ Hash_set.Poly.mem t.hide_vertexs v -> Set.add acc c
      | _ -> acc)
    t.graph Set.Poly.empty

let path_to t st ed =
  if G.mem_vertex t.graph st && G.mem_vertex t.graph ed then
    try
      Dijkstra.shortest_path t.graph st ed
      |> fst
      |> List.map ~f:(fun edge -> (G.E.src edge, G.E.dst edge))
    with exn_ when not (Common.Timer.is_async exn_) -> []
  else []

let rec hide_succs t v =
  hide_vertex t v;
  remove_example_in_exset t v;
  List.iter (G.succ t.graph v) ~f:(fun v ->
      remove_example_in_exset t v;
      hide_succs t v)

module Printer (Env : EnvType) =
  Gml.Print
    (G)
    (struct
      let node v =
        [ ("label", Gml.String (vstr_of_vertex Env.senv Env.hide_vertexs v)) ]

      let edge _ = [ ("label", Gml.String "") ]
    end)

let output_graph ?(pre = "") ~id t senv =
  let module Dot = Dot (struct
    let senv = senv
    let hide_vertexs = t.hide_vertexs
  end) in
  let module Printer = Printer (struct
    let senv = senv
    let hide_vertexs = t.hide_vertexs
  end) in
  (* The name carries the process id because the file lives in the current
     directory and is handed to an external [dot]: two solver processes started
     in the same directory used to write, read and delete one file called
     [output_graph_#<domain>_<phase>.dot], so [dot] read a half-written file and
     printed "syntax error in line N" -- which reads like a parse error of the
     user's *input* and is not one.  Reproduced with six concurrent runs of one
     [.hes] file under a verbose config: two of the six reported it. *)
  let file_name =
    let pid = Core_unix.getpid () |> Pid.to_int in
    match id with
    | Some i -> sprintf "output_graph_p%d_#%d_%s.dot" pid i pre
    | None -> sprintf "output_graph_p%d_%s.dot" pid pre
  in
  let file = Out_channel.create ~binary:false file_name in
  Dot.output_graph file t.graph;
  Out_channel.flush file;
  Out_channel.close file;
  (* Dot.output_graph Out_channel.stdout t.graph; *)
  (* Printer.print Format.std_formatter t.graph; Format.print_flush (); *)
  (* the [.dot] source is removed only when [dot] reported success, so a
     failure (graphviz missing, or a graph it rejects) leaves the input behind
     instead of vanishing without a word *)
  if
    0
    = Sys_unix.command
      @@ sprintf "dot -Tsvg %s > %s.svg" (Filename.quote file_name)
           (Filename.quote file_name)
  then Stdlib.Sys.remove file_name

(* [extra] is carried through untouched (the resolver keeps the unifier and
   the origin clause of each resolvent there, for derivation records) *)

(** Porting from Clause/ClauseSet *)
(* Remove from a clause the literals that the decided examples already settle.

    [falsified] and [verified] extend the set membership below to examples that
    settle a literal without being syntactically equal to it. Two parametric
    atoms can be the same atom under a substitution -- most simply a renaming of
    their parameters -- and a set difference sees two elements, so a head the
    examples have already refuted survives and the clause stays undecided for
    the rest of the run. The callers supply the test because deciding it needs a
    solver and this module does not depend on one; they receive the clause's own
    sort environment because converting a literal needs it. The default is the
    set membership alone, so a caller that passes nothing gets exactly the
    previous behaviour.

    What a caller must establish before answering [true] is *not* that the two
    atoms can be made equal: the literal is removed unconditionally, so the
    decided example has to settle it at **every** value of the clause's
    parameters. For a head [p] and a decided negative [n] that is
    [forall (p's parameters). exists (n's parameters). p = n], which a renaming
    satisfies and an overlap does not. Answering [true] for a mere overlap drops
    a literal the examples did not refute, which is a wrong [unsat]. *)
let simplify_with ?(falsified = fun _ _ -> false) ?(verified = fun _ _ -> false)
    pos neg =
  let pos1 = Set.Poly.map ~f:(fst >> snd) pos in
  let neg1 = Set.Poly.map ~f:(fst >> snd) neg in
  Set.Poly.filter_map ~f:(fun (((senv, c_pos, c_neg, c_phi), source), extra) ->
      if Set.are_disjoint c_pos pos1 && Set.are_disjoint c_neg neg1 then
        let source =
          (* the sources of the units that removed a literal (a negative unit
             removes a head, a positive one a body atom); with the condition
             inverted the sources of every *unused* unit would be attached
             instead, so a derived example's graph parents would name
             unrelated units and miss the ones it depends on *)
          let neg' =
            Set.Poly.filter_map neg ~f:(fun ((_, term), src) ->
                if Set.mem c_pos term then Some src else None)
          in
          let pos' =
            Set.Poly.filter_map pos ~f:(fun ((_, term), src) ->
                if Set.mem c_neg term then Some src else None)
          in
          Set.concat @@ Set.add (Set.union neg' pos') source
        in
        Some
          ( ( Clause.canon
                ( senv,
                  Set.filter (Set.diff c_pos neg1) ~f:(fun t ->
                      not (falsified senv t)),
                  Set.filter (Set.diff c_neg pos1) ~f:(fun t ->
                      not (verified senv t)),
                  c_phi ),
              source ),
            extra )
      else None)

let resolve_one_step ~print mode ((param_senv, (papp : term)), source) exi_senv
    (((uni_senv, c_pos, c_neg, c_phi) as cl), source1) =
  print @@ lazy ("input clause: " ^ Clause.str_of exi_senv cl);
  let atm1 =
    LogicOld.Atom.alpha_rename_let
    @@ ExtTerm.to_old_atm exi_senv param_senv papp
  in
  let uni_senv' = Map.force_merge uni_senv param_senv in
  (if Stdlib.(mode = `Forward) then
     let _ = print @@ lazy "forward:" in
     c_neg
   else
     let _ = print @@ lazy "backward:" in
     c_pos)
  |> Set.Poly.filter_map ~f:(fun papp' ->
         let atm2 = ExtTerm.to_old_atm exi_senv uni_senv' papp' in
         print
         @@ lazy
              (LogicOld.Atom.str_of atm2 ^ " |-> " ^ LogicOld.Atom.str_of atm1);
         let open Option.Monad_infix in
         LogicOld.Atom.unify (Map.key_set exi_senv) atm2 atm1
         >>= fun theta (*ToDo*) ->
         let theta = Map.Poly.map ~f:ExtTerm.of_old_term theta in
         let c_pos' =
           (if Stdlib.(mode = `Backward) then Set.remove c_pos papp' else c_pos)
           |> Set.Poly.map
                ~f:
                  (ExtTerm.subst theta
                  >> ExtTerm.to_old_atm exi_senv uni_senv'
                  >> Normalizer.normalize_let_atom >> Normalizer.normalize
                  >> ExtTerm.of_old_formula)
         in
         let c_neg' =
           (if Stdlib.(mode = `Forward) then Set.remove c_neg papp' else c_neg)
           |> Set.Poly.map
                ~f:
                  (ExtTerm.subst theta
                  >> ExtTerm.to_old_atm exi_senv uni_senv'
                  >> Normalizer.normalize_let_atom >> Normalizer.normalize
                  >> ExtTerm.of_old_formula)
         in
         let c_phi' =
           ExtTerm.(simplify_formula exi_senv uni_senv' @@ subst theta c_phi)
         in
         let cl' = Clause.canon (uni_senv', c_pos', c_neg', c_phi') in
         print @@ lazy ("substituted clause: " ^ Clause.str_of exi_senv cl');
         Some
           ( (cl', Set.union source source1),
             Map.Poly.map theta ~f:(ExtTerm.to_old_trm exi_senv uni_senv'),
             cl (* the clause resolved, for derivation records *) ))

(* val resolve: Atom.t Set.Poly.t -> Atom.t Set.Poly.t -> t -> t Set.Poly.t *)
let resolve_one_step_all ~print positive negative exi_senv =
  let resolve_one_step_all ~print positive negative exi_senv c =
    let cs_b =
      Set.fold negative ~init:Set.Poly.empty ~f:(fun acc neg ->
          Set.union (resolve_one_step ~print `Backward neg exi_senv c) acc)
    in
    let cs_f =
      Set.fold positive ~init:Set.Poly.empty ~f:(fun acc pos ->
          Set.union (resolve_one_step ~print `Forward pos exi_senv c) acc)
    in
    Set.filter (Set.union cs_b cs_f)
      ~f:
        ((fun (x, _, _) -> x) >> fst >> Quadruple.fth >> BoolTerm.is_true >> not)
  in
  Set.concat_map ~f:(resolve_one_step_all ~print positive negative exi_senv)

let to_clause_set_with_src exi_senv sample =
  Set.concat_map sample ~f:(fun (ex, src) ->
      let param_senv, phi = ExClause.to_formula ex in
      Logic.BoolTerm.cnf_of exi_senv param_senv phi
      |> Set.Poly.map ~f:(fun (ps, ns, phi) -> ((param_senv, ps, ns, phi), src)))
