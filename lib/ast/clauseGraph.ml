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

(* [Graph.Imperative.Digraph.ConcreteBidirectionalLabeled (V) (E)], rebuilt
   from the same blocks and the same wrapper so that it can also offer
   [add_new_edge_e].  The library's [add_edge_e] first asks [mem_edge_e],
   which scans the source's whole successor set comparing each successor
   structurally ([V.compare]); an example that many derived examples cite as a
   source has thousands of successors, so a seeded labeling's unit propagation,
   whose derived examples cite their transitive sources (hundreds each, about
   450,000 edges in one call), spent minutes in that scan.  [add_new_edge_e] is
   the insertion without the scan; it gives the same graph as [add_edge_e]
   whenever the edge is absent, which is its precondition. *)
module G : sig
  include
    Sig.I
      with type V.t = vertex
       and type V.label = vertex
       and type E.t = vertex * E.t * vertex
       and type E.label = E.t

  val add_new_edge_e : t -> E.t -> unit
  (** [add_new_edge_e g e] adds the edge [e], which must not be in [g] (no
      edge with [e]'s source, label and a destination equal to [e]'s by
      [V.compare]); then it is [add_edge_e g e]. *)
end = struct
  module B = Blocks.Make (Blocks.Make_Hashtbl)
  include B.Digraph.ConcreteBidirectionalLabeled (V) (E)

  (* the wrapper of [Graph.Imperative.Digraph.ConcreteBidirectionalLabeled],
     ocamlgraph 2.2.0, verbatim *)
  let add_vertex g v = ignore (add_vertex g v)
  let add_edge g v1 v2 = ignore (add_edge g v1 v2)
  let add_edge_e g (v1, l, v2) = ignore (add_edge_e g (v1, l, v2))
  let remove_edge g v1 v2 = ignore (remove_edge g v1 v2)
  let remove_edge_e g e = ignore (remove_edge_e g e)

  let remove_vertex g v =
    if HM.mem v g then (
      iter_pred_e (fun e -> remove_edge_e g e) g v;
      iter_succ_e (fun e -> remove_edge_e g e) g v;
      ignore (HM.remove v g))

  let add_new_edge_e g e = ignore (unsafe_add_edge_e g e)
end

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

(* vertices, and vertices with an edge label, identified as the graph's
   vertex table identifies them: by [V.equal] and [V.hash] *)
module VTbl = Stdlib.Hashtbl.Make (V)

module VLTbl = Stdlib.Hashtbl.Make (struct
  type t = vertex * E.t

  let equal (v1, l1) (v2, l2) = V.equal v1 v2 && E.compare l1 l2 = 0
  let hash (v, l) = Hashtbl.hash (V.hash v, l)
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
         per [ExClause.normalize] form; see [spelling_of].  PCSat's
         coordinator always sets it on the graph it solves with; the unset
         state is kept for a test that shows the identification is what
         removes the second spelling *)
  mutable norm_index : (ExClause.t, ExClause.t) Map.Poly.t;
      (* maintained only while [dedup_normalized] is set: an example's
         normal form, and each spelling that arrived, mapped to the first
         spelling stored *)
  edge_targets : unit VTbl.t;
      (* every vertex that has been the destination of an edge of this graph,
         removed or not: an out-set entry names one of them, so an example
         absent from it has no edge into it, not even one that a removal left
         behind (the library removes an edge by the spelling it is given, so
         a vertex removed under a spelling [V.equal] to the stored one but
         structurally different leaves its predecessors' entries in place) *)
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
    edge_targets = VTbl.create 64;
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
    edge_targets = VTbl.copy t.edge_targets;
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
            (* counted so that a run shows a second spelling was replaced by
               the stored one; changes nothing *)
            Common.PhaseTime.event_here "dedup-normalized-twin";
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

(* [add_edges_into t v_ex srcs]: an edge from each source in [srcs] other
   than [v_ex] itself into [v_ex], labelled [Hide] (and the source hidden) for
   a non-unit example whose flag asks for it, [Normal] otherwise.  When [v_ex]
   has never been the destination of an edge ([edge_targets]) no successor set
   holds it, so each edge is inserted without the library's membership scan
   ([G.add_new_edge_e]); the only edge that could already be there is one
   added earlier in this loop from a source the graph identifies with this
   one, which [added] remembers: a source is identified with a vertex by
   [V.equal], as the vertex table does, not by [V.compare], and two spellings
   of one example among the sources would otherwise put two entries for one
   edge into [v_ex]'s predecessor set.  Otherwise every edge goes through
   [G.add_edge_e].  The graph built is the one [add_edges_into_reference]
   builds (assuming, as the vertex table does, that [V.hash] is consistent
   with [V.equal]). *)
let add_edges_into t v_ex srcs =
  let edge (src, hide_und) =
    match src with
    | Example ex when hide_und && (not @@ ExClause.is_unit ex) ->
        hide_vertex t src;
        (src, E.Hide, v_ex)
    | _ -> (src, E.default, v_ex)
  in
  let seen = VTbl.mem t.edge_targets v_ex in
  VTbl.replace t.edge_targets v_ex ();
  if seen then
    Set.iter srcs ~f:(fun ((src, _) as s) ->
        if not @@ V.equal src v_ex then G.add_edge_e t.graph (edge s))
  else
    let added = VLTbl.create 16 in
    Set.iter srcs ~f:(fun ((src, _) as s) ->
        if not @@ V.equal src v_ex then (
          let ((src, l, _) as e) = edge s in
          if not (VLTbl.mem added (src, l)) then (
            VLTbl.replace added (src, l) ();
            G.add_new_edge_e t.graph e)))

(* the loop [add_edges_into] replaces, every edge through the library's
   checked insertion; kept as the specification it is tested against *)
let add_edges_into_reference t v_ex srcs =
  VTbl.replace t.edge_targets v_ex ();
  Set.iter srcs ~f:(fun (src, hide_und) ->
      if not @@ V.equal src v_ex then
        match src with
        | Example ex when hide_und && (not @@ ExClause.is_unit ex) ->
            hide_vertex t src;
            G.add_edge_e t.graph (src, E.Hide, v_ex)
        | _ -> G.add_edge t.graph src v_ex)

let add_ex_from_with add_edges t ex srcs =
  let ex = spelling_of t @@ ExClause.canon ex in
  let v_ex = Example ex in
  (* "new" means absent from the example sets, not from the graph: an edge
     added earlier towards this example (a derived example citing it as a
     premise) creates its vertex implicitly, and testing the vertex
     would then skip the example and lose it for the solver *)
  let present = Set.mem t.pos ex || Set.mem t.neg ex || Set.mem t.und ex in
  if (not present) || Hash_set.Poly.mem t.hide_vertexs v_ex then (
    (* the edges first, which add the vertex: a budget that ends this update
       half-way ([Common.Timer] raises asynchronously) then leaves the example
       linked to a source it came from, never a vertex linked to nothing,
       which pruning by reachability could not remove *)
    add_edges t v_ex srcs;
    G.add_vertex t.graph v_ex;
    Hash_set.Poly.remove t.hide_vertexs v_ex;
    add_example t v_ex)

let add_ex_from t ex srcs = add_ex_from_with add_edges_into t ex srcs

let add_ex_from_reference t ex srcs =
  add_ex_from_with add_edges_into_reference t ex srcs

let add_clause t clause = G.add_vertex t.graph (Clause (Clause.canon clause))

let add_clause_from t clause srcs =
  let v = Clause (Clause.canon clause) in
  G.add_vertex t.graph v;
  VTbl.replace t.edge_targets v ();
  List.iter srcs ~f:(fun src ->
      if not @@ V.equal src v then G.add_edge t.graph src v)

let pos_neg_und_examples_of t = (t.pos, t.neg, t.und)
let examples_of t = Set.Poly.union_list [ t.pos; t.neg; t.und ]

(* [descendants_of_examples t exs]: the examples of [t] that are in [exs]
   (by their stored spelling, looked up without indexing anything new) or
   reachable from one of them along the graph's edges, i.e. derived from
   one, returned as a membership test and its count; clause vertices are not
   collected.  Reads [t] and changes nothing.  The walk carries a visited
   set, since examples can cite each other; vertices are keyed by [V.hash],
   which sees the whole example (a polymorphic hash would not). *)
let descendants_of_examples t exs =
  let stored ex =
    if not t.dedup_normalized then ex
    else
      match Map.Poly.find t.norm_index ex with
      | Some s -> s
      | None -> (
          let ex' = ExClause.canon ex in
          match Map.Poly.find t.norm_index ex' with Some s -> s | None -> ex')
  in
  let visited = VTbl.create 1024 in
  let rec go = function
    | [] -> ()
    | v :: rest ->
        if VTbl.mem visited v || not (G.mem_vertex t.graph v) then go rest
        else (
          VTbl.replace visited v ();
          go (List.rev_append (G.succ t.graph v) rest))
  in
  go (List.map (Set.to_list exs) ~f:(fun ex -> Example (stored ex)));
  let count =
    VTbl.fold (fun v () n -> match v with Example _ -> n + 1 | _ -> n) visited 0
  in
  ((fun ex -> VTbl.mem visited (Example ex)), count)

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

(* [remove_examples_if senv t ~f]: removes every example vertex, hidden or
   not, whose example satisfies [f], together with everything derived from it
   ([remove_succ]); returns how many such examples there were.  Reads only the
   graph's vertices, so it holds whatever edges the graph has. *)
let remove_examples_if senv t ~f =
  let roots =
    G.fold_vertex
      (fun v acc -> match v with Example ex when f ex -> v :: acc | _ -> acc)
      t.graph []
  in
  List.iter roots ~f:(remove_succ senv t);
  List.length roots

(* [refresh_example_sets t]: the example sets recomputed from the graph, as
   [clone] computes them (the unhidden example vertices). *)
let refresh_example_sets t =
  let pos, neg, und = pos_neg_und_examples_of_graph t in
  t.pos <- pos;
  t.neg <- neg;
  t.und <- und

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

(* Whether [papp] applies a predicate of [exi_senv] and [papp'] applies a
   different variable.  Then the two cannot unify: [papp] becomes an
   application of that predicate, and [papp'] either an application of
   another predicate or no predicate application at all, while [unify]
   requires the same predicate.  So the literal is skipped without the
   conversion and the unification that would answer [None]; converting every
   literal of the clause against every unit was half of the resolution's time
   on a problem with many units.  ([COAR_RESOLVE_ALL_HEADS] tries them all.) *)
let different_pred_heads exi_senv papp papp' =
  match (Logic.Term.let_apps papp, Logic.Term.let_apps papp') with
  | (Logic.Var (p, _), _), (Logic.Var (q, _), _) ->
      Map.Poly.mem exi_senv p && not (Ident.tvar_equal p q)
  | _ -> false

let resolve_skip_other_heads =
  Stdlib.Atomic.make (Option.is_none (Sys.getenv "COAR_RESOLVE_ALL_HEADS"))

(* [bvs], when given, must be [Map.key_set exi_senv]; the caller that resolves
   many pairs against one [exi_senv] computes it once (rebuilding the key set
   of every predicate for every literal tried was most of the resolution's
   time on a problem with many units).

   Staged: the literals of the clause the unit is resolved against, and for
   one of them, [None] when it does not unify with the unit and otherwise a
   thunk that builds the resolvent.  The thunk is where the time goes: every
   body atom of the clause is substituted, converted and normalised.  With
   [~pure_first:false] it builds heads, body, pure part in that order and
   always answers [Some]; with [~pure_first:true] it simplifies the pure part
   first and answers [None], building no atom, when that is [true]. *)
let resolve_one_step_staged ~print ?bvs mode ((param_senv, (papp : term)), source)
    exi_senv (((uni_senv, c_pos, c_neg, c_phi) as cl), source1) =
  print @@ lazy ("input clause: " ^ Clause.str_of exi_senv cl);
  let ph = Common.PhaseTime.with_phase in
  let atm1 =
    ph "ros-unit" @@ fun () ->
    LogicOld.Atom.alpha_rename_let
    @@ ExtTerm.to_old_atm exi_senv param_senv papp
  in
  let uni_senv' = Map.force_merge uni_senv param_senv in
  let lits =
    if Stdlib.(mode = `Forward) then
      let _ = print @@ lazy "forward:" in
      c_neg
    else
      let _ = print @@ lazy "backward:" in
      c_pos
  in
  let stage papp' =
    if
      Stdlib.Atomic.get resolve_skip_other_heads
      && different_pred_heads exi_senv papp papp'
    then (
      (* COAR_EXACT_CROSSCHECK set: the skipped unification is made
         anyway, and an answer other than [None] reported on stderr *)
      if PropLogic.Formula.crosscheck then (
        PropLogic.Formula.crosscheck_tick ();
        let atm2 = ExtTerm.to_old_atm exi_senv uni_senv' papp' in
        if
          Option.is_some
            (LogicOld.Atom.unify (Map.key_set exi_senv) atm2 atm1)
        then
          Stdlib.prerr_endline
            "exact-crosscheck: ClauseGraph skipped head UNIFIES");
      None)
    else
      let atm2 =
        ph "ros-lit" @@ fun () -> ExtTerm.to_old_atm exi_senv uni_senv' papp'
      in
      print
      @@ lazy
           (LogicOld.Atom.str_of atm2 ^ " |-> " ^ LogicOld.Atom.str_of atm1);
      let open Option.Monad_infix in
      (ph "ros-unify" @@ fun () ->
       LogicOld.Atom.unify
         (match bvs with Some bvs -> bvs | None -> Map.key_set exi_senv)
         atm2 atm1)
      >>| fun theta (*ToDo*) ~pure_first ->
      ph "ros-resolvent" @@ fun () ->
      let theta = Map.Poly.map ~f:ExtTerm.of_old_term theta in
      let rewrite lits =
        Set.Poly.map lits
          ~f:
            (ExtTerm.subst theta
            >> ExtTerm.to_old_atm exi_senv uni_senv'
            >> Normalizer.normalize_let_atom >> Normalizer.normalize
            >> ExtTerm.of_old_formula)
      in
      let pos () =
        ph "ros-pos" @@ fun () ->
        rewrite
          (if Stdlib.(mode = `Backward) then Set.remove c_pos papp' else c_pos)
      in
      let neg () =
        ph "ros-neg" @@ fun () ->
        rewrite
          (if Stdlib.(mode = `Forward) then Set.remove c_neg papp' else c_neg)
      in
      let phi () =
        ph "ros-phi" @@ fun () ->
        ExtTerm.(simplify_formula exi_senv uni_senv' @@ subst theta c_phi)
      in
      let make c_pos' c_neg' c_phi' =
        let cl' =
          ph "ros-canon" @@ fun () ->
          Clause.canon (uni_senv', c_pos', c_neg', c_phi')
        in
        print @@ lazy ("substituted clause: " ^ Clause.str_of exi_senv cl');
        ( (cl', Set.union source source1),
          Map.Poly.map theta ~f:(ExtTerm.to_old_trm exi_senv uni_senv'),
          cl (* the clause resolved, for derivation records *) )
      in
      if pure_first then
        (* the pure part alone decides whether the resolvent is dropped as
           valid; most resolvents of a refutation are, and their atoms are
           the expensive part *)
        let c_phi' = phi () in
        if BoolTerm.is_true c_phi' then None
        else
          let c_pos' = pos () in
          let c_neg' = neg () in
          Some (make c_pos' c_neg' c_phi')
      else
        let c_pos' = pos () in
        let c_neg' = neg () in
        let c_phi' = phi () in
        Some (make c_pos' c_neg' c_phi')
  in
  (lits, stage)

(* every resolvent of the clause against the unit, as a set; the same
   operations, in the same order, on the same values, as before the staging
   (so the same set, down to its tree) *)
let resolve_one_step ~print ?bvs mode unit exi_senv clause =
  let lits, stage = resolve_one_step_staged ~print ?bvs mode unit exi_senv clause in
  Set.Poly.filter_map lits ~f:(fun papp' ->
      Option.bind (stage papp') ~f:(fun finish -> finish ~pure_first:false))

(* whether [resolve_one_step_all] computes the predicates' key set once (on)
   or once per literal tried (off, [COAR_RESOLVE_KEY_SET_PER_LITERAL]); the
   same set either way *)
let resolve_hoist_key_set =
  Stdlib.Atomic.make
    (Option.is_none (Sys.getenv "COAR_RESOLVE_KEY_SET_PER_LITERAL"))

(* whether a resolvent's pure part is not [true]; one that is is valid, says
   nothing, and is dropped *)
let not_trivial ((((_, _, _, phi), _), _, _) : _ * _ * _) =
  not (BoolTerm.is_true phi)

(* val resolve: Atom.t Set.Poly.t -> Atom.t Set.Poly.t -> t -> t Set.Poly.t *)
let resolve_one_step_all ~print positive negative exi_senv =
  let bvs =
    if Stdlib.Atomic.get resolve_hoist_key_set then Some (Map.key_set exi_senv)
    else None
  in
  let resolve_one_step_all ~print positive negative exi_senv c =
    let cs_b =
      Set.fold negative ~init:Set.Poly.empty ~f:(fun acc neg ->
          Set.union (resolve_one_step ~print ?bvs `Backward neg exi_senv c) acc)
    in
    let cs_f =
      Set.fold positive ~init:Set.Poly.empty ~f:(fun acc pos ->
          Set.union (resolve_one_step ~print ?bvs `Forward pos exi_senv c) acc)
    in
    Set.filter (Set.union cs_b cs_f) ~f:not_trivial
  in
  Set.concat_map ~f:(resolve_one_step_all ~print positive negative exi_senv)

(* How [resolve_find_map] picks the resolvent it answers with.
   [Whole_set] builds the set [resolve_one_step_all] builds and takes
   [Set.find_map] over it.  That reads the set's tree in pre-order (a node
   before its subtrees), so which resolvent comes first depends on the shape
   of the whole tree -- on every resolvent, the ones never read included, and
   on the order the per-clause sets were united in -- and not on the
   resolvents' comparison order alone; no enumeration that builds fewer
   resolvents can tell which one that is.
   [Generation] builds the resolvents one at a time, walking the clause set
   and each clause's literals ([Set.find_map]'s walk), negative units before
   positive ones, and stops at the first that [f] answers: fewer built, but
   possibly another resolvent than [Whole_set] answers with.  It also
   simplifies a resolvent's pure part before its atoms and builds no atom of
   a resolvent whose pure part is [true] (dropped as valid either way):
   [Whole_set] cannot skip them, since [Set.filter] keeps the tree's shape,
   so the dropped elements still decide where the others are read.  Each answer it
   can give is one [Whole_set] could give on a set holding only that
   resolvent, so what [f] guarantees of its answer holds for both. *)
type find_order = Whole_set | Generation

let resolve_find_map ?(order = Whole_set) ~print positive negative exi_senv cs ~f =
  match order with
  | Whole_set ->
      Set.find_map ~f
        (resolve_one_step_all ~print positive negative exi_senv cs)
  | Generation ->
      let bvs =
        if Stdlib.Atomic.get resolve_hoist_key_set then
          Some (Map.key_set exi_senv)
        else None
      in
      let try_units mode units c =
        Set.find_map units ~f:(fun u ->
            let lits, stage =
              resolve_one_step_staged ~print ?bvs mode u exi_senv c
            in
            Set.find_map lits ~f:(fun papp' ->
                Option.bind (stage papp') ~f:(fun finish ->
                    Common.PhaseTime.event "resolvent-tried";
                    match finish ~pure_first:true with
                    | None -> None
                    | Some r ->
                        Common.PhaseTime.event "resolvent-built";
                        f r)))
      in
      Set.find_map cs ~f:(fun c ->
          match try_units `Backward negative c with
          | Some _ as answer -> answer
          | None -> try_units `Forward positive c)

let to_clause_set_with_src exi_senv sample =
  Set.concat_map sample ~f:(fun (ex, src) ->
      let param_senv, phi = ExClause.to_formula ex in
      Logic.BoolTerm.cnf_of exi_senv param_senv phi
      |> Set.Poly.map ~f:(fun (ps, ns, phi) -> ((param_senv, ps, ns, phi), src)))
