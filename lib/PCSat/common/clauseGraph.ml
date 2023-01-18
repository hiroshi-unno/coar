open Core
open Graph
open Ast
open Logic
open Common
open Common.Ext

let verbose = false
module Debug = Debug.Make (val Debug.Config.(if verbose then enable else disable))
type vertex =
  | Example of ExClause.t
  | Clause of Clause.t
  | Dummy
  (* | Constr of Logic.sort_env_map * Logic.term *)

module V = struct

  type t = vertex
  let compare v1 v2 =
    match v1, v2 with
    | Dummy, Dummy -> 0
    | Clause c1, Clause c2 -> Stdlib.compare c1 c2
    | Example e1, Example e2 -> Stdlib.compare e1 e2
    | Dummy, _ -> 1
    | _, Dummy -> -1
    | Clause _, _ -> -1
    | _, Clause _ -> 1
  let equal v1 v2 =
    match v1, v2 with
    | Clause c1, Clause c2 -> Clause.equal c1 c2
    | Example e1, Example e2 -> ExClause.equal e1 e2
    | Dummy, Dummy -> true
    | _, _ -> false
  let hash = Hashtbl.hash

end
let vstr_of_vertex senv _hide_vertexs v=
  String.concat ~sep:"\\\\" @@
  String.split ~on:'\\' @@
  "\"" ^
  (* begin
     if Hash_set.mem hide_vertexs v then "(x)" else "(o)"
     end ^ *)
  match v with
  | Dummy -> "Dummy\""
  | Example ex -> sprintf "%s\"" (ExClause.str_of ex)
  | Clause cl -> sprintf "%s\"" (Ast.Clause.str_of senv cl)


module E = struct
  type lable = | Hide | Normal
  type t = lable
  let default = Normal
  let compare e1 e2 =
    match e1, e2 with
    | Hide, Normal -> 1
    | Normal, Hide -> -1
    | _ -> 0
end
module G = Imperative.Digraph.ConcreteBidirectionalLabeled(V)(E)
module W = struct
  type t = int
  type edge = (vertex *  E.lable * vertex) (** This is G.edge *)
  let zero = 0
  let add = (+)
  let compare = Int.compare
  let weight _ = 1
end

module Dijkstra = Path.Dijkstra(G)(W)

let black = 0x000000
and white = 0xFFFFFF
and red = 0xFF0000
and green = 0x00FF00
and blue = 0x0000FF
and yellow = 0xFFFF00
and cyan = 0x00FFFF
and magenta = 0xFF00FF

module type EnvType = sig val senv : Logic.sort_env_map val hide_vertexs : vertex Hash_set.Poly.t end
module Dot (Env:EnvType) = Graph.Graphviz.Dot(struct
    include G (* use the graph module from above *)
    let edge_attributes _ = [`Color 4711]
    let default_edge_attributes _ = []
    let get_subgraph _ = None
    let vertex_attributes v =
      (if Hash_set.mem Env.hide_vertexs v then [`Color red] else []) @
      (match v with | Example _ -> [`Shape `Box] | _ -> [`Shape `Oval; `Penwidth 3.0; `Style `Bold])
    let vertex_name v = vstr_of_vertex Env.senv Env.hide_vertexs v
    let default_vertex_attributes _ = []
    let graph_attributes _ = [`Rankdir `LeftToRight]
  end)

type t =
  {
    graph : G.t;
    hide_vertixs : vertex Hash_set.Poly.t;
    mutable pos : ExClauseSet.t;
    mutable neg : ExClauseSet.t;
    mutable und : ExClauseSet.t
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
    hide_vertixs = Hash_set.Poly.create ();
    pos = Set.Poly.empty;
    neg = Set.Poly.empty;
    und = Set.Poly.empty
  }

let examples_of_graph t =
  G.fold_vertex (fun v acc ->
      match v with
      | Example ex when not @@ Hash_set.Poly.mem t.hide_vertixs v  ->
        if (G.out_degree t.graph v = 0 || ExClause.is_unit ex)   then
          Set.Poly.add acc ex
        else acc
      | _ -> acc) t.graph Set.Poly.empty

let pos_neg_und_examples_of_graph t =
  G.fold_vertex (fun v (pos, neg, und) ->
      match v with
      | Example ex when not @@ Hash_set.Poly.mem t.hide_vertixs v ->
        if ExClause.is_unit_positive ex then (Set.Poly.add pos ex, neg, und)
        else if ExClause.is_unit_negative ex then (pos, Set.Poly.add neg ex, und)
        else (pos, neg, Set.Poly.add und ex)
      | _ -> (pos, neg, und))
    t.graph (Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)
let clone t =
  let pos, neg, und = pos_neg_und_examples_of_graph t in
  {
    graph = G.copy t.graph;
    hide_vertixs = Hash_set.copy t.hide_vertixs;
    pos; neg; und
  }

let rec pred_clause_vertexs_of g v =
  match v with
  | Dummy
  | Clause _ -> [v]
  | _ -> List.concat_map (G.pred g v) ~f:(pred_clause_vertexs_of g)

let rec pred_clause_und_vertexs_of g v =
  match v with
  | Dummy
  | Clause _ -> [v]
  | Example e when Fn.non ExClause.is_unit e -> [v]
  | _ -> List.concat_map (G.pred g v) ~f:(pred_clause_und_vertexs_of g)

let add_example (t:t) v =
  match v with
  | Example ex ->
    if ExClause.is_unit_positive ex then
      t.pos <- Set.Poly.add t.pos ex
    else if ExClause.is_unit_negative ex then
      t.neg <- Set.Poly.add t.neg ex
    else
      t.und <- Set.Poly.add t.und ex
  | _ -> ()

let remove_example_in_exset (t:t) ex =
  match ex with
  | Example ex ->
    if ExClause.is_unit_positive ex then
      t.pos <- Set.Poly.remove t.pos ex
    else if ExClause.is_unit_negative ex then
      t.neg <- Set.Poly.remove t.neg ex
    else
      t.und <- Set.Poly.remove t.und ex
  | _ -> ()

let remove_vertex t v =
  remove_example_in_exset t v;
  Hash_set.remove t.hide_vertixs v;
  let preds = G.pred_e t.graph v in
  G.remove_vertex t.graph v;
  List.iter preds ~f:(fun (src, lable, _) ->
      match lable with
      | E.Hide when Hash_set.mem t.hide_vertixs src ->
        let succs = G.succ_e t.graph src in
        if List.for_all succs
            ~f:(fun (_, lable, _) -> match lable with | E.Hide -> false | _ -> true) then begin
          Hash_set.remove t.hide_vertixs src;
          add_example t src
        end
      | _ -> ()
    )

let hide_vertex t v = remove_example_in_exset t v; Hash_set.add t.hide_vertixs v
let hide_und_example (t:t) v =
  match v with
  | Example ex ->
    if Fn.non ExClause.is_unit ex then begin
      hide_vertex t v;
    end
  | _ -> ()

let add_ex_from t ex srcs =
  let v_ex = (Example ex) in
  if not (G.mem_vertex t.graph v_ex) || Hash_set.Poly.mem t.hide_vertixs v_ex then begin
    Hash_set.Poly.remove t.hide_vertixs v_ex;
    G.add_vertex t.graph v_ex;
    add_example t v_ex;
    List.iter srcs ~f:(fun (src, hide_und) ->
        if not @@ V.equal src v_ex then begin
          match src with
          | Example ex when hide_und && not @@ ExClause.is_unit ex ->
            hide_vertex t src;
            G.add_edge_e t.graph (src, E.Hide, v_ex)
          | _ -> G.add_edge t.graph src v_ex;
        end)
  end
let add_clause t clause =  G.add_vertex t.graph (Clause clause)
let add_clause_from t clause srcs =
  let v = (Clause clause) in
  G.add_vertex t.graph v;
  List.iter srcs ~f:(fun (src) -> if not @@ V.equal src v then G.add_edge t.graph src v)

let pos_neg_und_examples_of t =
  t.pos, t.neg, t.und
let examples_of t = Set.Poly.union_list [t.pos; t.neg; t.und]

let remove_succ senv t (v:vertex) =
  ignore senv;
  let rec dfs history succs =
    match succs with
    | hd::tl ->
      if Set.Poly.mem history hd then dfs history tl
      else
        let history' = Set.Poly.add history hd in
        let succs' = G.succ t.graph hd @ tl in
        dfs history' succs'
    | [] -> history
  in
  if G.mem_vertex t.graph v then
    let removed_vertexs = dfs Set.Poly.empty [v] in
    (* print_endline @@ sprintf "rm_succs(%s):%d" (str_of_vertex senv v) (Set.Poly.length removing_vertexs); *)
    Set.Poly.iter removed_vertexs ~f:(remove_vertex t)

let clauses_of t =
  G.fold_vertex
    (fun v acc ->
       match v with
       | Clause c when not @@ Hash_set.Poly.mem t.hide_vertixs v -> Set.Poly.add acc c
       | _ -> acc)
    t.graph
    Set.Poly.empty

let path_to t st ed =
  if G.mem_vertex t.graph st && G.mem_vertex t.graph ed then
    try
      Dijkstra.shortest_path t.graph st ed
      |> fst
      |> List.map ~f:(fun edge -> G.E.src edge, G.E.dst edge)
    with _ -> []
  else []

let rec hide_succs t v =
  hide_vertex t v;
  remove_example_in_exset t v;
  List.iter (G.succ t.graph v) ~f:(fun v -> remove_example_in_exset t v; hide_succs t v)

module Printer (Env:EnvType) = Gml.Print(G)
    (struct
      let node v = ["label", Gml.String (vstr_of_vertex Env.senv Env.hide_vertexs v)]
      let edge _ = ["label", Gml.String ""]
    end)

let output_graph ?(pre="") ~id t senv =
  let module Dot = Dot(struct let senv = senv let hide_vertexs = t.hide_vertixs end) in
  let module Printer = Printer(struct let senv = senv let hide_vertexs = t.hide_vertixs end) in
  let file_name =
    match id with
    | Some i -> sprintf "output_graph_#%d_%s.dot" i pre
    | None -> sprintf "output_graph_%s.dot" pre
  in
  let file = Out_channel.create ~binary:false file_name in
  Dot.output_graph file t.graph;
  (* Dot.output_graph Out_channel.stdout t.graph; *)
  (* Printer.print (Format.std_formatter) t.graph; *)
  Out_channel.flush file;
  Out_channel.close file;
  ignore @@ Sys_unix.command @@ sprintf "dot -Tsvg %s > %s.svg" file_name file_name;
  ignore @@ Sys_unix.command @@ sprintf "rm %s" file_name


(** Porting from Clause/ClauseSet *)
let simplify_with positive negative ((senv, c_pos, c_neg, c_phi), source) =
  (* ToDo: improve this to exploit parametric examples *)
  let positive1 = Set.Poly.map ~f:(fun ((_, term), _src) -> term) positive in
  let negative1 = Set.Poly.map ~f:(fun ((_, term), _src) -> term) negative in
  if Set.Poly.is_empty (Set.Poly.inter positive1 c_pos) &&
     Set.Poly.is_empty (Set.Poly.inter negative1 c_neg)
  then
    let source =
      (Set.Poly.filter_map negative ~f:(fun ((_, term), src) ->
           if not @@ Set.Poly.mem c_pos term then Some src else None)
       |> Set.Poly.to_list) @
      (Set.Poly.filter_map positive ~f:(fun ((_, term), src) ->
           if not @@ Set.Poly.mem c_neg term then Some src else None)
       |> Set.Poly.to_list)
      |> List.concat
      |> List.append source
    in
    Some ((senv, Set.Poly.diff c_pos negative1, Set.Poly.diff c_neg positive1, c_phi), source)
  else None
let simplify_with positive negative = Set.Poly.filter_map ~f:(simplify_with positive negative)
let resolve_one_step
    mode ((param_senv, (papp: term)), source)
    exi_senv ((uni_senv, c_pos, c_neg, c_phi) as cl , source1) =
  let open Clause in
  Debug.print @@ lazy ("cl: " ^ str_of exi_senv cl);
  let atm1 = LogicOld.Atom.alpha_rename_let @@ ExtTerm.to_old_atom exi_senv param_senv papp [] in
  let uni_senv' = Map.force_merge uni_senv param_senv in
  (if Stdlib.(mode = `Forward)
   then let _ = Debug.print @@ lazy "forward:" in c_neg
   else let _ = Debug.print @@ lazy "backward:" in c_pos)
  |> Set.Poly.filter_map ~f:(fun papp' ->
      let atm2 = ExtTerm.to_old_atom exi_senv uni_senv' papp' [] in
      Debug.print @@ lazy ("atm1: " ^ LogicOld.Atom.str_of atm1);
      Debug.print @@ lazy ("atm2: " ^ LogicOld.Atom.str_of atm2);
      let open Option in
      LogicOld.Atom.unify (Map.key_set exi_senv) atm2 atm1 >>= fun theta (*ToDo*) ->
      let theta = Map.Poly.map ~f:ExtTerm.of_old_term theta in
      let c_pos' =
        Set.Poly.map (if Stdlib.(mode = `Backward) then Set.Poly.remove c_pos papp' else c_pos) ~f:(fun atm ->
            atm |> ExtTerm.subst theta |> Fn.flip (ExtTerm.to_old_atom exi_senv uni_senv') [] |>
            Normalizer.normalize_let_atom |> Normalizer.normalize |> ExtTerm.of_old_formula) in
      let c_neg' =
        Set.Poly.map (if Stdlib.(mode = `Forward) then Set.Poly.remove c_neg papp' else c_neg) ~f:(fun atm ->
            atm |> ExtTerm.subst theta |> Fn.flip (ExtTerm.to_old_atom exi_senv uni_senv') [] |>
            Normalizer.normalize_let_atom |> Normalizer.normalize |> ExtTerm.of_old_formula) in
      let c_phi' =
        ExtTerm.simplify_formula exi_senv uni_senv' @@ ExtTerm.subst theta c_phi
      in
      let cl' = uni_senv', c_pos', c_neg', c_phi' in
      Debug.print @@ lazy ("cl': " ^ str_of exi_senv cl');
      Some ((cl', source @ source1),
            Map.Poly.map theta ~f:(Fn.flip (ExtTerm.to_old_term exi_senv uni_senv') [])))

(* val resolve: Atom.t Set.Poly.t -> Atom.t Set.Poly.t -> t -> t Set.Poly.t *)
let resolve_one_step_all positive negative exi_senv c =
  let cs_b = Set.Poly.fold negative ~init:Set.Poly.empty
      ~f:(fun acc neg -> Set.Poly.union (resolve_one_step `Backward neg exi_senv c) acc) in
  let cs_f = Set.Poly.fold positive ~init:Set.Poly.empty
      ~f:(fun acc pos -> Set.Poly.union (resolve_one_step `Forward pos exi_senv c) acc) in
  Set.Poly.union cs_b cs_f |>
  Set.Poly.filter ~f:(fun (((_, _, _, t), _), _) -> Fn.non BoolTerm.is_true t)

let resolve_one_step_all positive negative exi_senv =
  Set.concat_map ~f:(resolve_one_step_all positive negative exi_senv)

let to_clause_set_with_src exi_senv sample =
  Set.concat_map sample ~f:(fun (ex, src) ->
      let param_senv, phi = ExClause.to_formula ex in
      let cnfs = Logic.BoolTerm.cnf_of exi_senv param_senv phi in
      Set.Poly.map cnfs ~f:(fun (ps, ns, phi) -> (param_senv, ps, ns, phi), src))
