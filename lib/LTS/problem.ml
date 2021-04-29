open Core
open Ast
open LogicOld
open Graph

let nondet_prefix = "#nondet"

type lts = string option(*start*) * string option(*error*) * string option(*cutpoint*) * transition list
and transition = string * command * string
and command = Skip | Assume of LogicOld.Formula.t | Subst of (Ident.tvar * LogicOld.Sort.t) * LogicOld.Term.t | Seq of command * command | Choice of command * command

type mode = Term | NonTerm | CondTerm
type t = lts * mode

let seq = function [] -> Skip | c::cs -> List.fold_left ~init:c cs ~f:(fun c1 c2 -> Seq (c1, c2))
let seq cs = seq @@ List.filter cs ~f:(fun c -> not @@ Stdlib.(=) c Skip)
let choice = function [] -> assert false | c::cs -> List.fold_left ~init:c cs ~f:(fun c1 c2 -> Choice (c1, c2))

let rec term_sort_env_of_command = function
  | Skip -> Set.Poly.empty
  | Assume atm -> Formula.term_sort_env_of atm
  | Subst ((x, s), t) -> Set.Poly.add (Term.term_sort_env_of t) (x, s)
  | Seq (c1, c2) | Choice (c1, c2) -> Set.Poly.union (term_sort_env_of_command c1) (term_sort_env_of_command c2)
let term_sort_env_of_transition (_, c, _) = term_sort_env_of_command c
let term_sort_env_of (_, _, _, trs) =
  Set.Poly.union_list @@ List.map ~f:term_sort_env_of_transition trs

let rec is_effect_free = function
  | Skip | Assume _ -> true
  | Subst ((_, _), t) -> Set.Poly.for_all (Term.tvs_of t) ~f:(fun x -> not @@ String.is_prefix (Ident.name_of_tvar x) ~prefix:nondet_prefix)
  | Seq (c1, c2) | Choice (c1, c2) -> is_effect_free c1 && is_effect_free c2

let rec str_of_command = function
  | Skip -> "skip;\n"
  | Assume atom ->
    Printf.sprintf "assume(%s);\n" (LogicOld.Formula.str_of ~priority:20 atom)
  | Subst ((x, _sort), t) ->
    Printf.sprintf "%s := %s;\n" (Ident.name_of_tvar x) (LogicOld.Term.str_of t)
  | Seq (c1, c2) -> str_of_command c1 ^ str_of_command c2
  | Choice (c1, c2) -> "(\n" ^ str_of_command c1 ^ ") || (\n" ^ str_of_command c2 ^ ");\n"

let str_of_transition (from, c, to_) =
  Printf.sprintf "FROM: %s;\n" from ^ str_of_command c ^ Printf.sprintf "TO: %s;\n\n" to_

let str_of_lts (s, e, c, trans) =
  (match s with None -> "" | Some s -> Printf.sprintf "START: %s;\n" s) ^
  (match e with None -> "" | Some e -> Printf.sprintf "ERROR: %s;\n" e) ^
  (match c with None -> "" | Some c -> Printf.sprintf "CUTPOINT: %s;\n" c) ^
  String.concat @@ List.map ~f:str_of_transition trans

let rec wp c phi = match c with
  | Skip -> phi
  | Assume phi' -> Formula.mk_imply phi' phi
  | Subst ((x, _s), t) -> Formula.subst (Map.Poly.singleton x t) phi
  | Seq (c1, c2) -> wp c1 (wp c2 phi)
  | Choice (c1, c2) -> Formula.and_of [wp c1 phi; wp c2 phi]

let used_vars c =
  let rec aux env = function
    | Skip -> env
    | Assume phi ->
      let env' =
        Set.Poly.filter (Formula.term_sort_env_of phi) ~f:(fun (x, _) ->
            not @@ String.is_prefix ~prefix:nondet_prefix @@ Ident.name_of_tvar x) in
      Set.Poly.union env' env
    | Subst ((x, _), t) ->
      let env' =
        Set.Poly.filter (Term.term_sort_env_of t) ~f:(fun (x, _) ->
            not @@ String.is_prefix ~prefix:nondet_prefix @@ Ident.name_of_tvar x) in
      Set.Poly.union env' (Set.Poly.filter env ~f:(fun (y, _) -> not @@ Stdlib.(=) x y))
    | Seq (c1, c2) -> aux (aux env c2) c1
    | Choice (c1, c2) -> Set.Poly.union (aux env c1) (aux env c2)
  in aux Set.Poly.empty c

let defined_vars c =
  let rec aux env = function
    | Skip -> env
    | Assume _ -> env
    | Subst ((x, s), _) -> Set.Poly.union (Set.Poly.singleton (x, s)) env
    | Seq (c1, c2) -> aux (aux env c2) c1
    | Choice (c1, c2) -> Set.Poly.inter (aux env c1) (aux env c2)
  in aux Set.Poly.empty c

module V (*: Sig.COMPARABLE*) = struct
  type t = string
  let compare = String.compare
  let hash = String.hash
  let equal = String.equal
end
module E (*: Sig.ORDERED_TYPE_DFT*) = struct
  type t = command
  let compare = Stdlib.compare
  let default = Skip
end
module G = Imperative.Digraph.ConcreteBidirectionalLabeled(V)(E)
let graph_of (trans : transition list) =
  let g = G.create () in
  List.iter trans ~f:(fun (f, c, t) ->
      let v1 = G.V.create f in
      let v2 = G.V.create t in
      G.add_vertex g v1;
      G.add_vertex g v2;
      G.add_edge_e g (G.E.create v1 c v2));
  g
let of_graph cfa : transition list =
  G.fold_edges_e (fun (f, c, t) trans -> (f, c, t) :: trans) cfa []
exception Found_Edges of G.edge list
let contract_edges cfa =
  try
    G.iter_edges (fun s d -> let edges = G.find_all_edges cfa s d in if List.length edges > 1 then raise (Found_Edges edges) else ()) cfa;
    false
  with Found_Edges [] -> assert false
     | Found_Edges (((s, _ ,d) :: _) as es) ->
       (*print_endline ("eliminating edge (" ^ s ^ ", " ^ d ^ ")");*)
       let c = choice @@ List.map es ~f:(fun (_, c, _) -> c) in
       G.remove_edge cfa s d; 
       G.add_edge_e cfa (s, c, d);
       true
exception Found_Vertex_1_1 of G.edge * G.vertex * G.edge
let contract_vertex_1_1 s cfa =
  try
    G.iter_vertex (fun v ->
        if String.(s = v) (* ignore start node *) || 
           not @@ List.is_empty @@ G.find_all_edges cfa v v (*ignore vertex with a self-loop*)
        then () else
          match G.pred_e cfa v, G.succ_e cfa v with
          | [e1], [e2] -> raise (Found_Vertex_1_1 (e1, v, e2))
          | _ -> ()) cfa;
    false
  with Found_Vertex_1_1 ((s, c1, _d), v, (_s, c2, d)) ->
    (*print_endline ("eliminating vertex " ^ v);*)
    G.remove_vertex cfa v; 
    G.add_edge_e cfa (s, seq [c1; c2], d);
    true
exception Found_Vertex_1_n of G.edge * G.vertex * G.edge list
let contract_vertex_1_n s cfa =
  try
    G.iter_vertex (fun v ->
        if String.(s = v) (* ignore start node *) || 
           not @@ List.is_empty @@ G.find_all_edges cfa v v (*ignore vertex with a self-loop*)
        then () else
          match G.pred_e cfa v, G.succ_e cfa v with
          | [(_, c, _) as e], es when is_effect_free c -> raise (Found_Vertex_1_n (e, v, es))
          | _ -> ()) cfa;
    false
  with Found_Vertex_1_n ((s, c1, _d), v, es) ->
    (*print_endline ("eliminating vertex " ^ v);*)
    G.remove_vertex cfa v; 
    List.iter es ~f:(fun (_s, c2, d) -> G.add_edge_e cfa (s, seq [c1; c2], d));
    true
exception Found_Vertex_n_1 of G.edge list * G.vertex * G.edge
let contract_vertex_n_1 s cfa =
  try
    G.iter_vertex (fun v ->
        if String.(s = v) (* ignore start node *) || 
           not @@ List.is_empty @@ G.find_all_edges cfa v v (*ignore vertex with a self-loop*)
        then () else
          match G.pred_e cfa v, G.succ_e cfa v with
          | es, [(_, c, _) as e] when is_effect_free c -> raise (Found_Vertex_n_1 (es, v, e))
          | _ -> ()) cfa;
    false
  with Found_Vertex_n_1 (es, v, (_s, c2, d)) ->
    (*print_endline ("eliminating vertex " ^ v);*)
    G.remove_vertex cfa v; 
    List.iter es ~f:(fun (s, c1, _d) -> G.add_edge_e cfa (s, seq [c1; c2], d));
    true
let rec simplify s cfa =
  if contract_edges cfa || contract_vertex_1_1 s cfa || contract_vertex_1_n s cfa || contract_vertex_n_1 s cfa then
    simplify s cfa
  else cfa

module LiveVariables = Graph.Fixpoint.Make(G)
    (struct
      type vertex = G.E.vertex
      type edge = G.E.t
      type g = G.t
      type data = (Ident.tvar * Sort.t) Set.Poly.t
      let direction = Graph.Fixpoint.Backward
      let equal = Set.Poly.equal
      let join = Set.Poly.union
      let analyze (_, c, _) env =
        let def = Set.Poly.map ~f:fst @@ defined_vars c in
        let use = used_vars c in
        Set.Poly.union use (Set.Poly.filter env ~f:(fun (x, _) -> not @@ Set.Poly.mem def x)) 
    end)

let analyze (s, e, c, trans) =
  match s with
  | None ->
    (fun _ -> Set.Poly.empty), Set.Poly.empty, (s, e, c, trans)
  | Some s ->
    let cfa = simplify s (graph_of trans) in
    let live_vars = LiveVariables.analyze (fun _ -> Set.Poly.empty) cfa in
    let cut_points = G.fold_vertex (fun v s -> Set.Poly.add s v) cfa Set.Poly.empty in
    let trans' = of_graph cfa in
    live_vars, cut_points, (Some s, e, c, trans')
