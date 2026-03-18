open Core
open Graph
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld

let bv_mode = ref false
let nondet_count = ref 0
let nondet_prefix = "#nondet"

let mk_nondet = function
  | None ->
      incr nondet_count;
      Ident.Tvar (nondet_prefix ^ string_of_int !nondet_count)
  | Some (bits, signed) ->
      incr nondet_count;
      Ident.Tvar
        (nondet_prefix
        ^ string_of_int !nondet_count
        ^ "_" ^ string_of_int bits
        ^ if signed then "_s" else "_u")

type lts =
  string option (* start *)
  * (Ident.tvar * Sort.t) list (* types *)
  * string option (* error *)
  * string option (* cutpoint *)
  * transition list

and transition = string * command * string

and command =
  | Skip
  | Assume of LogicOld.Formula.t
  | Subst of (Ident.tvar * LogicOld.Sort.t) * LogicOld.Term.t
  | Seq of command * command
  | Choice of command * command

type mode = Safe | NonSafe | Term | NonTerm | MuCal | Rel
type t = lts * mode

let seq = function
  | [] -> Skip
  | c :: cs -> List.fold_left ~init:c cs ~f:(fun c1 c2 -> Seq (c1, c2))

let seq = List.filter ~f:(Stdlib.( <> ) Skip) >> seq

let choice = function
  | [] -> assert false
  | c :: cs -> List.fold_left ~init:c cs ~f:(fun c1 c2 -> Choice (c1, c2))

let subst = List.map2_exn ~f:(fun arg term -> Subst (arg, term))

let commands_of_formula ~print args rel =
  let rel =
    let rel =
      Typeinf.typeinf_formula ~print ~default:(Some T_int.SInt (*ToDo*)) rel
    in
    if Formula.is_quantifier_free rel then rel
    else Z3Smt.Z3interface.qelim ~id:None ~fenv:(LogicOld.get_fenv ()) rel
  in
  let args_set = Set.Poly.of_list @@ List.map ~f:fst args in
  let phis_cond, phis_rest =
    Set.partition_tf (Formula.conjuncts_of rel) ~f:(fun phi ->
        Set.disjoint (Formula.fvs_of phi) args_set)
  in
  let sub, phis_rest, phis_cond =
    let rec loop (sub, phis_rest, phis_cond) =
      let sub', phis_rest' =
        Set.partition_map phis_rest ~f:(fun phi ->
            try
              let t1, t2, _ = Formula.let_eq phi in
              (*ToDo: the following code is ad hoc*)
              if
                Term.is_var t1
                && Set.mem args_set (fst @@ fst @@ Term.let_var t1)
                && Set.disjoint (Term.fvs_of t2) args_set
              then First (fst @@ Term.let_var t1, t2)
              else if
                Term.is_var t2
                && Set.mem args_set (fst @@ fst @@ Term.let_var t2)
                && Set.disjoint (Term.fvs_of t1) args_set
              then First (fst @@ Term.let_var t2, t1)
              else Second phi
            with _ -> Second phi)
      in
      if Set.is_empty sub' then (sub, phis_rest, phis_cond)
      else
        let sub', phiss_rest =
          List.unzip
          @@ List.map ~f:(fun res ->
              let arg = fst @@ List.hd_exn res in
              match List.map ~f:snd res with
              | [] -> assert false
              | t :: ts ->
                  ( (arg, t),
                    Set.Poly.of_list
                    @@ List.map ts ~f:(Formula.eq (uncurry Term.mk_var arg)) ))
          @@ List.classify (fun x y -> Stdlib.(fst x = fst y))
          @@ Set.to_list sub'
        in
        let subst =
          Map.Poly.of_alist_exn @@ List.map sub' ~f:(fun ((x, _), t) -> (x, t))
        in
        loop
          ( Set.union sub @@ Set.Poly.of_list sub',
            Set.Poly.map phis_rest' ~f:(Formula.subst subst),
            Set.union phis_cond
            @@ Set.Poly.map ~f:(Formula.subst subst)
            @@ Set.Poly.union_list phiss_rest )
    in
    loop (Set.Poly.empty, phis_rest, phis_cond)
  in
  let sub = Map.of_set_exn sub in
  let phi_rest = Formula.and_of @@ Set.to_list phis_rest in
  Assume (Formula.and_of @@ Set.to_list phis_cond)
  :: List.map args ~f:(fun arg ->
      if Map.Poly.mem sub arg then Subst (arg, Map.Poly.find_exn sub arg)
      else Subst (arg, Term.mk_var (mk_nondet None (*ToDo*)) (snd arg)))
  @ [ Assume phi_rest ]

let rec term_sort_env_of_command = function
  | Skip -> Set.Poly.empty
  | Assume atm -> Formula.term_sort_env_of atm
  | Subst ((x, s), t) -> Set.add (Term.term_sort_env_of t) (x, s)
  | Seq (c1, c2) | Choice (c1, c2) ->
      Set.union (term_sort_env_of_command c1) (term_sort_env_of_command c2)

let term_sort_env_of_transition (_, c, _) = term_sort_env_of_command c

let term_sort_env_of (_, _, _, _, trs) =
  Set.Poly.union_list @@ List.map ~f:term_sort_env_of_transition trs

let rec tvs_of_command = function
  | Skip -> Set.Poly.empty
  | Assume atm -> Formula.tvs_of atm
  | Subst ((x, _s), t) -> Set.add (Term.tvs_of t) x
  | Seq (c1, c2) | Choice (c1, c2) ->
      Set.union (tvs_of_command c1) (tvs_of_command c2)

let tvs_of_transition (_, c, _) = tvs_of_command c

let tvs_of (_, _, _, _, trs) =
  Set.Poly.union_list @@ List.map ~f:tvs_of_transition trs

let print_log = false

let rec cgen_command senv = function
  | Skip -> (senv, Set.Poly.empty)
  | Assume atm ->
      Typeinf.cgen_formula
        ~print:(fun s -> if print_log then print_endline (force s) else ())
        senv atm
  | Subst ((x, s), t) -> (
      let senv, s', constrs =
        Typeinf.cgen_term
          ~print:(fun s -> if print_log then print_endline (force s) else ())
          senv t
      in
      ( senv,
        match Map.Poly.find senv x with
        | None -> Set.add constrs (Typeinf.CEq (s, s'))
        | Some s'' ->
            Set.add
              (Set.add constrs (Typeinf.CEq (s'', s)))
              (Typeinf.CEq (s'', s')) ))
  | Seq (c1, c2) | Choice (c1, c2) ->
      let senv, cs1 = cgen_command senv c1 in
      let senv, cs2 = cgen_command senv c2 in
      (senv, Set.union cs1 cs2)

let cgen_transition senv (_, c, _) = cgen_command senv c

let rec subst_sorts_command senv map = function
  | Skip -> Skip
  | Assume atm -> Assume (Formula.subst_sorts map atm)
  | Subst ((x, s), t) ->
      Subst
        ( ( x,
            match Map.find senv x with
            | Some s -> s
            | None -> Term.subst_sorts_sort map s ),
          Term.subst_sorts map t )
  | Seq (c1, c2) ->
      Seq (subst_sorts_command senv map c1, subst_sorts_command senv map c2)
  | Choice (c1, c2) ->
      Choice (subst_sorts_command senv map c1, subst_sorts_command senv map c2)

let subst_sorts_trans senv map (f, c, t) = (f, subst_sorts_command senv map c, t)

let rec str_of_command = function
  | Skip -> "skip;\n"
  | Assume atom ->
      sprintf "assume(%s);\n" (LogicOld.Formula.str_of ~priority:20 atom)
  | Subst ((x, sort), t) ->
      if false then
        sprintf "%s := %s;\n" (Ident.name_of_tvar x) (LogicOld.Term.str_of t)
      else
        sprintf "%s : %s := %s;\n" (Ident.name_of_tvar x)
          (Term.str_of_sort sort) (LogicOld.Term.str_of t)
  | Seq (c1, c2) -> str_of_command c1 ^ str_of_command c2
  | Choice (c1, c2) ->
      "(\n" ^ str_of_command c1 ^ ") || (\n" ^ str_of_command c2 ^ ");\n"

let str_of_transition (from, c, to_) =
  sprintf "FROM: %s;\n%sTO: %s;\n\n" from (str_of_command c) to_

let str_of_lts (s, _ (*ToDo*), e, c, trans) =
  (match s with None -> "" | Some s -> sprintf "START: %s;\n" s)
  ^ (match e with None -> "" | Some e -> sprintf "ERROR: %s;\n" e)
  ^ (match c with None -> "" | Some c -> sprintf "CUTPOINT: %s;\n" c)
  ^ String.concat_map_list ~f:str_of_transition trans

let typeinf ?(bv_mode = false) (s, types, e, c, trans) =
  let types =
    if bv_mode then types
    else
      List.map types ~f:(function
        | _, T_bv.SBV _ -> failwith "not supported"
        | bind -> bind (*ToDo*))
  in
  let senv =
    Map.of_set_exn
    @@ Set.Poly.map
         (tvs_of (s, types, e, c, trans))
         ~f:(fun x ->
           match List.Assoc.find ~equal:Stdlib.( = ) types x with
           | None -> (x, Sort.mk_fresh_svar ())
           | Some s -> (x, s))
  in
  let _, constrs =
    List.fold trans ~init:(senv, Set.Poly.empty) ~f:(fun (senv, cs) tr ->
        let senv, cs' = cgen_transition senv tr in
        (senv, Set.union cs cs'))
  in
  let nums, map =
    Typeinf.solve constrs ~print:(fun s ->
        if print_log then print_endline (force s) else ())
  in
  let default_size = Some (*ToDo*) 32 in
  let map =
    Typeinf.elim_nums ~to_sus:false
      ~default:(Some (if bv_mode then T_bv.SBV default_size else T_int.SInt))
      nums map
  in
  (*let map =
    Map.Poly.map map ~f:(function
      | T_bv.SBV None -> T_bv.SBV default_size
      | s (*ToDo*) -> s)
  in*)
  let svs = Set.diff (Typeinf.svs_of_constrs constrs) (Map.Poly.key_set map) in
  if false then
    print_endline
    @@ sprintf "unsolved vars: %s"
         (String.concat_map_set ~sep:", " ~f:Ident.name_of_svar svs);
  let map' =
    Map.of_set_exn
    @@ Set.Poly.map svs ~f:(fun svar ->
        (*print_endline @@ sprintf "adding svar %s" (Ident.name_of_svar svar);*)
        (svar, if bv_mode then T_bv.SBV default_size else T_int.SInt))
  in
  let map =
    Map.force_merge (Map.Poly.map map ~f:(Term.subst_sorts_sort map')) map'
  in
  let types =
    (*List.map ~f:(fun (x, s) -> (x, Term.subst_sorts_sort map s))*) types
  in
  let senv = Map.Poly.map senv ~f:(Term.subst_sorts_sort map) in
  if false then
    print_endline
    @@ sprintf "senv: %s"
         (String.concat_map_list ~sep:", "
            ~f:(fun (x, s) ->
              sprintf "%s: %s" (Ident.name_of_tvar x) (Term.str_of_sort s))
            (Map.to_alist senv));
  let trans = List.map trans ~f:(subst_sorts_trans senv map) in
  (s, types, e, c, trans)

let rec is_effect_free = function
  | Skip | Assume _ -> true
  | Subst ((_, _), t) ->
      Set.for_all (Term.tvs_of t) ~f:(fun x ->
          not @@ String.is_prefix (Ident.name_of_tvar x) ~prefix:nondet_prefix)
  | Seq (c1, c2) | Choice (c1, c2) -> is_effect_free c1 && is_effect_free c2

let qelim_records = Hashtbl.Poly.create ()
let clean () = Hashtbl.Poly.clear qelim_records

let qelim phi =
  match Hashtbl.Poly.find qelim_records phi with
  | Some rcd -> rcd
  | None ->
      let ret =
        Z3Smt.Z3interface.qelim ~id:None ~fenv:(LogicOld.get_fenv ()) phi
      in
      Hashtbl.Poly.set qelim_records ~key:phi ~data:ret;
      ret

let bind_nondet nondet_senv phi =
  let nondet_senv =
    let tvs = Formula.tvs_of phi in
    List.filter nondet_senv ~f:(fst >> Set.mem tvs)
  in
  let range =
    List.filter_map nondet_senv ~f:(fun (x, s) ->
        match (String.split ~on:'_' (Ident.name_of_tvar x), s) with
        | [ _; bits; signed ], T_int.SInt ->
            let bits = int_of_string bits in
            let is_signed = String.(signed = "s") in
            Some
              (Formula.and_of
              @@ Formula.mk_range (Term.mk_var x s) (min_num bits is_signed)
                   (max_num bits is_signed))
        | _ (*ToDo*) -> None)
  in
  Formula.mk_forall_if_bounded nondet_senv
  @@
  if List.is_empty range then phi
  else Formula.mk_imply (Formula.and_of range) phi

let rec wp c phi =
  if print_log then
    print_endline
    @@ sprintf "command:\n%spost: %s\n" (str_of_command c) (Formula.str_of phi);
  let phi =
    match c with
    | Skip -> phi
    | Assume phi' -> Formula.mk_imply phi' phi
    | Subst ((x, _s), t) ->
        (if false then Evaluator.simplify_keep_imply else Fn.id)
        @@ Formula.apply_pred (x, phi) t
    | Seq (c1, c2) -> wp c1 (wp c2 phi)
    | Choice (c1, c2) ->
        Set.union
          (Formula.implies_of (wp c1 phi))
          (Formula.implies_of (wp c2 phi))
        |> Set.fold ~init:Map.Poly.empty ~f:(fun map (lhss, rhs) ->
            let lhs = Evaluator.simplify_and lhss in
            Map.Poly.update map rhs ~f:(function
              | None -> Set.Poly.singleton lhs
              | Some lhss -> Set.add lhss lhs))
        |> Map.Poly.map ~f:(Set.to_list >> Formula.or_of)
        |> Map.Poly.to_alist
        |> List.filter_map ~f:(fun (rhs, lhs) ->
            if Formula.is_false lhs || Formula.is_true rhs then None
            else if Formula.is_true lhs then Some rhs
            else Some (Formula.mk_imply lhs rhs))
        |> Formula.and_of
  in
  if print_log then
    print_endline @@ sprintf "wp: %s" (LogicOld.Formula.str_of phi);
  let nondet_senv =
    Set.filter
      (Formula.term_sort_env_of phi)
      ~f:(fst >> Ident.name_of_tvar >> String.is_prefix ~prefix:nondet_prefix)
  in
  if Set.is_empty nondet_senv then phi
  else
    let res =
      let nondet_senv_int =
        Set.filter nondet_senv ~f:(snd >> LogicOld.Term.is_int_sort)
      in
      if Set.is_empty nondet_senv_int then phi
      else (
        clean ();
        Formula.and_of @@ Set.to_list
        @@ Set.Poly.filter_map ~f:(fun (lhss, rhs) ->
            if Formula.is_true rhs then None
            else if Set.is_empty lhss then Some rhs
            else
              let lhs =
                (if true then Set.to_list >> Formula.and_of
                 else Evaluator.simplify_and)
                  lhss
              in
              if Formula.is_false lhs then None
              else
                let nondet_senv_int_lhs =
                  let tvs = Formula.tvs_of rhs in
                  Set.filter nondet_senv_int ~f:(fst >> Set.mem tvs >> not)
                in
                let lhs =
                  qelim
                  @@ Formula.mk_exists_if_bounded
                       (Set.to_list nondet_senv_int_lhs)
                       lhs
                in
                if Formula.is_false lhs then None
                else if Formula.is_true lhs then Some rhs
                else Some (Formula.mk_imply lhs rhs))
        @@ Formula.implies_of phi)
    in
    if print_log then
      print_endline @@ sprintf "simplified wp: %s" (LogicOld.Formula.str_of res);
    bind_nondet (Set.to_list nondet_senv) res

let used_vars c =
  let rec aux env = function
    | Skip -> env
    | Assume phi ->
        let env' =
          Set.filter
            (Formula.term_sort_env_of phi)
            ~f:
              (fst >> Ident.name_of_tvar
              >> String.is_prefix ~prefix:nondet_prefix
              >> not)
        in
        Set.union env' env
    | Subst ((x, _), t) ->
        let env' =
          Set.filter (Term.term_sort_env_of t)
            ~f:
              (fst >> Ident.name_of_tvar
              >> String.is_prefix ~prefix:nondet_prefix
              >> not)
        in
        Set.union env' (Set.filter env ~f:(fun (y, _) -> Stdlib.(x <> y)))
    | Seq (c1, c2) -> aux (aux env c2) c1
    | Choice (c1, c2) -> Set.union (aux env c1) (aux env c2)
  in
  aux Set.Poly.empty c

let defined_vars c =
  let rec aux env = function
    | Skip -> env
    | Assume _ -> env
    | Subst ((x, _), _) -> Set.add env x
    | Seq (c1, c2) -> aux (aux env c2) c1
    | Choice (c1, c2) -> Set.inter (aux env c1) (aux env c2)
  in
  aux Set.Poly.empty c

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

module G = Imperative.Digraph.ConcreteBidirectionalLabeled (V) (E)
module DFS = Traverse.Dfs (G)

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
  G.fold_edges_e (fun tr trans -> tr :: trans) cfa []

exception Found_Edges of G.edge list

let contract_edges ~print cfa =
  try
    G.iter_edges
      (fun s d ->
        let edges = G.find_all_edges cfa s d in
        if List.length edges > 1 then raise (Found_Edges edges) else ())
      cfa;
    false
  with
  | Found_Edges [] -> assert false
  | Found_Edges ((s, _, d) :: _ as es) ->
      print @@ lazy (sprintf "eliminating edge (%s, %s)" s d);
      let c = choice @@ List.map es ~f:snd3 in
      G.remove_edge cfa s d;
      G.add_edge_e cfa (s, c, d);
      true

exception Found_Vertex_1_1 of G.edge * G.vertex * G.edge

let contract_vertex_1_1 ~print s cfa =
  try
    G.iter_vertex
      (fun v ->
        if
          String.(s = v)
          (* ignore start node *)
          || Fn.non List.is_empty
             @@ G.find_all_edges cfa v v (* ignore vertex with a self-loop *)
        then ()
        else
          match (G.pred_e cfa v, G.succ_e cfa v) with
          | [ e1 ], [ e2 ] -> raise (Found_Vertex_1_1 (e1, v, e2))
          | _ -> ())
      cfa;
    false
  with Found_Vertex_1_1 ((s, c1, _d), v, (_s, c2, d)) ->
    print @@ lazy (sprintf "eliminating vertex %s" v);
    G.remove_vertex cfa v;
    G.add_edge_e cfa (s, seq [ c1; c2 ], d);
    true

exception Found_Vertex_1_n of G.edge * G.vertex * G.edge list

let contract_vertex_1_n ~print s cfa =
  try
    G.iter_vertex
      (fun v ->
        if
          String.(s = v)
          (* ignore start node *)
          || Fn.non List.is_empty
             @@ G.find_all_edges cfa v v (* ignore vertex with a self-loop *)
        then ()
        else
          match (G.pred_e cfa v, G.succ_e cfa v) with
          | [ ((_, c, _) as e) ], es when is_effect_free c ->
              raise (Found_Vertex_1_n (e, v, es))
          | _ -> ())
      cfa;
    false
  with Found_Vertex_1_n ((s, c1, _d), v, es) ->
    print @@ lazy (sprintf "eliminating vertex %s" v);
    G.remove_vertex cfa v;
    List.iter es ~f:(fun (_s, c2, d) -> G.add_edge_e cfa (s, seq [ c1; c2 ], d));
    true

exception Found_Vertex_n_1 of G.edge list * G.vertex * G.edge

let contract_vertex_n_1 ~print s cfa =
  try
    G.iter_vertex
      (fun v ->
        if
          String.(s = v)
          (* ignore start node *)
          || Fn.non List.is_empty
             @@ G.find_all_edges cfa v v (*ignore vertex with a self-loop*)
        then ()
        else
          match (G.pred_e cfa v, G.succ_e cfa v) with
          | es, [ ((_, c, _) as e) ] when is_effect_free c ->
              raise (Found_Vertex_n_1 (es, v, e))
          | _ -> ())
      cfa;
    false
  with Found_Vertex_n_1 (es, v, (_s, c2, d)) ->
    print @@ lazy (sprintf "eliminating vertex %s" v);
    G.remove_vertex cfa v;
    List.iter es ~f:(fun (s, c1, _d) -> G.add_edge_e cfa (s, seq [ c1; c2 ], d));
    true

let rec simplify ~print s cfa =
  if
    contract_edges ~print cfa
    || contract_vertex_1_1 ~print s cfa
    || contract_vertex_1_n ~print s cfa
    || contract_vertex_n_1 ~print s cfa
  then simplify ~print s cfa
  else cfa

module LiveVariables =
  Graph.Fixpoint.Make
    (G)
    (struct
      type vertex = G.E.vertex
      type edge = G.E.t
      type g = G.t
      type data = sort_env_set

      let direction = Graph.Fixpoint.Backward
      let equal = Set.equal
      let join = Set.union

      let analyze (_, c, _) env =
        let def = defined_vars c in
        let use = used_vars c in
        Set.union use (Set.filter env ~f:(fst >> Set.mem def >> not))
    end)

let rec cut_points_of g res =
  if DFS.has_cycle g then (
    let vertices_self_loop =
      G.fold_vertex
        (fun s vs -> if G.mem_edge g s s then Set.add vs s else vs)
        g Set.Poly.empty
    in
    Set.iter vertices_self_loop ~f:(G.remove_vertex g);
    let res = Set.union res vertices_self_loop in
    let vertices_deg_leq_1 =
      G.fold_vertex
        (fun s vs ->
          if G.in_degree g s + G.out_degree g s <= 1 then Set.add vs s else vs)
        g Set.Poly.empty
    in
    Set.iter vertices_deg_leq_1 ~f:(G.remove_vertex g);
    let vertices_indeg1_outdeg1 =
      G.fold_vertex
        (fun s vs ->
          match (G.pred g s, G.succ g s) with
          | [ pred ], [ succ ] (*when String.(pred <> s && succ <> s)*) ->
              Set.add vs (pred, s, succ)
          | _ -> vs)
        g Set.Poly.empty
    in
    Set.iter vertices_indeg1_outdeg1 ~f:(fun (pred, s, succ) ->
        if not @@ G.mem_edge g pred succ then G.add_edge g pred succ;
        G.remove_vertex g s);
    if
      Set.is_empty vertices_self_loop
      && Set.is_empty vertices_deg_leq_1
      && Set.is_empty vertices_indeg1_outdeg1
    then (
      let _, v =
        G.fold_vertex
          (fun s (deg0, s0) ->
            let deg = G.in_degree g s + G.out_degree g s in
            if deg > deg0 then (deg, s) else (deg0, s0))
          g (-1, "")
      in
      G.remove_vertex g v;
      cut_points_of g @@ Set.add res v)
    else cut_points_of g res)
  else res

let analyze ~print ((s, types, e, c, trans) as lts) =
  print @@ lazy "************* simplifying LTS ***************";
  print @@ lazy (sprintf "input LTS:\n%s" @@ str_of_lts lts);
  match s with
  | None -> ((fun _ -> Set.Poly.empty), Set.Poly.empty, (s, types, e, c, trans))
  | Some s ->
      let cfa = simplify ~print s (graph_of trans) in
      let live_vars = LiveVariables.analyze (fun _ -> Set.Poly.empty) cfa in
      let cut_points = cut_points_of (G.copy cfa) Set.Poly.empty in
      let lts' = (Some s, types, e, c, of_graph cfa) in
      print @@ lazy (sprintf "simplified LTS:\n%s" @@ str_of_lts lts');
      print
      @@ lazy
           (sprintf "cut points: %s" @@ String.concat_set ~sep:", " cut_points);
      (live_vars, cut_points, lts')
