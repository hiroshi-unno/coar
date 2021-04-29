open Core
open Common
open Common.Util
open Ast
open Ast.LogicOld
open PCSatCommon

module Config = struct
  type t = {
    verbose: bool;
    lex_deg: int; (* Degree of lexicographic ranking function >= 0 *)
    qualifier: string; (* Type of qualifiers (for eager halfspace generation): interval | octagon *)
    approx_level : int; (* Approximation level of hyperplanes obtained from svm. If approx_level > 0, then use truncated continued fractions with length at most approx_level. If approx_level = 0, then the length of truncated continued fractions is chosen automatically. *)
    csvm : float; (* c parameter for csvm *)
    eager_halfspace_gen : bool; (* Eager halfspace generation. Note that the combination of nonneg = true & eager_halfspace_gen = false is not supported. *)
    optimize_sum_coeff : bool;
    qualifier_reduction : bool
  } [@@deriving yojson]

  module type ConfigType = sig val config: t end

  let instantiate_ext_files cfg = Ok cfg
end

module Make (Cfg: Config.ConfigType) (PCSP: PCSP.Problem.ProblemType) = struct
  let config = Cfg.config

  module Debug = Debug.Make (val Debug.Config.(if config.verbose then enable else disable))

  type classifier = SortMap.t * (Ident.pvar * (SortEnv.t * Formula.t))

  type halfspace_ineq = Ge0 | Gt0 | Le0 | Lt0

  let halfspace_ineq_neg =
    function
    | Ge0 -> Lt0
    | Gt0 -> Le0
    | Le0 -> Gt0
    | Lt0 -> Ge0

  type halfspace = (Ident.tvar * Sort.t, Term.t) Map.Poly.t * Term.t * halfspace_ineq

  let halfspace_neg (maps, t, ineq) = (maps, t, halfspace_ineq_neg ineq)

  let atom_of_halfspace (maps, t, ineq) =
    let t = Map.Poly.fold maps ~init:t ~f:(fun ~key:(tvar, sort) ~data:c t -> T_int.mk_add t (T_int.mk_mult c (Term.mk_var tvar sort))) in
    match ineq with
    | Ge0 -> T_int.mk_geq t (T_int.zero ())
    | Gt0 -> T_int.mk_gt t (T_int.zero ())
    | Le0 -> T_int.mk_leq t (T_int.zero ())
    | Lt0 -> T_int.mk_lt t (T_int.zero ())

  let term_of_halfspace h = T_bool.of_atom (atom_of_halfspace h)
  let formula_of_halfspace h = Formula.mk_atom (atom_of_halfspace h)

  let eval_halfspace params_x_tvar x h =
    let map = List.zip_exn params_x_tvar x |> Map.Poly.of_alist_exn in
    Formula.subst map (formula_of_halfspace h) |> Evaluator.eval

  module Table = struct
    type t =
      | Eager of bool array array * halfspace array * SortEnv.t * (Term.t list * Term.t list) array
      | Lazy of (int, bool array) Hashtbl.t * (int, halfspace) Hashtbl.t * int ref * SortEnv.t * (Term.t list * Term.t list) array
    type halfspace = In of int | Notin of int
    let get_halfspace = function
      | Eager (_, hs, _, _) ->
        (function
          | In i -> hs.(i)
          | Notin i -> halfspace_neg hs.(i))
      | Lazy (_, hs, _, _, _) ->
        (function
          | In i -> Option.value_exn (Hashtbl.find hs i)
          | Notin i -> Option.value_exn (Hashtbl.find hs i) |> halfspace_neg)
    let halfspace_neg =
      function
      | In id -> Notin id
      | Notin id -> In id
    let make_eager hs params_x ex_list : t =
      let params_x_tvar = SortEnv.args_of params_x in
      Debug.print @@ lazy (Printf.sprintf "number of input qualifiers: %d" (List.length hs));
      if config.qualifier_reduction then
        let choose_best_hs l =
          let abs_sum_of_coeff (maps, t, _) =
            List.map ~f:(fun tm -> match Evaluator.eval_term tm with Value.Int n -> Z.abs n | _ -> assert false) (t :: Map.Poly.data maps)
            |> List.fold ~init:Z.zero ~f:(fun x y -> Z.(x + y)) in
          match List.map ~f:(fun h -> (h, abs_sum_of_coeff h)) l
                |> List.min_elt ~compare:(fun (_, x) (_, y) -> Z.compare x y) with
          | None -> assert false
          | Some (h, _) -> h in
        let rec make_table = function
          | [] -> fun _ -> []
          | hs -> function
            | [] -> [choose_best_hs hs, []]
            | ex::l ->
              let hs_t, hs_f = List.partition_tf hs ~f:(eval_halfspace params_x_tvar ex) in
              let table_t = make_table hs_t l in
              let table_f = make_table hs_f l in
              List.map ~f:(fun (h, t) -> (h, true::t)) table_t @ List.map ~f:(fun (h, t) -> (h, false::t)) table_f in
        let hs, table = make_table hs (List.fold_right ex_list ~f:(fun (x, y) l -> x::y::l) ~init:[]) |> List.unzip in
        let table = List.map ~f:Array.of_list table |> Array.of_list in
        let hs = Array.of_list hs in
        let ex = Array.of_list ex_list in
        Debug.print @@ lazy (Printf.sprintf "number of reduced qualifiers: %d" (Array.length hs));
        Eager (table, hs, params_x, ex)
      else
        let table = Array.make_matrix ~dimx:(List.length hs) ~dimy:(2 * List.length ex_list) true in
        let hs = Array.of_list hs in
        let ex = Array.of_list ex_list in
        Array.iteri hs ~f:(fun i h -> Array.iteri ex ~f:(fun j (x, y) ->
            table.(i).(2*j) <- eval_halfspace params_x_tvar x h;
            table.(i).(2*j+1) <- eval_halfspace params_x_tvar y h));
        Eager (table, hs, params_x, ex)
    let make_lazy params_x ex_list : t =
      let table = Hashtbl.create (module Int) in
      let hs = Hashtbl.create (module Int) in
      let ex = Array.of_list ex_list in
      Lazy (table, hs, ref 0, params_x, ex)
    let add_hs t h =
      match t with
      | Eager _ -> failwith "adding qualifiers is not allowed in eager mode"
      | Lazy (table, hs, r, params_x, ex) ->
        let h_id = !r in
        let params_x_tvar = SortEnv.args_of params_x in
        let a = Array.init (2 * Array.length ex) ~f:(fun i ->
            let (x, y) = ex.(i/2) in
            let x = if i % 2 = 0 then x else y in
            eval_halfspace params_x_tvar x h) in
        Hashtbl.add_exn table ~key:h_id ~data:a;
        Hashtbl.add_exn hs ~key:h_id ~data:h;
        r := h_id + 1;
        In h_id
    let get_hs_size = function
      | Eager (_, hs, _, _) -> Array.length hs
      | Lazy (_, hs, _, _, _) -> Hashtbl.length hs
    let get_ex = function
      | Eager (_, _, _, ex) -> ex
      | Lazy (_, _, _, _, ex) -> ex
    let get_ex_id_list t =
      let len = get_ex t |> Array.length in
      List.init len ~f:(fun i -> (2*i, 2*i+1))
    let get_hs_id_list t =
      let len = get_hs_size t in
      List.init len ~f:(fun i -> In i)
    let eval_halfspace t x_id =
      match t with
      | Eager (table, _, _, _) ->
        (function
          | In h_id -> table.(h_id).(x_id)
          | Notin h_id -> not table.(h_id).(x_id))
      | Lazy (table, _, _, _, _) ->
        (function
          | In h_id -> (Option.value_exn (Hashtbl.find table h_id)).(x_id)
          | Notin h_id -> (Option.value_exn (Hashtbl.find table h_id)).(x_id) |> not)
    let get_x t i =
      let ex = get_ex t in
      let (x, y) = ex.(i/2) in
      if i % 2 = 0 then x else y
    let get_params_x = function
      | Eager (_, _, params_x, _) -> params_x
      | Lazy (_, _, _, params_x, _) -> params_x
    let get_x_map t i =
      let params_x_tvar = SortEnv.args_of @@ get_params_x t in
      List.zip_exn params_x_tvar (get_x t i) |> Map.Poly.of_alist_exn
  end

  type 'a dtree = Leaf of 'a | Node of Table.halfspace * 'a dtree * 'a dtree

  let rec dtree_fmap f =
    function
    | Leaf x -> Leaf (f x)
    | Node (h, tt, ft) -> Node (h, dtree_fmap f tt, dtree_fmap f ft)

  module Lexicographic = struct
    type t = Term.t list
    let gt x y =
      let rec gt' eq =
        function
        | [] -> []
        | (x, y)::xys ->
          let x_gt_y = Formula.mk_and (Formula.mk_atom (T_int.mk_geq x (T_int.zero ()))) (Formula.mk_atom (T_int.mk_gt x y)) in
          let x_eq_y = Formula.mk_atom (T_bool.mk_eq x y) in
          let xy_neg = Formula.mk_and (Formula.mk_atom (T_int.mk_lt x (T_int.zero ()))) (Formula.mk_atom (T_int.mk_lt y (T_int.zero ()))) in
          let x_eq_y = Formula.mk_or x_eq_y xy_neg in
          (Formula.and_of (x_gt_y::eq))::gt' (x_eq_y::eq) xys in
      Formula.or_of (gt' [] (List.zip_exn x y))
    let gt2 x y =
      let rec gt2' eq =
        function
        | [] -> []
        | (x, y)::xys ->
          let x_gt_y = Formula.mk_and (Formula.mk_atom (T_int.mk_geq x (T_int.zero ()))) (Formula.mk_atom (T_int.mk_gt x y)) in
          let x_eq_y = Formula.mk_atom (T_bool.mk_eq x y) in
          (Formula.and_of (x_gt_y::eq))::gt2' (x_eq_y::eq) xys in
      Formula.or_of (gt2' [] (List.zip_exn x y))
  end

  module Template = struct
  (*
  Make an affine template, no constraint and a list of parameters.
  *)
    let gen_template_simple params_x =
      let p = Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt in
      let template, params = List.fold (SortEnv.list_of params_x) ~init:(p, [p]) ~f:(fun (template, params) (tvar, sort) ->
          let p = Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt in
          (T_int.mk_add template (T_int.mk_mult p (Term.mk_var tvar sort))), p::params) in
      (template, params)

    let gen_template_lexicographic t =
      let gather = List.fold_right ~init:([], []) ~f:(fun (t, p) (ts, p') -> (t::ts, p @ p')) in
      let params_x = Table.get_params_x t in
      List.init (config.lex_deg + 1) ~f:(fun _ -> gen_template_simple params_x) |> gather
  end

  let rec term_of_dtree t =
    function
    | Leaf term -> term
    | Node (h, tt, ft) -> List.zip_exn (term_of_dtree t tt) (term_of_dtree t ft) |> List.map ~f:(fun (x,y) -> T_bool.mk_if_then_else (Table.get_halfspace t h |> term_of_halfspace) x y)
(*
  let gen_halfspaces params_x ex =
    Set.Poly.to_list ex
      |> List.map ~f:(fun (x, y) -> [x; y])
      |> List.concat
      |> List.map ~f:(fun x -> List.zip_exn params_x x)
      |> List.concat
      |> List.map ~f:(fun ((tvar, sort), x) ->
          [T_int.mk_geq (Term.mk_var tvar sort) x;
            T_int.mk_leq (Term.mk_var tvar sort) x])
      |> List.concat
*)
  let collect_xy ex =
    Set.Poly.to_list ex
    |> List.map ~f:(fun (x, y) -> [x; y])
    |> List.concat
    |> Set.Poly.of_list

  let approximate_hyperplane t ex w b =
    let wb_to_int w b =
      let lcm_den = Map.Poly.fold w ~init:(Q.den b) ~f:(fun ~key:_ ~data:q a -> Z.lcm a (Q.den q)) in
      let mul_lcm_den x = Q.(x * Q.of_bigint lcm_den) |> Q.num in
      let b' = mul_lcm_den b in
      let w' = Map.Poly.map ~f:mul_lcm_den w in
      w', b' in
    let make_halfspace w b = (Map.Poly.map ~f:T_int.mk_int w, T_int.mk_int b, Ge0) in
    let eval_halfspace h x =
      let params_x_tvar = SortEnv.args_of @@ Table.get_params_x t in
      eval_halfspace params_x_tvar x h in
    let exact_w = Map.Poly.map ~f:Q.of_float w in
    let exact_b = Q.of_float b in
    let exact_w, exact_b = wb_to_int exact_w exact_b in
    let exact_bw = exact_b :: SortEnv.map (Table.get_params_x t) ~f:(fun key -> Map.Poly.find_exn exact_w key) in
    let abs_exact_bw = List.map ~f:Z.abs exact_bw in
    let sorted_abs_exact_bw = List.sort ~compare:Z.compare abs_exact_bw in
    let all_examples = List.map ex ~f:(fun (x, y) -> [x; y]) |> List.concat |> Set.Poly.of_list |> Set.Poly.map ~f:(Table.get_x t) in
    if config.approx_level > 0 then
      let abs_approx_bw = ContFrac.approximate_ratio abs_exact_bw config.approx_level in
      let approx_bw = List.zip_exn abs_approx_bw exact_bw |> List.map ~f:(fun (a, s) -> if Z.Compare.(s < Z.zero) then Z.(~-a) else a) in
      let w' = (List.zip_exn (SortEnv.list_of @@ Table.get_params_x t) (List.tl_exn approx_bw) |> Map.Poly.of_alist_exn) in
      let b' = List.hd_exn approx_bw in
      make_halfspace w' b'
    else
      let exact_halfspace = make_halfspace exact_w exact_b in
      let len_params = SortEnv.length (Table.get_params_x t) in
      let rec loop level cut =
        let lb = List.nth_exn sorted_abs_exact_bw cut in
        let abs_exact_bw' = List.map ~f:(fun n -> if Z.Compare.(n >= lb) then n else Z.zero) abs_exact_bw in
        let abs_approx_bw' = ContFrac.approximate_ratio abs_exact_bw' level in
        let approx_bw' = List.zip_exn abs_approx_bw' exact_bw |> List.map ~f:(fun (a, s) -> if Z.Compare.(s < Z.zero) then Z.(~-a) else a) in
        let w' = (List.zip_exn (SortEnv.list_of @@ Table.get_params_x t) (List.tl_exn approx_bw') |> Map.Poly.of_alist_exn) in
        let b' = List.hd_exn approx_bw' in
        let h = make_halfspace w' b' in
        if Set.Poly.for_all all_examples ~f:(fun ex -> Bool.(eval_halfspace h ex = eval_halfspace exact_halfspace ex)) then
          h
        else
        if cut <= 0 then
          loop (level + 1) len_params
        else
          loop level (cut - 1) in
      loop 1 len_params

  let int_term_compare t1 t2 =
    let force_int tm = match Evaluator.eval_term tm with Value.Int n -> n | _ -> assert false in
    Z.compare (force_int t1) (force_int t2)

  let gen_halfspaces_interval params_x ex_xy =
    let params_x = SortEnv.list_of params_x in
    Set.Poly.to_list ex_xy
    |> List.map ~f:(fun x -> List.zip_exn params_x x)
    |> List.concat
    |> List.dedup_and_sort ~compare:(Comparable.lexicographic [
        (fun ((tv1, _), _) ((tv2, _), _) -> Ident.tvar_compare tv1 tv2) (* ignore sort *);
        (fun (_, t1) (_, t2) -> int_term_compare t1 t2)
      ])
    |> List.map ~f:(fun (v, t) ->
        let map = Map.Poly.singleton v (T_int.one ()) in
        let neg_t = T_int.mk_neg t in
        [(map, neg_t, Ge0); (map, neg_t, Le0)])
    |> List.concat

  let rec make_all_pairs =
    function
    | [] -> []
    | x::l -> List.map ~f:(fun y -> (x, y)) l @ make_all_pairs l

  let gen_halfspaces_octagon params_x ex_xy =
    let params_x = SortEnv.list_of params_x in
    Set.Poly.to_list ex_xy
    |> List.map ~f:(fun x -> List.zip_exn params_x x)
    |> List.map ~f:make_all_pairs
    |> List.concat
    |> List.map ~f:(fun ((p1, x1), (p2, x2)) ->
        let one = T_int.one () in
        let neg_one = T_int.from_int (-1) in
        let force_int tm = match Evaluator.eval_term tm with Value.Int n -> n | _ -> assert false in
        let x1 = force_int x1 in
        let x2 = force_int x2 in
        [((p1, one), (p2, one), T_int.mk_int Z.(~-x1 - x2));
         ((p1, one), (p2, neg_one), T_int.mk_int Z.(~-x1 + x2));
         ((p1, neg_one), (p2, one), T_int.mk_int Z.(x1 - x2));
         ((p1, neg_one), (p2, neg_one), T_int.mk_int Z.(x1 + x2))])
    |> List.concat
    |> List.dedup_and_sort ~compare:(Comparable.lexicographic [
        (fun (((tv1, _), _), _, _) (((tv2, _), _), _, _)  -> Ident.tvar_compare tv1 tv2);
        (fun (_, ((tv1, _), _), _) (_, ((tv2, _), _), _)  -> Ident.tvar_compare tv1 tv2);
        (fun ((_, t1), _, _) ((_, t2), _, _)  -> int_term_compare t1 t2);
        (fun (_, (_, t1), _) (_, (_, t2), _)  -> int_term_compare t1 t2);
        (fun ((_, _), _, t1) ((_, _), _, t2)  -> int_term_compare t1 t2)
      ])
    |> List.map ~f:(fun (p1, p2, c) -> (Map.Poly.of_alist_exn [p1; p2], c, Ge0))

  let gen_halfspaces params_x ex_xy =
    if Stdlib.(=) config.qualifier "interval" then
      gen_halfspaces_interval params_x ex_xy
    else if Stdlib.(=) config.qualifier "octagon" then
      gen_halfspaces_interval params_x ex_xy @ gen_halfspaces_octagon params_x ex_xy
    else (* default *)
      gen_halfspaces_interval params_x ex_xy @ gen_halfspaces_octagon params_x ex_xy

  let rec split_examples t h =
    function
    | [] -> ([], [], [], [])
    | (x, y)::ex ->
      let (tt, tf, ft, ff) = split_examples t h ex in
      match Table.eval_halfspace t x h, Table.eval_halfspace t y h with
      | true, true -> ((x, y)::tt, tf, ft, ff)
      | true, false -> (tt, (x, y)::tf, ft, ff)
      | false, true -> (tt, tf, (x, y)::ft, ff)
      | false, false -> (tt, tf, ft, (x, y)::ff)

  let mk_map params_x_tvar x = List.zip_exn params_x_tvar x |> Map.Poly.of_alist_exn

  let max_sat_template lex2wf t ex =
    let template_terms, _ = Template.gen_template_lexicographic t in
    let params_x_tvar = SortEnv.args_of @@ Table.get_params_x t in
    let fenv = Set.Poly.empty in (*TODO: generate fenv*)
    let t_x_gt_t_y = List.map ~f:(fun (x, y) -> 
        let t_x = List.map ~f:(Term.subst (mk_map params_x_tvar (Table.get_x t x))) template_terms in
        let t_y = List.map ~f:(Term.subst (mk_map params_x_tvar (Table.get_x t y))) template_terms in
        lex2wf t_x t_y) ex in
    let soft_constraints = Map.Poly.singleton "txgtty" (List.map ~f:(fun x -> (x, 1)) t_x_gt_t_y) in
    match Z3Smt.Z3interface.max_smt fenv [] soft_constraints with
    | Some(num_sat, _) ->
      num_sat
    | None -> assert false

  module BuildDT = struct
    (* evaluate each soft constraint by the model returned by Z3interface.max_smt
     * almost the same as max_sat_template*)
    let assign_label t ex =
      let open Lacaml.D in
      let template_terms, _ = Template.gen_template_lexicographic t in
      let params_x_tvar = SortEnv.args_of @@ Table.get_params_x t in
      let fenv = Set.Poly.empty in (*TODO: generate fenv*)
      let t_x_gt_t_y = List.map ~f:(fun (x, y) -> 
          let t_x = List.map ~f:(Term.subst (mk_map params_x_tvar (Table.get_x t x))) template_terms in
          let t_y = List.map ~f:(Term.subst (mk_map params_x_tvar (Table.get_x t y))) template_terms in
          Lexicographic.gt t_x t_y) ex in
      let soft_constraints = Map.Poly.singleton "txgtty" (List.map ~f:(fun x -> (x, 1)) t_x_gt_t_y) in
      match Z3Smt.Z3interface.max_smt fenv [] soft_constraints with
      | Some(_, model) ->
        let model = LogicOld.remove_dontcare model |> Map.Poly.of_alist_exn in
        let labels = List.map ~f:(fun c -> if Formula.subst model c |> Evaluator.eval then 1. else -1.) t_x_gt_t_y in
        let x_label, y_label = List.zip_exn ex labels
                               |> List.map ~f:(fun ((x_id, y_id), label) -> (x_id, label), (y_id, label))
                               |> List.unzip in
        let xy_label = List.map ~f:(fun (x, label) -> (Table.get_x t x |> List.map ~f:(fun xi -> T_int.let_int xi |> Z.to_float), label)) (x_label @ y_label) in
        let compare (x, l) (x', l') =
          let x_comp = List.compare Float.compare x x' in
          if x_comp = 0 then
            Float.compare l l'
          else
            x_comp in
        (*            List.iter ~f:(fun (x, label) -> Debug.print @@ lazy (
                        let x_str = List.map ~f:string_of_float x |> String.concat ~sep:", " in
                        let label_str = string_of_float label in
                        Printf.sprintf "(%s): %s" x_str label_str
                      )) xy_label;*)
        let xy_label = List.dedup_and_sort ~compare xy_label in
        (*            (* assuming only two labels 1/-1 *)
                      let rec remove_contradiction_sorted = function
                      | [] -> []
                      | x::l -> remove_contradiction_sorted' x l
                      and remove_contradiction_sorted' (key, value) = function
                      | [] -> [(key, value)]
                      | (key', value')::l' ->
                          if key = key' then
                            if value <> value' then
                              remove_contradiction_sorted l'
                            else
                              (key, value) :: remove_contradiction_sorted l'
                          else
                            (key, value) :: remove_contradiction_sorted' (key', value') l' in
                      let xy_label = remove_contradiction_sorted xy_label in
                      Debug.print @@ lazy "after removing duplication";*)
        List.iter ~f:(fun (x, label) -> Debug.print @@ lazy (
            let x_str = List.map ~f:string_of_float x |> String.concat ~sep:", " in
            let label_str = string_of_float label in
            Printf.sprintf "(%s): %s" x_str label_str
          )) xy_label;
        let samples, labels = List.unzip xy_label in
        let labels = Array.of_list labels |> Vec.of_array in
        let samples = List.map ~f:Array.of_list samples |> Array.of_list |> Mat.of_array in
        (samples, labels)
      | None -> assert false

    let has_examples_in_both_side t h =
      function
      | [] -> false
      | x::ex -> List.exists ex ~f:(fun y -> Stdlib.(<>) (Table.eval_halfspace t x h) (Table.eval_halfspace t y h))

    let filter_hyperplanes t ex hs =
      List.filter hs ~f:(fun h -> has_examples_in_both_side t h ex)

    let choose_halfspace_eager lex2wf t ex_id_list h_id_list =
      let try_halfspace h_id =
        let (ex_tt, ex_tf, ex_ft, ex_ff) = split_examples t h_id ex_id_list in
        let progress = (List.length ex_id_list > List.length ex_tt) && (List.length ex_id_list > List.length ex_ff) in
        let t_max_sat = max_sat_template lex2wf t ex_tt in
        let f_max_sat = max_sat_template lex2wf t ex_ff in
        let plogp p = if Float.(p >. 0.) then p *. Common.Util.log2 p else 0. in
        let ent p n = (~-.(plogp (p /. (p +. n)) +. plogp (n /. (p +. n)))) in
        let gain =
          let ex_tt_p = float_of_int t_max_sat in
          let ex_ff_p = float_of_int f_max_sat in
          let ex_tf_p = float_of_int (List.length ex_tf) in
          let ex_tf_n = float_of_int (List.length ex_ft) in
          (ex_tt_p +. ex_ff_p) +. (ex_tf_p +. ex_tf_n) *. (1. -. ent ex_tf_p ex_tf_n) in
        (gain, progress, h_id, (ex_tt, t_max_sat), (ex_ff, f_max_sat)) in
      let (_, _, best_halfspace, (ex_tt, t_max_sat), (ex_ff, f_max_sat)) =
        List.map ~f:try_halfspace h_id_list
        |> List.filter ~f:(fun (_, p, _, _, _) -> p) (* making progress *)
        |> fun l -> (
          List.sort ~compare:(fun (g0, _, _, _, _) (g1, _, _, _, _) -> Stdlib.compare g0 g1) l
          |> List.iter ~f:(fun (g, _, h_id, _, _) ->
              Debug.print @@ lazy (
                let s = Table.get_halfspace t h_id |> formula_of_halfspace |> Evaluator.simplify |> Formula.str_of in
                s ^ ": gain = " ^ string_of_float g
              )
            );
          l)
          |> List.max_elt ~compare:(fun (g0, _, _, _, _) (g1, _, _, _, _) -> Stdlib.compare g0 g1) (* take a halfspace with maximum information gain *)
          |> function Some x -> x | None -> assert false in
      (best_halfspace, (ex_tt, t_max_sat), (ex_ff, f_max_sat))


    let choose_halfspace_lazy lex2wf t ex_id_list =
      let samples, labels = assign_label t ex_id_list in
      let params_x = Table.get_params_x t in
      let eval_hyperplane (w, b) sample = List.zip_exn (SortEnv.list_of params_x) (Array.to_list sample) |> List.fold ~init:b ~f:(fun a (x, b) -> a +. b *. Map.Poly.find_exn w x) in
      let is_useless_hyperplane (w, b) samples =
        let has_pos = Array.exists samples ~f:(fun sample -> Float.(eval_hyperplane (w, b) sample >=. 0.)) in
        let has_neg = Array.exists samples ~f:(fun sample -> Float.(eval_hyperplane (w, b) sample <. 0.)) in
        not (has_pos && has_neg) in
      let undersample samples labels =
        let samples = Lacaml.D.Mat.to_array samples in
        let labels = Lacaml.D.Vec.to_array labels in
        let pos_samples, neg_samples = Array.partitioni_tf samples ~f:(fun i _ -> Float.(labels.(i) >. 0.)) in
        let undersample_major major minor =
          let remove_index = match Array.findi major ~f:(fun _ sample -> Array.mem minor sample ~equal:(Array.equal Stdlib.(=))) with
            | Some (i, _) -> i
            | None -> 0 in
          Array.filteri major ~f:(fun i _ -> remove_index <> i) in
        let pos_samples, neg_samples =
          if Array.length pos_samples > Array.length neg_samples then
            let pos_samples = undersample_major pos_samples neg_samples in
            pos_samples, neg_samples
          else
            let neg_samples = undersample_major neg_samples pos_samples in
            pos_samples, neg_samples in
        let samples = Array.append pos_samples neg_samples in
        let labels = Array.init (Array.length samples) ~f:(fun i -> if i < Array.length pos_samples then 1. else -1.) in
        Lacaml.D.Mat.of_array samples, Lacaml.D.Vec.of_array labels in
      let rec get_useful_hyperplane samples labels =
        let n_pos = Lacaml.D.Vec.to_list labels |> List.count ~f:(fun x -> Float.(x > 0.)) in
        let n_neg = Lacaml.D.Vec.dim labels - n_pos in
        let weights = [(1, 1. /. float_of_int n_pos); (-1, 1. /. float_of_int n_neg)] in
        let w, b = if n_pos = 1 && n_neg = 1 then
            (Debug.print @@ lazy "2 samples";
             let samples = Lacaml.D.Mat.to_array samples in
             Array.iter ~f:(fun sample -> Debug.print @@ lazy (Array.map ~f:string_of_float sample |> Array.to_list |> String.concat ~sep:", ")) samples;
             let w = List.mapi ~f:(fun i x -> (x, samples.(1).(i) -. samples.(0).(i))) (SortEnv.list_of params_x) in
             let b = (Array.foldi ~init:0. ~f:(fun i sum a -> let b = samples.(1).(i) in sum +. a *. a -. b *. b) samples.(0)) /. 2. in
             Debug.print @@ lazy ("w = " ^ (List.map w ~f:(fun (_, a) -> string_of_float a) |> String.concat ~sep:", "));
             Debug.print @@ lazy ("b = " ^ string_of_float b);
             let eval_hyperplane sample = List.foldi ~init:b ~f:(fun i sum (_, a) -> sum +. a *. sample.(i)) w in
             Debug.print @@ lazy ("sample0 = " ^ (string_of_float @@ eval_hyperplane samples.(0)));
             Debug.print @@ lazy ("sample1 = " ^ (string_of_float @@ eval_hyperplane samples.(1)));
             Map.Poly.of_alist_exn w, b)
          else
            Qualifier.SVM.get_hyperplane_float config.csvm ~weights params_x samples labels in
        if is_useless_hyperplane (w, b) (Lacaml.D.Mat.to_array samples) then
          let samples, labels = undersample samples labels in
          get_useful_hyperplane samples labels
        else
          w, b in
      let w, b = get_useful_hyperplane samples labels in
      let hs = approximate_hyperplane t ex_id_list w b in
      let h_id = Table.add_hs t hs in
      let (ex_tt, _, _, ex_ff) = split_examples t h_id ex_id_list in
      let t_max_sat = max_sat_template lex2wf t ex_tt in
      let f_max_sat = max_sat_template lex2wf t ex_ff in
      (h_id, (ex_tt, t_max_sat), (ex_ff, f_max_sat))

    type build_dtree_info =
      | InfoEager of Table.halfspace list * int list
      | InfoLazy

    let choose_halfspace lex2wf t ex_id_list = function
      | InfoEager (h_id_list, _) -> choose_halfspace_eager lex2wf t ex_id_list h_id_list
      | InfoLazy -> choose_halfspace_lazy lex2wf t ex_id_list

    let update_info t new_halfspace = function
      | InfoEager (h_id_list, ex_xy_id_list) ->
        let t_ex_xy, f_ex_xy = List.partition_tf ex_xy_id_list ~f:(fun x -> Table.eval_halfspace t x new_halfspace) in
        let t_hs = filter_hyperplanes t t_ex_xy h_id_list in
        let f_hs = filter_hyperplanes t f_ex_xy h_id_list in
        (InfoEager (t_hs, t_ex_xy), InfoEager (f_hs, f_ex_xy))
      | InfoLazy -> (InfoLazy, InfoLazy)

    let rec build_dtree' lex2wf t ex_id_list ex_max_sat info =
      Debug.print @@ lazy (Printf.sprintf "ex_max_sat = %d" ex_max_sat);
      List.iter ~f:(fun (x, y) -> 
          let x_str = "(" ^ (Table.get_x t x |> List.map ~f:Term.str_of |> String.concat ~sep:", ") ^ ")" in
          let y_str = "(" ^ (Table.get_x t y |> List.map ~f:Term.str_of |> String.concat ~sep:", ") ^ ")" in
          Debug.print @@ lazy (x_str ^ " " ^ y_str)
        ) ex_id_list;
      if List.length ex_id_list = ex_max_sat then
        Leaf (Template.gen_template_lexicographic t)
      else
        let (best_halfspace, (ex_tt, t_max_sat), (ex_ff, f_max_sat)) = choose_halfspace lex2wf t ex_id_list info in
        Debug.print @@ lazy (Table.get_halfspace t best_halfspace |> formula_of_halfspace |> Evaluator.simplify |> Formula.str_of);
        let tinfo, finfo = update_info t best_halfspace info in
        let ttree = build_dtree' lex2wf t ex_tt t_max_sat tinfo in
        let ftree = build_dtree' lex2wf t ex_ff f_max_sat finfo in
        Node (best_halfspace, ttree, ftree)

    let build_dtree lex2wf t =
      let ex_id_list = Table.get_ex_id_list t in
      let ex_xy_id_list = ex_id_list |> List.map ~f:(fun (x, y) -> [x; y]) |> List.concat in
      let info = if config.eager_halfspace_gen then
          InfoEager (Table.get_hs_id_list t, ex_xy_id_list)
        else
          InfoLazy in
      let max_sat = max_sat_template lex2wf t ex_id_list in
      build_dtree' lex2wf t ex_id_list max_sat info
  end

  let choose_separating_halfspace_eager t x y ex_in_poly =
    let cross_hyperplane_t_f h x y = (Table.eval_halfspace t x h) && not (Table.eval_halfspace t y h) in
    let hs_xt_yf = List.filter ~f:(fun h -> cross_hyperplane_t_f h x y) (Table.get_hs_id_list t) in
    let count_xt_yf h = List.count ~f:(fun (x, y) -> cross_hyperplane_t_f h x y) ex_in_poly in
    let hs_xt_yf = List.map ~f:(fun h -> (count_xt_yf h, h)) hs_xt_yf in
    let hs_xf_yt = List.filter ~f:(fun h -> cross_hyperplane_t_f h y x) (Table.get_hs_id_list t) in
    let count_xf_yt h = List.count ~f:(fun (x, y) -> cross_hyperplane_t_f h y x) ex_in_poly in
    let hs_xf_yt = List.map ~f:(fun h -> (count_xf_yt h, h)) hs_xf_yt in
    List.min_elt ~compare:(fun (c0, _) (c1, _) -> compare c0 c1) (hs_xt_yf @ hs_xf_yt) |> function Some (_, x) -> x | None -> assert false

  let choose_separating_halfspace_lazy t x y ex_in_poly =
    let fenv = Set.Poly.empty in (*TODO: generate fenv*)
    let params_x = Table.get_params_x t in
    let p = Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt in
    let vars_params = SortEnv.map ~f:(fun x -> x, Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt) params_x in
    let h : halfspace = (Map.Poly.of_alist_exn vars_params, p, Ge0) in
    let _, params = List.unzip vars_params in
    let params = p::params in
    let formula = formula_of_halfspace h in
    let xp = Formula.subst (Table.get_x_map t x) formula in
    let yn = Formula.mk_neg (Formula.subst (Table.get_x_map t y) formula) in
    let hard = [xp; yn] in
    let soft = List.map ~f:(fun (x, y) ->
        let xn = Formula.mk_neg (Formula.subst (Table.get_x_map t x) formula) in
        let yp = Formula.subst (Table.get_x_map t y) formula in
        Formula.mk_or xn yp
      ) ex_in_poly in
    let soft = Map.Poly.singleton "noncrossing" (List.map ~f:(fun x -> (x, 1)) soft) in
    match Z3Smt.Z3interface.max_smt fenv hard soft with
    | Some(_, model) ->
      let zero_model =
        List.map ~f:(fun p -> let (t, _, _) = Term.let_var p in (t, T_int.zero ())) params
        |> Map.Poly.of_alist_exn in
      let model = LogicOld.remove_dontcare model |> Map.Poly.of_alist_exn in
      let model = Map.Poly.merge model zero_model ~f:(fun ~key:_ -> function `Left v | `Both (v, _) | `Right v -> Some v) in
      let h = let (map, c, ineq) = h in (Map.Poly.map ~f:(Term.subst model) map, Term.subst model c, ineq) in
      Table.add_hs t h
    | None -> assert false

  let choose_separating_halfspace t x y ex_in_poly =
    match t with
    | Table.Eager _ -> choose_separating_halfspace_eager t x y ex_in_poly
    | Table.Lazy _ -> choose_separating_halfspace_lazy t x y ex_in_poly

  (* x : incoming, y : outgoing *)
  let rec dtree_separate t x y ex_in_poly =
    function
    | Leaf _ ->
      let h = choose_separating_halfspace t x y ex_in_poly in
      let tt = Leaf (Template.gen_template_lexicographic t) in
      let ft = Leaf (Template.gen_template_lexicographic t) in
      Node (h, tt, ft)
    | Node (h, tt, ft) ->
      match Table.eval_halfspace t x h, Table.eval_halfspace t y h with
      | true, true ->
        let ex_in_poly' = List.filter ~f:(fun (x, y) -> Table.eval_halfspace t x h && Table.eval_halfspace t y h) ex_in_poly in
        Node (h, dtree_separate t x y ex_in_poly' tt, ft)
      | false, false ->
        let ex_in_poly' = List.filter ~f:(fun (x, y) -> not (Table.eval_halfspace t x h) && not (Table.eval_halfspace t y h)) ex_in_poly in
        Node (h, tt, dtree_separate t x y ex_in_poly' ft)
      | _, _ -> Node (h, tt, ft)

  module DecisionTreeTemplate = struct
    type t = (Term.t list * Term.t list) dtree
    let rec eval_dtree t x =
      function
      | Leaf (term, _) -> List.map ~f:(Term.subst (Table.get_x_map t x)) term
      | Node (h, tt, ft) ->
        if Table.eval_halfspace t x h then
          eval_dtree t x tt
        else
          eval_dtree t x ft

    let rec to_term t =
      function
      | Leaf (term, _) -> term
      | Node (h, tt, ft) ->
        let tf = List.zip_exn (to_term t tt) (to_term t ft) in
        List.map tf ~f:(fun (tmt, tmf) -> T_bool.mk_if_then_else (Table.get_halfspace t h |> term_of_halfspace) tmt tmf)

    let rec collect_params =
      function
      | Leaf (_, p) -> p
      | Node (_, tt, ft) -> collect_params tt @ collect_params ft
  end

  let rec add_unsat_example t x y =
    let rec add_incoming x =
      function
      | Leaf (xs, _) -> xs := x::!xs
      | Node (h, tt, ft) ->
        if Table.eval_halfspace t x h then
          add_incoming x tt
        else
          add_incoming x ft in
    let rec add_outgoing x =
      function
      | Leaf (_, xs) -> xs := x::!xs
      | Node (h, tt, ft) ->
        if Table.eval_halfspace t x h then
          add_outgoing x tt
        else
          add_outgoing x ft in
    function
    | Leaf _ -> ()
    | Node (h, tt, ft) ->
      match Table.eval_halfspace t x h, Table.eval_halfspace t y h with
      | true, true -> add_unsat_example t x y tt
      | false, false -> add_unsat_example t x y ft
      | true, false -> add_outgoing x tt; add_incoming y ft
      | false, true -> add_outgoing x ft; add_incoming y tt

  let rec collect_nonempty_dt =
    function
    | Leaf (incoming, outgoing) ->
      if (not (List.is_empty !incoming)) && (not (List.is_empty !outgoing)) then
        [(!incoming, !outgoing)]
      else
        []
    | Node (_, tt, ft) ->
      collect_nonempty_dt tt @ collect_nonempty_dt ft

  let sum_of_abs_params template_params =
    let qs, constraints = List.map ~f:(fun p ->
        let q = Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt in
        let p_le_q = Formula.mk_atom (T_int.mk_leq p q) in
        let minus_q_le_p = Formula.mk_atom (T_int.mk_leq (T_int.mk_neg q) p) in
        q, Formula.mk_and p_le_q minus_q_le_p
      ) template_params |> List.unzip in
    T_int.mk_sum (T_int.zero ()) qs, constraints

  exception LoopEliminationFailure

  let rec loop_elimination lex2wf t dt =
    let example_map, constraints = List.map ~f:(fun (x, y) -> ((x, y), lex2wf (DecisionTreeTemplate.eval_dtree t x dt) (DecisionTreeTemplate.eval_dtree t y dt))) (Table.get_ex_id_list t)
                                   |> List.mapi ~f:(fun i (e, phi) -> let key = Printf.sprintf "D%d" i in ((key, e), (key, phi)))
                                   |> List.unzip
                                   |> fun (a, b) -> (Map.Poly.of_alist_exn a, Map.Poly.of_alist_exn b) in
    Debug.print @@ lazy "synthesizing linear functions"; 
    Debug.print @@ lazy ("constraint size = " ^ string_of_int (Map.Poly.length constraints));
    (*Map.Poly.iter ~f:(fun c -> Debug.print @@ lazy (Evaluator.simplify c |> Formula.str_of)) constraints;*)
    let fenv = Set.Poly.empty in (*TODO: generate fenv*)
    match Z3Smt.Z3interface.check_sat_unsat_core fenv constraints with
    | `Sat model ->
      let model = if config.optimize_sum_coeff then
          let template_params = DecisionTreeTemplate.collect_params dt in
          let obj, abs_constraints = sum_of_abs_params template_params in
          match Z3Smt.Z3interface.check_opt_maximize fenv (Map.Poly.data constraints @ abs_constraints) (T_int.mk_neg obj) with
          | Some (_, _, model) -> model
          | None -> assert false
        else
          model in
      let zero_model =
        DecisionTreeTemplate.collect_params dt
        |> List.map ~f:(fun p -> let t, _, _ = Term.let_var p in (t, T_int.zero ()))
        |> Map.Poly.of_alist_exn in
      let model = remove_dontcare model |> Map.Poly.of_alist_exn in
      let model = Map.Poly.merge model zero_model ~f:(fun ~key:_ -> function `Left v | `Both (v, _) | `Right v -> Some v) in
      dtree_fmap (fun (t, _) -> List.map ~f:(Term.subst model) t) dt
    | `Unsat unsat_keys ->
      Debug.print @@ lazy "loop elimination";
      let unsat_dt = dtree_fmap (fun _ -> (ref [], ref [])) dt in (* incoming/outgoing *)
      List.iter ~f:(fun k -> Debug.print @@ lazy k) unsat_keys;
      let unsat_keys = List.filter ~f:(fun s -> String.is_prefix s ~prefix:"D") unsat_keys in
      List.iter ~f:(fun key -> 
          let (x, y) = Map.Poly.find_exn example_map key in
          Debug.print @@ lazy (
            let x_str = Table.get_x t x |> List.map ~f:Term.str_of |> String.concat ~sep:", " |> fun s -> "(" ^ s ^ ")" in
            let y_str = Table.get_x t y |> List.map ~f:Term.str_of |> String.concat ~sep:", " |> fun s -> "(" ^ s ^ ")" in
            key ^ ": " ^ x_str ^ " " ^ y_str
          );
          let cons = Map.Poly.find_exn constraints key in
          Debug.print @@ lazy (Formula.str_of cons);
          add_unsat_example t x y unsat_dt) unsat_keys;
      let rec find_different_pair xs =
        function
        | [] -> None
        | y::ys ->
          match List.find xs ~f:(fun x -> Stdlib.(<>) (Table.get_x t x) (Table.get_x t y)) with
          | Some x -> Some (x, y)
          | None -> find_different_pair xs ys in
      let x, y = match collect_nonempty_dt unsat_dt |> List.find_map ~f:(fun (xs, ys) -> find_different_pair xs ys) with
        | Some (x, y) -> x, y
        | None -> raise LoopEliminationFailure in
      let x_str = Table.get_x t x |> List.map ~f:Term.str_of |> String.concat ~sep:", " |> fun s -> "(" ^ s ^ ")" in
      let y_str = Table.get_x t y |> List.map ~f:Term.str_of |> String.concat ~sep:", " |> fun s -> "(" ^ s ^ ")" in
      Debug.print @@ lazy ("separate: " ^ x_str ^ " and " ^ y_str);
      let dt' = dtree_separate t x y (Table.get_ex_id_list t) dt in
      loop_elimination lex2wf t dt'
    | `Unknown reason -> failwith reason
    | `Timeout -> failwith "timeout"

  let str_of_halfspace h = formula_of_halfspace h |> Formula.str_of

  (*  let total_time = ref 0.*)
  let mk_classifier pvar (params : SortEnv.t) table labeling _examples =
    let tt = TruthTable.get_table table pvar in
    let tt = TruthTable.set_alist tt labeling in
    Debug.print @@ lazy (sprintf "    labeled atoms (%d):" (Map.Poly.length labeling));
    Debug.print @@ lazy (TruthTable.str_of_atoms tt);
    let _neg_ex, pneg_ex, pos_ex, ppos_ex = TruthTable.papps_of tt in
    (* ToDo: ppos_ex can be non-empty *)
    (* temporarily allow negative examples *)
    assert (Set.Poly.is_empty pneg_ex && Set.Poly.is_empty ppos_ex);
    (* assert (Set.Poly.is_empty neg_ex && Set.Poly.is_empty pneg_ex && Set.Poly.is_empty ppos_ex); *)
    (*    total_time := 0.;
          max_sat_time := 0.;
          let start_time = Stdlib.Sys.time () in*)
    let n = (SortEnv.length params) / 2 in
    let (params_x, params_y) = List.split_n (SortEnv.list_of params) n in
    let params_x = SortEnv.of_list params_x in
    let params_y = SortEnv.of_list params_y in
    let ex = Set.Poly.map ~f:(fun (_, t) -> List.split_n t n) pos_ex in
    let ex_xy = collect_xy ex in
    (*    Debug.print @@ lazy "Halfspace generation";
          List.iter ~f:(fun h -> Debug.print @@ lazy (str_of_halfspace h)) hs;*)
    assert (config.lex_deg >= 0);
    (*    let deg = if config.lex_deg < 0 then 0 else config.lex_deg in*)
    let table = if config.eager_halfspace_gen then
        let hs = gen_halfspaces params_x ex_xy in
        Table.make_eager hs params_x (Set.Poly.to_list ex)
      else
        Table.make_lazy params_x (Set.Poly.to_list ex) in
    try
      let pre_dt = BuildDT.build_dtree Lexicographic.gt table in
      List.iter ~f:(fun tm -> Debug.print @@ lazy (Term.str_of tm)) (dtree_fmap (fun (t, _) -> t) pre_dt |> term_of_dtree table);
      let dtx = loop_elimination Lexicographic.gt table pre_dt in
      let dtx_term = term_of_dtree table dtx in
      let params_x_tvar = SortEnv.args_of params_x in
      let params_y_term = Term.of_sort_env params_y in
      let dty_term = List.map ~f:(Term.subst (List.zip_exn params_x_tvar params_y_term |> Map.Poly.of_alist_exn)) dtx_term in
      Debug.print @@ lazy "** Decision tree";
      List.iter ~f:(fun t -> Debug.print @@ lazy (Evaluator.simplify_term t |> Term.str_of)) dtx_term;
      Ok (SortMap.empty(* parameters of parametric candidate*),
          (pvar, (params, Lexicographic.gt dtx_term dty_term)))
    with
    | LoopEliminationFailure ->
      Debug.print @@ lazy "use stricter well-founded relations";
      let pre_dt = BuildDT.build_dtree Lexicographic.gt2 table in
      List.iter ~f:(fun tm -> Debug.print @@ lazy (Term.str_of tm)) (dtree_fmap (fun (t, _) -> t) pre_dt |> term_of_dtree table);
      let dtx = loop_elimination Lexicographic.gt2 table pre_dt in
      let dtx_term = term_of_dtree table dtx in
      let params_x_tvar = SortEnv.args_of params_x in
      let params_y_term = Term.of_sort_env params_y in
      let dty_term = List.map ~f:(Term.subst (List.zip_exn params_x_tvar params_y_term |> Map.Poly.of_alist_exn)) dtx_term in
      Debug.print @@ lazy "** Decision tree";
      List.iter ~f:(fun t -> Debug.print @@ lazy (Evaluator.simplify_term t |> Term.str_of)) dtx_term;
      Ok (SortMap.empty(* parameters of parametric candidate*),
          (pvar, (params, Lexicographic.gt2 dtx_term dty_term)))
end
