open Core
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld

let avoid_ite_const = false
let avoid_ite_coeffs = false

let quals_over quals params =
  let vs = Set.Poly.of_list @@ List.map ~f:fst params in
  List.filter quals ~f:(fun q -> Set.is_subset (Formula.tvs_of q) ~of_:vs)

let terms_over terms params =
  let vs = Set.Poly.of_list @@ List.map ~f:fst params in
  List.filter terms ~f:(fun t -> Set.is_subset (Term.tvs_of t) ~of_:vs)

let merge temp_paramss =
  Map.of_set_exn @@ Logic.of_old_sort_env_set
  @@ Set.Poly.union_list temp_paramss

let mk_bounds_of_const_int t lb ub seeds =
  Formula.or_of
  @@ List.map (Set.to_list seeds) ~f:(fun n ->
         if
           avoid_ite_const
           && Option.for_all lb ~f:(fun n -> Z.Compare.(n >= Z.zero))
           && Option.for_all ub ~f:(fun n -> Z.Compare.(n >= Z.zero))
         then
           let nt = T_int.mk_int n in
           Formula.mk_or
             (Formula.and_of @@ Formula.mk_range_opt (T_int.mk_sub t nt) lb ub)
             (Formula.and_of @@ Formula.mk_range_opt (T_int.mk_sub nt t) lb ub)
         else
           let norm = T_int.mk_abs @@ T_int.mk_sub t (T_int.mk_int n) in
           Formula.and_of @@ Formula.mk_range_opt norm lb ub)

let mk_bounds_of_const_real t lb ub seeds =
  Formula.or_of
  @@ List.map (Set.to_list seeds) ~f:(fun n ->
         if
           avoid_ite_const
           && Option.for_all lb ~f:(fun n -> Q.(n >= zero))
           && Option.for_all ub ~f:(fun n -> Q.(n >= zero))
         then
           let nt = T_real.mk_real n in
           Formula.mk_or
             (Formula.and_of
             @@ Formula.mk_range_real_opt (T_real.mk_rsub t nt) lb ub)
             (Formula.and_of
             @@ Formula.mk_range_real_opt (T_real.mk_rsub nt t) lb ub)
         else
           let norm = T_real.mk_rabs @@ T_real.mk_rsub t (T_real.mk_real n) in
           Formula.and_of @@ Formula.mk_range_real_opt norm lb ub)

let mk_bounds_of_coeffs_int norm_type ts lb ub be =
  if avoid_ite_coeffs && norm_type = 1 then
    let xps, xns =
      List.unzip
      @@ List.map ts ~f:(fun t ->
             let xp, xn =
               if Term.is_var t then
                 let (Ident.Tvar x, _), _ = Term.let_var t in
                 ( Ident.Tvar (x ^ "#pos" (*ToDo*)),
                   Ident.Tvar (x ^ "#neg" (*ToDo*)) )
               else (Ident.mk_fresh_tvar (), Ident.mk_fresh_tvar ())
             in
             ((xp, T_int.SInt), (xn, T_int.SInt)))
    in
    let tps = Term.of_sort_env xps in
    let tns = Term.of_sort_env xns in
    let ts' = List.map2_exn tps tns ~f:T_int.mk_sub in
    let norm = T_int.mk_sum (T_int.zero ()) (tps @ tns) in
    ( Set.Poly.of_list (xps @ xns),
      Formula.and_of
      @@ List.map (tps @ tns) ~f:(Fn.flip Formula.geq (T_int.zero ()))
      @ List.map2_exn ts ts' ~f:Formula.eq
      @ Formula.mk_range_opt norm lb ub
      @
      match be with
      | None -> []
      | Some be ->
          List.concat_map ts' ~f:(fun t -> Formula.mk_range t (Z.neg be) be) )
  else
    let norm =
      if norm_type = 1 then T_int.l1_norm ts
      else if norm_type = 2 then T_int.l2_norm_sq ts
      else failwith "not supported"
    in
    ( Set.Poly.empty,
      Formula.and_of
      @@ Formula.mk_range_opt norm lb ub
      @
      match be with
      | None -> []
      | Some be ->
          List.concat_map ts ~f:(fun t -> Formula.mk_range t (Z.neg be) be) )

let mk_bounds_of_coeffs_real norm_type ts lb ub be =
  if avoid_ite_coeffs && norm_type = 1 then
    let xps, xns =
      List.unzip
      @@ List.map ts ~f:(fun t ->
             let xp, xn =
               if Term.is_var t then
                 let (Ident.Tvar x, _), _ = Term.let_var t in
                 ( Ident.Tvar (x ^ "#pos" (*ToDo*)),
                   Ident.Tvar (x ^ "#neg" (*ToDo*)) )
               else (Ident.mk_fresh_tvar (), Ident.mk_fresh_tvar ())
             in
             ((xp, T_real.SReal), (xn, T_real.SReal)))
    in
    let tps = Term.of_sort_env xps in
    let tns = Term.of_sort_env xns in
    let ts' = List.map2_exn tps tns ~f:T_real.mk_rsub in
    let norm = T_real.mk_rsum (T_real.rzero ()) (tps @ tns) in
    ( Set.Poly.of_list (xps @ xns),
      Formula.and_of
      @@ List.map (tps @ tns) ~f:(Fn.flip Formula.geq (T_real.rzero ()))
      @ List.map2_exn ts ts' ~f:Formula.eq
      @ Formula.mk_range_real_opt norm lb ub
      @
      match be with
      | None -> []
      | Some be ->
          List.concat_map ts' ~f:(fun t ->
              Formula.mk_range_real t (Q.neg be) be) )
  else
    let norm =
      if norm_type = 1 then T_real.l1_norm ts
      else if norm_type = 2 then T_real.l2_norm_sq ts
      else failwith "not supported"
    in
    ( Set.Poly.empty,
      Formula.and_of
      @@ Formula.mk_range_real_opt norm lb ub
      @
      match be with
      | None -> []
      | Some be ->
          List.concat_map ts ~f:(fun t -> Formula.mk_range_real t (Q.neg be) be)
    )

type hole_qualifiers_map_elem = (Ident.tvar * (sort_env_list * Formula.t)) list
type hole_qualifiers_map = (Ident.tvar * hole_qualifiers_map_elem) list

let gen_hole_for_qualifiers ?(qds = None) (params, quals) =
  let hole = Ident.mk_fresh_tvar ~prefix:(Some "hole") () in
  if List.is_empty quals then (Set.Poly.empty, [], hole)
  else
    let qds =
      match qds with
      | Some qds -> qds
      | None ->
          Array.init (List.length quals) ~f:(fun _ ->
              Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt)
    in
    let temp_params, temp_param_qual_map =
      List.unzip
      @@ List.mapi quals ~f:(fun i qual ->
             let (temp_param, sort), _ = Term.let_var qds.(i) in
             ((temp_param, sort), (temp_param, (params, qual))))
    in
    ( Set.Poly.of_list temp_params,
      (temp_param_qual_map : hole_qualifiers_map_elem),
      hole )

let qual_env_of_hole_map (hole_qualifiers_map : hole_qualifiers_map) =
  List.map hole_qualifiers_map ~f:(fun (_, quals) ->
      List.fold quals ~init:Map.Poly.empty ~f:(fun acc (var, (_, phi)) ->
          Map.Poly.add_exn acc ~key:phi ~data:var))

(** Templates for conjunctive boolean combination of qualifiers *)

let gen_from_qualifiers (params, quals) =
  Logic.Term.mk_lambda params
  @@ Logic.ExtTerm.of_old_formula @@ Formula.and_of
  @@ List.concat_map quals ~f:(fun (temp_param, (_, params', qual)) ->
         let map =
           Map.Poly.of_alist_exn
           @@ List.map2_exn params' params ~f:(fun (x', _) (x, _) -> (x', x))
         in
         let qual = Formula.rename map qual in
         let key = Term.mk_var temp_param T_int.SInt in
         let pos = Formula.mk_imply (Formula.gt key (T_int.zero ())) qual in
         let neg =
           Formula.mk_imply
             (Formula.lt key (T_int.zero ()))
             (Formula.mk_neg qual)
         in
         [ pos; neg ])

(** Templates for ordinary predicate variables *)

let gen_dnf ?(eq_atom = false) ?(terms = []) ?(quals = []) (shp, ubc, ubd, s)
    bec params :
    Logic.sort_env_map
    * hole_qualifiers_map
    * Formula.t
    * Formula.t
    * Formula.t
    * Formula.t =
  let sort, num_ts =
    let terms =
      List.map params ~f:(fun (x, s) -> (Term.mk_var x s, s)) @ terms
    in
    ( Arith.sort_of terms,
      List.filter terms ~f:(function
        | _, T_int.SInt | _, T_real.SReal -> true
        | _, _ -> false) )
  in
  let ( temp_paramss,
        hole_quals_map,
        disjuncs,
        cnstr_of_coeffs,
        cnstr_of_consts,
        cnstr_of_quals ) =
    List.unzip6
    @@ List.init (List.length shp) ~f:(fun idx ->
           let ( temp_paramss,
                 atoms,
                 cnstr_of_coeffs,
                 cnstr_of_consts,
                 cnstr_of_quals ) =
             (* generate affine equality (if eq_atom) or inequality (otherwise) templates *)
             List.unzip5
             @@ List.init (List.nth_exn shp idx) ~f:(fun _ ->
                    let (coeffs, const), tmpl =
                      if eq_atom then Arith.eq_of sort num_ts
                      else Arith.ineq_of sort num_ts
                    in
                    let pos_neg_map, cnstr_of_coeffs =
                      mk_bounds_of_coeffs_int 1 coeffs None ubc bec
                    in
                    let cnstr_of_const =
                      mk_bounds_of_const_int const None ubd s
                    in
                    let cnstr_of_quals = (*ToDo*) Formula.mk_true () in
                    let temp_params =
                      Set.union pos_neg_map @@ Set.Poly.of_list
                      @@ List.map ~f:(Term.let_var >> fst)
                      @@ (const :: coeffs)
                    in
                    ( temp_params,
                      Formula.mk_atom tmpl,
                      cnstr_of_coeffs,
                      cnstr_of_const,
                      cnstr_of_quals ))
           in
           let temp_params_quals, quals, hole =
             gen_hole_for_qualifiers (params, quals)
           in
           let hole_term =
             Formula.mk_atom
             @@ Atom.pvar_app_of_senv (Ident.tvar_to_pvar hole) params
           in
           ( Set.Poly.union_list (temp_params_quals :: temp_paramss),
             (hole, quals),
             Formula.and_of (hole_term :: atoms),
             Formula.and_of cnstr_of_coeffs,
             Formula.and_of cnstr_of_consts,
             Formula.and_of cnstr_of_quals ))
  in
  ( merge temp_paramss,
    hole_quals_map,
    Formula.or_of disjuncs,
    Formula.and_of cnstr_of_coeffs,
    Formula.and_of cnstr_of_consts,
    Formula.and_of cnstr_of_quals )

(** Templates for function variables *)

type tp = {
  shp : int list;
  depth : int;
  ext : int;
  ubec : Z.t option;
  ubed : Z.t option;
  es : Z.t Set.Poly.t;
  ubcc : Z.t option;
  ubcd : Z.t option;
  cs : Z.t Set.Poly.t;
}

type tsp = {
  lbec : Z.t option;
  lbcc : Z.t option;
  beec : Z.t option;
  becc : Z.t option;
}

let mk_tp shp depth ext ubec ubed es ubcc ubcd cs =
  { shp; depth; ext; ubec; ubed; es; ubcc; ubcd; cs }

let mk_tsp lbec lbcc beec becc = { lbec; lbcc; beec; becc }

let gen_cond_and_exps_of_fun quals terms template_params template_sub_params ret
    params r_x =
  let irb_params = List.filter params ~f:(snd >> Term.is_irb_sort) in
  let txs =
    List.map ~f:T_irb.to_int_if_rb
    @@ Term.of_sort_env irb_params
    @ List.filter terms ~f:T_irb.is_sirb
  in
  let size = List.length txs in
  let gen_params_2d nd =
    Array.init nd ~f:(fun i ->
        let nc = List.nth_exn template_params.shp i in
        Array.init nc ~f:(fun _j ->
            Array.init (size + 1) ~f:(fun _ ->
                Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt)))
  in
  let nd = max 1 (*ToDo*) @@ List.length template_params.shp in
  let dc = gen_params_2d (nd - 1) in
  let d_x i j =
    T_int.mk_sum
      dc.(i).(j).(0)
      (List.mapi ~f:(fun k -> T_int.mk_mult dc.(i).(j).(k + 1)) txs)
  in
  let temp_params_fun =
    Set.Poly.of_list
    @@ List.map ~f:(Term.let_var >> fst)
    @@ List.concat_map ~f:Array.to_list
    @@ List.concat_map ~f:Array.to_list
    @@ Array.to_list dc
  in
  let temp_params_quals, hole_quals_map, exp_x =
    let ts = List.init nd ~f:(fun i -> (i, r_x i)) in
    let rest, last = List.rest_last ts in
    List.fold_right rest
      ~init:(Set.Poly.empty, [], snd last)
      ~f:(fun (i, t1) (temp_params_quals', hole_quals_map, t2) ->
        let nc = List.nth_exn template_params.shp i in
        let params =
          match ret with None -> params | Some ret -> params @ [ ret ]
        in
        let temp_params_quals, quals, hole =
          gen_hole_for_qualifiers (params, quals)
        in
        let hole_term =
          Formula.mk_atom
          @@ Atom.pvar_app_of_senv (Ident.tvar_to_pvar hole) params
        in
        ( Set.union temp_params_quals temp_params_quals',
          (hole, quals) :: hole_quals_map,
          let cond =
            Formula.and_of
            @@ hole_term
               :: List.init nc ~f:(fun j ->
                      Formula.geq (d_x i j) (T_int.zero ()))
          in
          T_bool.ifte cond t1 t2 ))
  in
  let cond_pos_neg_map, cond_coeffs_bounds =
    let cond_pos_neg_maps, phis =
      List.unzip
      @@ List.init (nd - 1) ~f:(fun i ->
             let maps, phis =
               let nc = List.nth_exn template_params.shp i in
               List.unzip
               @@ List.init nc ~f:(fun j ->
                      let ts =
                        Array.to_list
                        @@ Array.slice dc.(i).(j) 1 (Array.length dc.(i).(j))
                      in
                      mk_bounds_of_coeffs_int 1 ts template_sub_params.lbcc
                        template_params.ubcc template_sub_params.becc)
             in
             (Set.Poly.union_list maps, Formula.and_of phis))
    in
    (Set.Poly.union_list cond_pos_neg_maps, Formula.and_of phis)
  in
  let cond_const_bounds =
    Formula.and_of
    @@ List.init (nd - 1) ~f:(fun i ->
           let nc = List.nth_exn template_params.shp i in
           Formula.and_of
           @@ List.init nc ~f:(fun j ->
                  mk_bounds_of_const_int
                    dc.(i).(j).(0)
                    None template_params.ubcd template_params.cs))
  in
  ( temp_params_fun,
    temp_params_quals,
    hole_quals_map,
    exp_x,
    cond_pos_neg_map,
    cond_coeffs_bounds,
    cond_const_bounds )

let gen_dt_fun quals terms template_params template_sub_params ~ret:(v, sort)
    params :
    Logic.sort_env_map
    * hole_qualifiers_map
    * Term.t
    * Formula.t
    * Formula.t
    * Formula.t
    * Formula.t
    * Formula.t =
  let quals, _ret_quals =
    List.partition_tf quals ~f:(fun qual ->
        not @@ Set.mem (Formula.tvs_of qual) v)
  in
  let int_terms =
    List.dedup_and_sort ~compare:Stdlib.compare
    @@ List.filter ~f:T_int.is_sint
    @@ Term.of_sort_env params @ terms_over terms params
  in
  let dc =
    Array.init template_params.ext ~f:(fun _ ->
        Array.init
          (List.length int_terms + 1)
          ~f:(fun _ -> Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt))
  in
  let ext_params_map =
    Set.Poly.of_list @@ List.concat
    @@ List.init template_params.ext ~f:(fun i ->
           List.init
             (List.length int_terms + 1)
             ~f:(fun j -> fst @@ Term.let_var dc.(i).(j)))
  in
  let dt_terms =
    let affines =
      List.init template_params.ext ~f:(fun i ->
          T_int.mk_sum dc.(i).(0)
          @@ List.mapi int_terms ~f:(fun j -> T_int.mk_mult dc.(i).(j + 1)))
    in
    Set.to_list
    @@ Datatype.enum_cons_terms template_params.depth sort
    @@ Set.Poly.of_list @@ List.append affines @@ Term.of_sort_env params
  in
  let gen_exp_params nd =
    Array.init nd ~f:(fun _ ->
        Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt)
  in
  let nd = max 1 (*ToDo*) @@ List.length template_params.shp in
  let ec = gen_exp_params nd in
  let ( temp_params_fun,
        temp_params_quals,
        hole_quals_map,
        exp_x,
        cond_pos_neg_map,
        cond_coeffs_bounds,
        cond_const_bounds ) =
    let r_x i =
      List.fold_right
        (List.mapi dt_terms ~f:(fun i t -> (t, i)))
        ~init:(Term.mk_dummy sort)
        ~f:(fun (t1, j) t2 ->
          T_bool.ifte (Formula.eq ec.(i) (T_int.from_int j)) t1 t2)
    in
    gen_cond_and_exps_of_fun quals dt_terms template_params template_sub_params
      (Some (v, sort))
      params r_x
  in
  let expr_params_map, expr_params_bound =
    let params, bounds =
      List.unzip
      @@ List.init nd ~f:(fun i ->
             ( fst @@ Term.let_var ec.(i),
               [
                 Formula.mk_atom @@ T_int.mk_geq ec.(i) (T_int.zero ());
                 Formula.mk_atom
                 @@ T_int.mk_lt ec.(i) (T_int.from_int (List.length terms));
               ] ))
    in
    (Set.Poly.of_list params, Formula.and_of @@ List.concat bounds)
  in
  let expr_const_bounds =
    match template_params.ubed with
    | Some ubed ->
        Formula.and_of
        @@ List.init template_params.ext ~f:(fun i ->
               Formula.mk_atom
               @@ T_int.mk_leq (T_int.mk_abs dc.(i).(0)) (T_int.mk_int ubed))
    | _ -> Formula.mk_true ()
  in
  let expr_coeffs_bounds =
    match template_params.ubec with
    | Some ubec ->
        Formula.and_of
        @@ List.init template_params.ext ~f:(fun i ->
               Formula.mk_atom
               @@ T_int.mk_leq
                    (Array.foldi dc.(i) ~init:(T_int.zero ()) ~f:(fun j acc c ->
                         if j = 0 then acc
                         else T_int.mk_add acc @@ T_int.mk_abs c))
                    (T_int.mk_int ubec))
    | _ -> Formula.mk_true ()
  in
  let temp_params =
    merge
      [
        cond_pos_neg_map;
        temp_params_fun;
        temp_params_quals;
        expr_params_map;
        ext_params_map;
      ]
  in
  ( temp_params,
    hole_quals_map,
    exp_x,
    expr_params_bound,
    expr_coeffs_bounds,
    expr_const_bounds,
    cond_coeffs_bounds,
    cond_const_bounds )

let gen_bool_fun quals _terms template_params template_sub_params ~ret:(v, sort)
    params :
    Logic.sort_env_map
    * hole_qualifiers_map
    * Term.t
    * Formula.t
    * Formula.t
    * Formula.t
    * Formula.t
    * Formula.t =
  let quals, _ret_quals =
    List.partition_tf quals ~f:(fun qual ->
        not @@ Set.mem (Formula.tvs_of qual) v)
  in
  let terms = List.map quals ~f:T_bool.of_formula in
  let gen_exp_params nd =
    Array.init nd ~f:(fun _ ->
        Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt)
  in
  let nd = max 1 (*ToDo*) @@ List.length template_params.shp in
  let ec = gen_exp_params nd in
  let ( temp_params_fun,
        temp_params_quals,
        hole_quals_map,
        exp_x,
        cond_pos_neg_map,
        cond_coeffs_bounds,
        cond_const_bounds ) =
    let r_x i =
      List.fold_right
        (List.mapi terms ~f:(fun i t -> (t, i)))
        ~init:(Term.mk_dummy sort)
        ~f:(fun (t1, j) t2 ->
          T_bool.ifte (Formula.eq ec.(i) (T_int.from_int j)) t1 t2)
    in
    gen_cond_and_exps_of_fun quals terms template_params template_sub_params
      (Some (v, sort))
      params r_x
  in
  let expr_params_map, expr_params_bound =
    let params, bounds =
      List.unzip
      @@ List.init nd ~f:(fun i ->
             ( fst @@ Term.let_var ec.(i),
               [
                 Formula.mk_atom @@ T_int.mk_geq ec.(i) (T_int.zero ());
                 Formula.mk_atom
                 @@ T_int.mk_lt ec.(i) (T_int.from_int (List.length terms));
               ] ))
    in
    (Set.Poly.of_list params, Formula.and_of @@ List.concat bounds)
  in
  let expr_const_bounds = Formula.mk_true () in
  let expr_coeffs_bounds = Formula.mk_true () in
  let temp_params =
    merge
      [ cond_pos_neg_map; temp_params_fun; temp_params_quals; expr_params_map ]
  in
  ( temp_params,
    hole_quals_map,
    exp_x,
    expr_params_bound,
    expr_coeffs_bounds,
    expr_const_bounds,
    cond_coeffs_bounds,
    cond_const_bounds )

let gen_int_fun quals terms template_params template_sub_params ?(ret = None)
    params :
    Logic.sort_env_map
    * hole_qualifiers_map
    * Term.t
    * Formula.t
    * Formula.t
    * Formula.t
    * Formula.t
    * Formula.t =
  let irb_params = List.filter params ~f:(snd >> Term.is_irb_sort) in
  let txs =
    List.map ~f:T_irb.to_int_if_rb
    @@ Term.of_sort_env irb_params
    @ List.filter terms ~f:T_irb.is_sirb
  in
  let quals, ret_quals =
    List.partition_tf quals ~f:(fun qual ->
        match ret with
        | None -> true
        | Some (v, _) -> not @@ Set.mem (Formula.tvs_of qual) v)
  in
  let ret_quals =
    List.filter ret_quals ~f:(fun phi ->
        match ret with
        | None -> false
        | Some (v, s) ->
            Option.is_some
            @@ AffineTerm.extract_affine_term_from
                 (Stdlib.( = ) (Term.mk_var v s))
                 phi)
  in
  let size = List.length txs in
  let gen_params_1d nd =
    Array.init (max 1 nd) ~f:(fun _i ->
        Array.init (size + 1) ~f:(fun _ ->
            Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt))
  in
  let gen_params_2d nd =
    Array.init (max 1 nd) ~f:(fun i ->
        let nc = if nd >= 1 then List.nth_exn template_params.shp i else 1 in
        Array.init nc ~f:(fun _j ->
            Array.init (size + 1) ~f:(fun _ ->
                Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt)))
  in
  let nd = List.length template_params.shp in
  let ec =
    Array.init (max 1 nd) ~f:(fun _i ->
        Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt)
  in
  let gen_expr i exp_x =
    match ret with
    | None -> exp_x
    | Some (v, s) ->
        (* print_endline @@ (sprintf "[%s] quals:\n" (Ident.name_of_tvar @@ v) ^
           String.concat_map_list ~sep:"\n" ret_quals ~f:Formula.str_of); *)
        let ts =
          List.filter_mapi ret_quals ~f:(fun i phi ->
              Option.map
                ~f:(fun t -> (i, t))
                (AffineTerm.extract_affine_term_from
                   (Stdlib.( = ) (Term.mk_var v s))
                   phi))
        in
        List.fold_right ts ~init:exp_x ~f:(fun (j, t1) t2 ->
            T_bool.ifte (Formula.eq ec.(i) (T_int.from_int j)) t1 t2)
  in
  let expr_params_map, expr_params_bound =
    if List.is_empty ret_quals then (Set.Poly.empty, Formula.mk_true ())
    else
      let params, bounds =
        List.unzip
        @@ List.init (Array.length ec) ~f:(fun i ->
               ( fst @@ Term.let_var ec.(i),
                 [
                   Formula.mk_atom @@ T_int.mk_geq ec.(i) (T_int.zero ());
                   Formula.mk_atom
                   @@ T_int.mk_leq ec.(i)
                        (T_int.from_int (List.length ret_quals));
                 ] ))
      in
      (Set.Poly.of_list params, Formula.and_of @@ List.concat bounds)
  in
  if nd <= 0 then
    let exp_x = gen_expr 0 (T_int.zero ()) in
    let temp_params =
      Map.of_set_exn @@ Logic.of_old_sort_env_set expr_params_map
    in
    ( temp_params,
      [],
      exp_x,
      expr_params_bound,
      Formula.mk_true (),
      Formula.mk_true (),
      Formula.mk_true (),
      Formula.mk_true () )
  else
    let rc, dc = (gen_params_1d nd, gen_params_2d (nd - 1)) in
    let r_x i =
      T_int.mk_sum
        rc.(i).(0)
        (List.mapi ~f:(fun j -> T_int.mk_mult rc.(i).(j + 1)) txs)
    in
    let d_x i j =
      T_int.mk_sum
        dc.(i).(j).(0)
        (List.mapi ~f:(fun k -> T_int.mk_mult dc.(i).(j).(k + 1)) txs)
    in
    let temp_params_quals, hole_quals_map, exp_x =
      let ts = List.init nd ~f:(fun i -> (i, r_x i)) in
      let rest, last = List.rest_last ts in
      List.fold_right rest
        ~init:(Set.Poly.empty, [], uncurry gen_expr last)
        ~f:(fun (i, t1) (temp_params_quals', hole_quals_map, t2) ->
          let nc = List.nth_exn template_params.shp i in
          let params =
            match ret with None -> params | Some ret -> params @ [ ret ]
          in
          let temp_params_quals, quals, hole =
            gen_hole_for_qualifiers (params, quals)
          in
          let hole_term =
            Formula.mk_atom
            @@ Atom.pvar_app_of_senv (Ident.tvar_to_pvar hole) params
          in
          ( Set.union temp_params_quals temp_params_quals',
            (hole, quals) :: hole_quals_map,
            let cond =
              Formula.and_of
              @@ hole_term
                 :: List.init nc ~f:(fun j ->
                        Formula.geq (d_x i j) (T_int.zero ()))
            in
            T_bool.ifte cond (gen_expr i t1) t2 ))
    in
    let expr_pos_neg_map, expr_coeffs_bounds =
      let expr_pos_neg_maps, phis =
        List.unzip
        @@ List.init nd ~f:(fun i ->
               let ts =
                 Array.to_list @@ Array.slice rc.(i) 1 (Array.length rc.(i))
               in
               mk_bounds_of_coeffs_int 1 ts template_sub_params.lbec
                 template_params.ubec template_sub_params.beec)
      in
      (Set.Poly.union_list expr_pos_neg_maps, Formula.and_of phis)
    in
    let expr_const_bounds =
      Formula.and_of
      @@ List.init nd ~f:(fun i ->
             mk_bounds_of_const_int
               rc.(i).(0)
               None template_params.ubed template_params.es)
    in
    let cond_pos_neg_map, cond_coeffs_bounds =
      let cond_pos_neg_maps, phis =
        List.unzip
        @@ List.init (nd - 1) ~f:(fun i ->
               let maps, phis =
                 let nc = List.nth_exn template_params.shp i in
                 List.unzip
                 @@ List.init nc ~f:(fun j ->
                        let ts =
                          Array.to_list
                          @@ Array.slice dc.(i).(j) 1 (Array.length dc.(i).(j))
                        in
                        mk_bounds_of_coeffs_int 1 ts template_sub_params.lbcc
                          template_params.ubcc template_sub_params.becc)
               in
               (Set.Poly.union_list maps, Formula.and_of phis))
      in
      (Set.Poly.union_list cond_pos_neg_maps, Formula.and_of phis)
    in
    let cond_const_bounds =
      Formula.and_of
      @@ List.init (nd - 1) ~f:(fun i ->
             let nc = List.nth_exn template_params.shp i in
             Formula.and_of
             @@ List.init nc ~f:(fun j ->
                    mk_bounds_of_const_int
                      dc.(i).(j).(0)
                      None template_params.ubcd template_params.cs))
    in
    let temp_params =
      let temp_params_fun =
        Set.Poly.of_list
        @@ List.map ~f:(Term.let_var >> fst)
        @@ (List.concat_map ~f:Array.to_list @@ Array.to_list rc)
        @ List.concat_map ~f:Array.to_list
        @@ List.concat_map ~f:Array.to_list
        @@ Array.to_list dc
      in
      Map.of_set_exn @@ Logic.of_old_sort_env_set
      @@ Set.Poly.union_list
           [
             expr_pos_neg_map;
             cond_pos_neg_map;
             expr_params_map;
             temp_params_fun;
             temp_params_quals;
           ]
    in
    ( temp_params,
      hole_quals_map,
      exp_x,
      expr_params_bound,
      expr_coeffs_bounds,
      expr_const_bounds,
      cond_coeffs_bounds,
      cond_const_bounds )

let gen_real_fun quals terms template_params template_sub_params ?(ret = None)
    params =
  let ( temp_params,
        hole_quals_map,
        exp_x,
        expr_params_bound,
        expr_coeffs_bounds,
        expr_const_bounds,
        cond_coeffs_bounds,
        cond_const_bounds ) =
    gen_int_fun quals terms template_params template_sub_params ~ret params
  in
  ( temp_params,
    hole_quals_map,
    T_irb.mk_int_to_real exp_x,
    expr_params_bound,
    expr_coeffs_bounds,
    expr_const_bounds,
    cond_coeffs_bounds,
    cond_const_bounds )

let gen_bv_fun quals terms template_params template_sub_params ?(ret = None)
    params =
  let ( temp_params,
        hole_quals_map,
        exp_x,
        expr_params_bound,
        expr_coeffs_bounds,
        expr_const_bounds,
        cond_coeffs_bounds,
        cond_const_bounds ) =
    gen_int_fun quals terms template_params template_sub_params ~ret params
  in
  let size = match ret with Some (_, T_bv.SBV size) -> size | _ -> None in
  ( temp_params,
    hole_quals_map,
    T_irb.mk_int_to_bv ~size exp_x,
    expr_params_bound,
    expr_coeffs_bounds,
    expr_const_bounds,
    cond_coeffs_bounds,
    cond_const_bounds )

let gen_array_fun _quals _terms _template_params _template_sub_params
    ?(ret = None) _params =
  match ret with
  | None -> failwith "gen_array_fun"
  | Some (_, s) -> (*ToDo*)
      ( Map.Poly.empty,
        [],
        Term.mk_dummy s,
        Formula.mk_true (),
        Formula.mk_true (),
        Formula.mk_true (),
        Formula.mk_true (),
        Formula.mk_true () )

let gen_prop_fun is_integ quals terms template_params template_sub_params
    ?(ret = None) params :
    Logic.sort_env_map
    * hole_qualifiers_map
    * Term.t
    * Formula.t
    * Formula.t
    * Formula.t
    * Formula.t
    * Formula.t =
  let int_real_params =
    List.filter params ~f:(fun (_, s) ->
        Term.is_int_sort s || Term.is_real_sort s)
  in
  let txs =
    List.map
      ~f:(fun t -> if T_real.is_sreal t then t else T_irb.mk_int_to_real t)
      (Term.of_sort_env int_real_params
      @ if is_integ then [] else List.filter terms ~f:T_irb.is_sint_sreal)
  in
  let quals =
    List.filter quals ~f:(fun qual ->
        match ret with
        | None -> true
        | Some (v, _) ->
            let tvs = Formula.tvs_of qual in
            (not @@ Set.mem tvs v)
            &&
            if is_integ then
              not
              @@ Set.mem tvs (fst @@ fst @@ Term.let_var @@ List.last_exn txs)
            else true)
  in
  let size = List.length txs in
  let gen_params_1d nd =
    Array.init (max 1 nd) ~f:(fun _i ->
        Array.init (size + 1) ~f:(fun _ ->
            Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt))
  in
  let gen_params_2d nd =
    let size = if is_integ then size - 1 else size in
    Array.init (max 1 nd) ~f:(fun i ->
        let nc = if nd >= 1 then List.nth_exn template_params.shp i else 1 in
        Array.init nc ~f:(fun _j ->
            Array.init (size + 1) ~f:(fun _ ->
                Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt)))
  in
  let nd = List.length template_params.shp in
  if nd <= 0 then
    ( Map.Poly.empty,
      [],
      T_int.zero (),
      Formula.mk_true (),
      Formula.mk_true (),
      Formula.mk_true (),
      Formula.mk_true (),
      Formula.mk_true () )
  else
    let rc, dc = (gen_params_1d nd, gen_params_2d (nd - 1)) in
    let r_x i =
      (if is_integ then Fn.id else T_real.mk_rabs ~info:Dummy)
      @@ T_real.mk_rsum
           (T_irb.mk_int_to_real rc.(i).(0))
           (List.mapi
              ~f:(fun j t ->
                T_real.mk_rmult (T_irb.mk_int_to_real rc.(i).(j + 1)) t)
              txs)
    in
    let d_x i j =
      T_real.mk_rsum
        (T_irb.mk_int_to_real dc.(i).(j).(0))
        (List.mapi ~f:(fun k ->
             T_real.mk_rmult (T_irb.mk_int_to_real dc.(i).(j).(k + 1)))
        @@ if is_integ then List.initial txs else txs)
    in
    let temp_params_quals, hole_quals_map, exp_x =
      let ts = List.init nd ~f:(fun i -> (i, r_x i)) in
      let _last_i, last_t = List.last_exn ts in
      List.fold_right
        (List.take ts (List.length ts - 1))
        ~init:(Set.Poly.empty, [], last_t)
        ~f:(fun (i, t1) (temp_params_quals', hole_quals_map, t2) ->
          let nc = List.nth_exn template_params.shp i in
          let params =
            match ret with None -> params | Some ret -> params @ [ ret ]
          in
          let temp_params_quals, quals, hole =
            gen_hole_for_qualifiers (params, quals)
          in
          let hole_term =
            Formula.mk_atom
            @@ Atom.pvar_app_of_senv (Ident.tvar_to_pvar hole) params
          in
          ( Set.union temp_params_quals temp_params_quals',
            (hole, quals) :: hole_quals_map,
            let cond =
              Formula.and_of
              @@ hole_term
                 :: List.init nc ~f:(fun j ->
                        Formula.geq (d_x i j) (T_real.rzero ()))
            in
            T_bool.ifte cond t1 t2 ))
    in
    let expr_pos_neg_map, expr_coeffs_bounds =
      let expr_pos_neg_maps, phis =
        List.unzip
        @@ List.init nd ~f:(fun i ->
               let ts =
                 Array.to_list @@ Array.slice rc.(i) 1 (Array.length rc.(i))
               in
               mk_bounds_of_coeffs_int 1 ts template_sub_params.lbec
                 template_params.ubec template_sub_params.beec)
      in
      (Set.Poly.union_list expr_pos_neg_maps, Formula.and_of phis)
    in
    let expr_const_bounds =
      Formula.and_of
      @@ List.init nd ~f:(fun i ->
             mk_bounds_of_const_int
               rc.(i).(0)
               None template_params.ubed template_params.es)
    in
    let cond_pos_neg_map, cond_coeffs_bounds =
      let cond_pos_neg_maps, phis =
        List.unzip
        @@ List.init (nd - 1) ~f:(fun i ->
               let maps, phis =
                 let nc = List.nth_exn template_params.shp i in
                 List.unzip
                 @@ List.init nc ~f:(fun j ->
                        let ts =
                          Array.to_list
                          @@ Array.slice dc.(i).(j) 1 (Array.length dc.(i).(j))
                        in
                        mk_bounds_of_coeffs_int 1 ts None template_params.ubcc
                          None)
               in
               (Set.Poly.union_list maps, Formula.and_of phis))
      in
      (Set.Poly.union_list cond_pos_neg_maps, Formula.and_of phis)
    in
    let cond_const_bounds =
      Formula.and_of
      @@ List.init (nd - 1) ~f:(fun i ->
             let nc = List.nth_exn template_params.shp i in
             Formula.and_of
             @@ List.init nc ~f:(fun j ->
                    mk_bounds_of_const_int
                      dc.(i).(j).(0)
                      None template_params.ubcd template_params.cs))
    in
    let temp_params =
      let temp_params_fun =
        Set.Poly.of_list
        @@ List.map ~f:(Term.let_var >> fst)
        @@ (List.concat_map ~f:Array.to_list @@ Array.to_list rc)
        @ List.concat_map ~f:Array.to_list
        @@ List.concat_map ~f:Array.to_list
        @@ Array.to_list dc
      in
      Map.of_set_exn @@ Logic.of_old_sort_env_set
      @@ Set.Poly.union_list
           [
             expr_pos_neg_map;
             cond_pos_neg_map;
             temp_params_fun;
             temp_params_quals;
           ]
    in
    ( temp_params,
      hole_quals_map,
      exp_x,
      Formula.mk_true (),
      expr_coeffs_bounds,
      expr_const_bounds,
      cond_coeffs_bounds,
      cond_const_bounds )

let gen_fun ignore_bool quals terms template_params template_sub_params
    ?(ret = None) ?(prop = false) ?(is_integ = false) params :
    Logic.sort_env_map
    * hole_qualifiers_map
    * Term.t
    * Formula.t
    * Formula.t
    * Formula.t
    * Formula.t
    * Formula.t =
  let rec aux = function
    | [] ->
        (match ret with
        | Some ((_, T_dt.SDT _) as ret) -> gen_dt_fun ~ret
        | Some ((_, T_bool.SBool) as ret) -> gen_bool_fun ~ret
        | None | Some (_, T_int.SInt) -> gen_int_fun ~ret
        | Some (_, T_real.SReal) ->
            if prop then gen_prop_fun is_integ ~ret else gen_real_fun ~ret
        | Some (_, T_bv.SBV _) -> gen_bv_fun ~ret
        | Some (_, T_array.SArray _) -> gen_array_fun ~ret
        | Some (_, T_tuple.STuple sorts)
          when prop && List.for_all sorts ~f:Term.is_real_sort ->
            gen_prop_fun is_integ ~ret
        | Some (_, sort) ->
            failwith
            @@ sprintf "[gen_fun] %s not supported" (Term.str_of_sort sort))
          quals terms template_params template_sub_params params
    | (x, sort) :: xs ->
        assert (Term.is_bool_sort sort);
        let ( temp_params1,
              hole_quals_map1,
              exp_x1,
              expr_dt_bounds1,
              expr_coeffs_bounds1,
              expr_const_bounds1,
              cond_coeffs_bounds1,
              cond_const_bounds1 ) =
          aux xs
        in
        let ( temp_params2,
              hole_quals_map2,
              exp_x2,
              expr_dt_bounds2,
              expr_coeffs_bounds2,
              expr_const_bounds2,
              cond_coeffs_bounds2,
              cond_const_bounds2 ) =
          aux xs
        in
        ( Map.force_merge temp_params1 temp_params2,
          hole_quals_map1 @ hole_quals_map2,
          T_bool.ifte (Formula.of_bool_var x) exp_x1 exp_x2,
          Formula.mk_and expr_dt_bounds1 expr_dt_bounds2,
          Formula.mk_and expr_coeffs_bounds1 expr_coeffs_bounds2,
          Formula.mk_and expr_const_bounds1 expr_const_bounds2,
          Formula.mk_and cond_coeffs_bounds1 cond_coeffs_bounds2,
          Formula.mk_and cond_const_bounds1 cond_const_bounds2 )
  in
  aux
    (if ignore_bool then [] else List.filter params ~f:(snd >> Term.is_bool_sort))

(** Templates for admissible predicate variables *)

let gen_adm_predicate with_cond ignore_bool enable_lhs_param quals terms
    template_params params :
    Logic.sort_env_map
    * hole_qualifiers_map
    * Formula.t
    * Formula.t
    * Formula.t
    * Formula.t
    * Formula.t
    * Formula.t =
  let params, ret = List.rest_last params in
  (* assert (Fn.non Term.is_bool_sort (snd ret)); *)
  let xs =
    match ret with
    | _, T_real.SReal when not with_cond -> [ uncurry Term.mk_var ret ]
    | _, T_tuple.STuple sorts
      when List.for_all sorts ~f:Term.is_real_sort
           && ((not with_cond) || List.length sorts = 2) ->
        List.mapi sorts ~f:(fun i _ ->
            T_tuple.mk_tuple_sel sorts (uncurry Term.mk_var ret) i)
    | _ -> failwith "unsupported sort"
  in
  let lhs_params, ps, lhs_bounds, pxs =
    if enable_lhs_param then
      let coeffs = List.map xs ~f:(fun _ -> Ident.mk_fresh_parameter ()) in
      let ps = List.map coeffs ~f:(fun c -> Term.mk_var c T_int.SInt) in
      ( Map.Poly.of_alist_exn
        @@ List.map coeffs ~f:(fun c -> (c, Logic.IntTerm.SInt)),
        ps,
        List.map ps ~f:(fun p ->
            Formula.mk_atom @@ T_int.mk_leq (T_int.zero ()) p),
        List.map2_exn ps xs ~f:(fun p x ->
            T_real.mk_rmult (T_irb.mk_int_to_real p) x) )
    else (Map.Poly.empty, [], [], xs)
  in
  let ( temp_paramss,
        hole_quals_maps,
        exp_xs,
        expr_dt_boundss,
        expr_coeffs_boundss,
        expr_const_boundss,
        cond_coeffs_boundss,
        cond_const_boundss ) =
    List.unzip8
    @@ List.map pxs ~f:(fun _ ->
           gen_fun ignore_bool quals terms template_params
             (mk_tsp None None None None)
             params ~ret:(Some ret) ~prop:true)
  in
  let b = Ident.mk_fresh_parameter () in
  let map = Map.force_merge_list @@ (lhs_params :: temp_paramss) in
  ( (if with_cond then Map.Poly.add_exn map ~key:b ~data:Logic.BoolTerm.SBool
     else map),
    List.concat hole_quals_maps,
    (if with_cond then
       match (xs, ps, pxs, exp_xs) with
       | [ x; score ], [ _; p2 ], [ px; pscore ], [ exp_x; exp_score ] ->
           let p = T_real.mk_radd (T_real.rone ()) p2 in
           Formula.and_of
           @@ [
                Formula.leq (T_real.rzero ()) x;
                Formula.leq px
                  (T_bool.ifte (Formula.of_bool_var b) exp_x
                     (T_real.mk_rmult score exp_x));
                Formula.leq
                  (T_real.mk_rmin exp_score p)
                  (T_real.mk_radd score pscore);
                (* min (e, p) <= p score where p>=1 *)
                Formula.leq score (T_real.rone ());
              ]
       | _ -> assert false
     else
       Formula.and_of
       @@ List.map3_exn xs pxs exp_xs ~f:(fun x px exp_x ->
              Formula.mk_and
                (Formula.leq (T_real.rzero ()) x)
                (Formula.leq px exp_x))),
    Formula.and_of @@ lhs_bounds @ expr_dt_boundss,
    Formula.and_of expr_coeffs_boundss,
    Formula.and_of expr_const_boundss,
    Formula.and_of cond_coeffs_boundss,
    Formula.and_of cond_const_boundss )

(** Templates for integrable predicate variables *)

let gen_integ_predicate ignore_bool enable_lhs_param quals terms template_params
    params :
    Logic.sort_env_map
    * hole_qualifiers_map
    * Formula.t
    * Formula.t
    * Formula.t
    * Formula.t
    * Formula.t
    * Formula.t =
  let params, ret = List.rest_last params in
  (* assert (Fn.non Term.is_bool_sort (snd ret)); *)
  let xs =
    match ret with
    | _, T_real.SReal -> [ uncurry Term.mk_var ret ]
    | _, T_tuple.STuple sorts when List.for_all sorts ~f:Term.is_real_sort ->
        List.mapi sorts ~f:(fun i _ ->
            T_tuple.mk_tuple_sel sorts (uncurry Term.mk_var ret) i)
    | _ -> failwith "unsupported sort"
  in
  let lhs_params, lhs_bounds, xs =
    if enable_lhs_param then
      let coeffs = List.map xs ~f:(fun _ -> Ident.mk_fresh_parameter ()) in
      let lhs_params = List.map coeffs ~f:(fun c -> Term.mk_var c T_int.SInt) in
      ( Map.Poly.of_alist_exn
        @@ List.map coeffs ~f:(fun c -> (c, Logic.IntTerm.SInt)),
        List.map lhs_params ~f:(fun p ->
            Formula.mk_atom @@ T_int.mk_leq (T_int.zero ()) p),
        List.map2_exn lhs_params xs ~f:(fun p x ->
            T_real.mk_rmult
              (T_irb.mk_int_to_real
                 (*ToDo*) (T_int.mk_add p (T_int.mk_int Z.one)))
              x) )
    else (Map.Poly.empty, [], xs)
  in
  let ( temp_paramss,
        hole_quals_maps,
        exp_xs,
        expr_dt_boundss,
        expr_coeffs_boundss,
        expr_const_boundss,
        cond_coeffs_boundss,
        cond_const_boundss ) =
    List.unzip8
    @@ List.map xs ~f:(fun _ ->
           gen_fun ignore_bool quals terms template_params
             (mk_tsp None None None None)
             params ~ret:(Some ret) ~prop:true ~is_integ:true)
  in
  ( Map.force_merge_list @@ (lhs_params :: temp_paramss),
    List.concat hole_quals_maps,
    Formula.and_of
    @@ List.map2_exn xs exp_xs ~f:(fun x exp_x ->
           Formula.mk_and
             (Formula.leq (T_real.rzero ()) x)
             (Formula.leq x exp_x)),
    Formula.and_of @@ lhs_bounds @ expr_dt_boundss,
    Formula.and_of expr_coeffs_boundss,
    Formula.and_of expr_const_boundss,
    Formula.and_of cond_coeffs_boundss,
    Formula.and_of cond_const_boundss )

(** Templates for functional predicate variables *)

let gen_fn_predicate ignore_bool quals terms template_params template_sub_params
    params :
    Logic.sort_env_map
    * hole_qualifiers_map
    * Formula.t
    * Formula.t
    * Formula.t
    * Formula.t
    * Formula.t
    * Formula.t =
  let params, ret = List.rest_last params in
  (* assert (Fn.non Term.is_bool_sort (snd ret)); *)
  let ( temp_params,
        hole_quals_map,
        exp_x,
        expr_dt_bounds,
        expr_coeffs_bounds,
        expr_const_bounds,
        cond_coeffs_bounds,
        cond_const_bounds ) =
    gen_fun ignore_bool quals terms template_params template_sub_params params
      ~ret:(Some ret)
  in
  ( temp_params,
    hole_quals_map,
    Formula.eq (uncurry Term.mk_var ret) exp_x,
    expr_dt_bounds,
    expr_coeffs_bounds,
    expr_const_bounds,
    cond_coeffs_bounds,
    cond_const_bounds )

(** Templates for non-empty predicate variables *)

let gen_int_ne_template quals terms (_dep, _ext, uc, ud) b_j params (rv, rs) =
  (* print_endline @@ sprintf "gen_int_ne_template terms: %s" @@
     String.concat_map_list ~sep:"," terms ~f:Term.str_of; *)
  let int_terms =
    List.dedup_and_sort ~compare:Stdlib.compare
    @@ List.filter ~f:T_int.is_sint
    @@ Term.of_sort_env params @ terms_over terms params
  in
  let quals =
    let vs = Set.Poly.of_list @@ ((rv, rs) :: params) in
    List.filter quals ~f:(fun phi ->
        match Normalizer.normalize phi with
        | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; _ ], _), _) as
          phi
          when AffineTerm.is_affine t1 ->
            let tvs = Formula.term_sort_env_of phi in
            Set.is_subset tvs ~of_:vs
            && Set.mem tvs (rv, rs)
            && Option.is_some
               @@ AffineTerm.extract_term_from_affine
                    (Stdlib.( = ) (Term.mk_var rv rs))
                    t1
        | _ -> false)
  in
  (* print_endline @@ sprintf "gen_int_ne_template int_terms: %s" @@
     String.concat_map_list ~sep:"," int_terms ~f:Term.str_of; *)
  let dc =
    Array.init
      (List.length int_terms + 1)
      ~f:(fun _ -> Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt)
  in
  let sel_terms, cond =
    let sel_terms, conds =
      List.unzip
      @@ List.filter_map int_terms ~f:(function
           | Term.FunApp (T_dt.DTSel (sel_name, dt, _sort), [ t ], _) as term
             -> (
               match Datatype.look_up_cons_of_sel dt sel_name with
               | Some cons ->
                   Some
                     ( term,
                       Formula.mk_atom
                       @@ T_dt.mk_is_cons dt (Datatype.name_of_cons cons) t )
               | _ -> None)
           | _ -> None)
    in
    (Set.Poly.of_list sel_terms, Formula.and_of conds)
  in
  let tmpl =
    let tmpl_t =
      Formula.mk_imply cond
      @@ Formula.eq (Term.mk_var rv rs)
      @@ T_int.mk_sum dc.(0)
      @@ List.mapi int_terms ~f:(fun i t -> T_int.mk_mult dc.(i + 1) t)
    in
    let tmpl_f =
      Formula.mk_imply (Formula.mk_neg cond)
      @@ Formula.eq (Term.mk_var rv rs)
      @@ T_int.mk_sum dc.(0)
      @@ List.mapi int_terms ~f:(fun i t ->
             T_int.mk_mult
               (if Set.mem sel_terms t then T_int.zero () else dc.(i + 1))
               t)
    in
    Formula.and_of
    @@ Formula.mk_imply
         (Formula.eq b_j @@ T_int.mk_int Z.zero)
         (Formula.and_of [ tmpl_t; tmpl_f ])
       :: List.mapi quals ~f:(fun i qual ->
              Formula.mk_imply
                (Formula.eq b_j @@ T_int.mk_int @@ Z.of_int (i + 1))
                qual)
  in
  let const_bound_constr =
    Formula.mk_atom
    @@ T_int.mk_leq (T_int.mk_abs dc.(0)) (T_int.mk_int @@ Z.of_int ud)
  in
  let coeff_bound_constr =
    Formula.mk_atom
    @@ T_int.mk_leq
         (Array.foldi dc ~init:(T_int.zero ()) ~f:(fun i acc c ->
              if i = 0 then acc else T_int.mk_add acc @@ T_int.mk_abs c))
         (T_int.mk_int @@ Z.of_int uc)
  in
  let param_senv =
    Map.Poly.of_alist_exn @@ Array.to_list
    @@ Array.map dc ~f:(Term.let_var >> fst)
  in
  let scope_constr =
    Formula.and_of
      [
        Formula.mk_atom @@ T_int.mk_geq b_j @@ T_int.zero ();
        Formula.mk_atom @@ T_int.mk_leq b_j @@ T_int.mk_int @@ Z.of_int
        @@ (List.length quals + 1);
      ]
  in
  (param_senv, tmpl, scope_constr, coeff_bound_constr, const_bound_constr)

let gen_bool_ne_template quals _terms (_dep, _ext, _uc, _ud) b_j params (rv, rs)
    =
  let quals =
    List.dedup_and_sort ~compare:Stdlib.compare
    @@ (Formula.mk_true () :: Formula.mk_false () :: quals_over quals params)
  in
  let tmpl =
    Formula.and_of
    @@ List.mapi quals ~f:(fun i qual ->
           Formula.mk_imply
             (Formula.eq b_j @@ T_int.mk_int @@ Z.of_int i)
             (Formula.eq (Term.mk_var rv rs) @@ T_bool.of_formula qual))
  in
  let scope_constr =
    Formula.and_of
      [
        Formula.mk_atom @@ T_int.mk_geq b_j @@ T_int.zero ();
        Formula.mk_atom @@ T_int.mk_leq b_j @@ T_int.mk_int @@ Z.of_int
        @@ List.length quals;
      ]
  in
  (Map.Poly.empty, tmpl, scope_constr, Formula.mk_true (), Formula.mk_true ())

let gen_dt_ne_template _quals terms (dep, ext, uc, ud) b_j params (rv, rs) =
  let int_terms =
    List.dedup_and_sort ~compare:Stdlib.compare
    @@ List.filter ~f:T_int.is_sint
    @@ Term.of_sort_env params @ terms_over terms params
  in
  let dc =
    Array.init ext ~f:(fun _ ->
        Array.init
          (List.length int_terms + 1)
          ~f:(fun _ -> Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt))
  in
  let cons_terms =
    let affines =
      List.init ext ~f:(fun i ->
          T_int.mk_sum dc.(i).(0)
          @@ List.mapi int_terms ~f:(fun j t -> T_int.mk_mult dc.(i).(j + 1) t))
    in
    Set.to_list
    @@ Datatype.enum_cons_terms dep rs
    @@ Set.Poly.of_list @@ List.append affines
    @@ List.map params ~f:(uncurry Term.mk_var)
  in
  let tmpl =
    Formula.and_of
    @@ List.mapi cons_terms ~f:(fun i t ->
           Formula.mk_imply
             (Formula.eq b_j @@ T_int.mk_int @@ Z.of_int i)
             (Formula.eq (Term.mk_var rv rs) t))
  in
  let scope_constr =
    Formula.and_of
      [
        Formula.mk_atom @@ T_int.mk_geq b_j @@ T_int.zero ();
        Formula.mk_atom @@ T_int.mk_leq b_j @@ T_int.mk_int @@ Z.of_int
        @@ List.length cons_terms;
      ]
  in
  let const_bound_constr =
    Formula.and_of
    @@ List.init ext ~f:(fun i ->
           Formula.mk_atom
           @@ T_int.mk_leq
                (T_int.mk_abs dc.(i).(0))
                (T_int.mk_int @@ Z.of_int ud))
  in
  let coeff_bound_constr =
    Formula.and_of
    @@ List.init ext ~f:(fun i ->
           Formula.mk_atom
           @@ T_int.mk_leq
                (Array.foldi dc.(i) ~init:(T_int.zero ()) ~f:(fun j acc c ->
                     if j = 0 then acc else T_int.mk_add acc @@ T_int.mk_abs c))
                (T_int.mk_int @@ Z.of_int uc))
  in
  let param_senv =
    Map.Poly.of_alist_exn @@ List.concat
    @@ List.init ext ~f:(fun i ->
           Array.to_list @@ Array.map dc.(i) ~f:(Term.let_var >> fst))
  in
  (param_senv, tmpl, scope_constr, coeff_bound_constr, const_bound_constr)

let gen_ne_template quals terms (dep, ext, uc, ud) params =
  let param_permutation =
    List.permutation_of @@ List.map params ~f:List.return
  in
  let bc =
    Array.init
      (List.length params + 1)
      ~f:(fun _ -> Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt)
  in
  let mk_select_i op i =
    Formula.mk_binop op (Formula.eq bc.(0) (T_int.mk_int @@ Z.of_int i))
  in
  let param_senv, tmpl, scope_constr, coeff_bound_constr, const_bound_constr =
    let ( param_senvs,
          tmpls,
          scope_constrs,
          coeff_bound_constrs,
          const_bound_constrs ) =
      List.unzip5
      @@ List.mapi param_permutation ~f:(fun i params ->
             let ( param_senvs,
                   tmpls,
                   scope_constrs,
                   coeff_bound_constrs,
                   const_bound_constrs ) =
               List.unzip5
               @@ List.mapi params ~f:(fun j _ ->
                      let params' = List.take params (j + 1) in
                      let xs, r =
                        (List.take params' j, List.last_exn params')
                      in
                      let ( param_senv,
                            tmpl,
                            scope_constr,
                            coeff_bound_constr,
                            const_bound_constr ) =
                        (match snd r with
                        | T_dt.SDT _ -> gen_dt_ne_template
                        | T_int.SInt -> gen_int_ne_template
                        | T_bool.SBool -> gen_bool_ne_template
                        | _ -> failwith "unsupported sort of ne predicate")
                          quals terms (dep, ext, uc, ud)
                          bc.(j + 1)
                          xs r
                      in
                      ( param_senv,
                        tmpl,
                        scope_constr,
                        coeff_bound_constr,
                        const_bound_constr ))
             in
             ( Map.force_merge_list param_senvs,
               mk_select_i Formula.Imply i @@ Formula.and_of tmpls,
               mk_select_i Formula.Imply i @@ Formula.and_of scope_constrs,
               mk_select_i Formula.Imply i @@ Formula.and_of coeff_bound_constrs,
               mk_select_i Formula.Imply i @@ Formula.and_of const_bound_constrs
             ))
    in
    ( Map.force_merge_list param_senvs,
      Formula.and_of tmpls,
      Formula.and_of scope_constrs,
      Formula.and_of coeff_bound_constrs,
      Formula.and_of const_bound_constrs )
  in
  let ne_constr =
    Formula.and_of
      [
        Formula.mk_atom @@ T_int.mk_geq bc.(0) @@ T_int.zero ();
        Formula.mk_atom
        @@ T_int.mk_lt bc.(0)
        @@ T_int.mk_int @@ Z.of_int
        @@ List.length param_permutation;
      ]
  in
  let param_senv =
    Logic.of_old_sort_env_map @@ Map.force_merge param_senv
    @@ Map.Poly.of_alist_exn @@ Array.to_list
    @@ Array.map bc ~f:(Term.let_var >> fst)
  in
  ( param_senv,
    tmpl,
    ne_constr,
    scope_constr,
    coeff_bound_constr,
    const_bound_constr )

(** Templates for well-founded predicate variables *)

let gen_wf_predicate use_ifte quals _terms (* ToDo: not used *)
    (nl, np, ubrc, ubrd, ndc, ubdc, ubdd, ds)
    (norm_type, lbrc, lbdc, berc, bedc) params =
  assert (List.length params mod 2 = 0);
  let irb_params = List.filter params ~f:(snd >> Term.is_irb_sort) in
  let size = List.length irb_params / 2 in
  let irb_params_x, irb_params_y = List.split_n irb_params size in
  let txs = List.map ~f:T_irb.to_int_if_rb @@ Term.of_sort_env irb_params_x in
  let tys = List.map ~f:T_irb.to_int_if_rb @@ Term.of_sort_env irb_params_y in
  let gen_params_2d nl np =
    Array.init nl ~f:(fun _i ->
        Array.init np ~f:(fun _j ->
            Array.init (size + 1) ~f:(fun _ ->
                Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt)))
  in
  let gen_params_3d nl np ndc =
    Array.init nl ~f:(fun _i ->
        Array.init np ~f:(fun _j ->
            Array.init ndc ~f:(fun _k ->
                Array.init (size + 1) ~f:(fun _ ->
                    Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt))))
  in
  let rc, dc =
    (gen_params_2d nl np, gen_params_3d nl (if use_ifte then np - 1 else np) ndc)
  in
  let r_x i j =
    T_int.mk_sum
      rc.(i).(j).(0)
      (List.mapi ~f:(fun k -> T_int.mk_mult rc.(i).(j).(k + 1)) txs)
  in
  let r_y i j =
    T_int.mk_sum
      rc.(i).(j).(0)
      (List.mapi ~f:(fun k -> T_int.mk_mult rc.(i).(j).(k + 1)) tys)
  in
  let d_x i j k =
    T_int.mk_sum
      dc.(i).(j).(k).(0)
      (List.mapi ~f:(fun l -> T_int.mk_mult dc.(i).(j).(k).(l + 1)) txs)
  in
  let d_y i j k =
    T_int.mk_sum
      dc.(i).(j).(k).(0)
      (List.mapi ~f:(fun l -> T_int.mk_mult dc.(i).(j).(k).(l + 1)) tys)
  in
  let temp_params_quals, hole_quals_map, holes =
    let params_x, params_y = List.split_n params (List.length params / 2) in
    let x2y = Formula.rename @@ tvar_map_of_sort_env_list params_x params_y in
    let quals = quals_over quals params_x in
    let temp_params_qualss, hole_quals_maps, holess =
      List.unzip3
      @@ List.init nl ~f:(fun i ->
             let temp_params_qualss, hole_quals_maps, holes =
               List.unzip3
               @@ List.init np ~f:(fun j ->
                      let temp_params_quals, quals_x, hole =
                        gen_hole_for_qualifiers (params, quals)
                      in
                      let quals_y =
                        List.map quals_x ~f:(fun (b, (senv, q)) ->
                            (b, (senv, x2y q)))
                      in
                      let hole_x_name = Ident.name_of_tvar hole ^ "_x" in
                      let hole_y_name = Ident.name_of_tvar hole ^ "_y" in
                      let hole_term_of name =
                        Formula.mk_atom
                        @@ Atom.pvar_app_of_senv (Ident.Pvar name) params
                      in
                      ( temp_params_quals,
                        [
                          (Ident.Tvar hole_x_name, quals_x);
                          (Ident.Tvar hole_y_name, quals_y);
                        ],
                        ( (i, j),
                          (hole_term_of hole_x_name, hole_term_of hole_y_name)
                        ) ))
             in
             ( Set.Poly.union_list temp_params_qualss,
               List.concat hole_quals_maps,
               holes ))
    in
    ( Set.Poly.union_list temp_params_qualss,
      List.concat hole_quals_maps,
      List.concat holess )
  in
  let hole_x i j =
    fst @@ List.Assoc.find_exn ~equal:Stdlib.( = ) holes (i, j)
  in
  let hole_y i j =
    snd @@ List.Assoc.find_exn ~equal:Stdlib.( = ) holes (i, j)
  in
  let disc_x i j =
    Formula.and_of
    @@ hole_x i j
       :: List.init ndc ~f:(fun k -> Formula.geq (d_x i j k) (T_int.zero ()))
  in
  let disc_y i j =
    Formula.and_of
    @@ hole_y i j
       :: List.init ndc ~f:(fun k -> Formula.geq (d_y i j k) (T_int.zero ()))
  in
  let rfun_x i =
    let ts = List.init np ~f:(fun j -> (j, r_x i j)) in
    List.fold_right
      (List.take ts (List.length ts - 1))
      ~init:(snd @@ List.last_exn ts)
      ~f:(fun (j, t1) t2 -> T_bool.ifte (disc_x i j) t1 t2)
  in
  let rfun_y i =
    let ts = List.init np ~f:(fun j -> (j, r_y i j)) in
    List.fold_right
      (List.take ts (List.length ts - 1))
      ~init:(snd @@ List.last_exn ts)
      ~f:(fun (j, t1) t2 -> T_bool.ifte (disc_y i j) t1 t2)
  in
  let tmpl =
    let r_geq_zero =
      if use_ifte then
        Formula.and_of
        @@ List.init nl ~f:(fun i -> Formula.geq (rfun_x i) (T_int.zero ()))
      else
        Formula.and_of
        @@ List.init nl ~f:(fun i ->
               Formula.and_of
               @@ List.init np ~f:(fun j ->
                      Formula.mk_imply (disc_x i j)
                        (Formula.geq (r_x i j) (T_int.zero ()))))
    in
    let d_x_geq_zero =
      if use_ifte then Formula.mk_true ()
      else
        Formula.and_of
        @@ List.init nl ~f:(fun i ->
               Formula.or_of @@ List.init np ~f:(fun j -> disc_x i j))
    in
    let d_y_geq_zero =
      if use_ifte then Formula.mk_true ()
      else
        Formula.and_of
        @@ List.init nl ~f:(fun i ->
               Formula.or_of @@ List.init np ~f:(fun j -> disc_y i j))
    in
    let x_gt_y =
      Formula.or_of
      @@ List.init nl ~f:(fun i ->
             Formula.and_of
               [
                 (if use_ifte then
                    Formula.geq (rfun_x i)
                      (T_int.mk_add (rfun_y i) (T_int.one ()))
                  else
                    Formula.or_of
                    @@ List.init np ~f:(fun j ->
                           Formula.and_of
                             [
                               disc_x i j;
                               Formula.and_of
                               @@ List.init np ~f:(fun k ->
                                      Formula.mk_imply (disc_y i k)
                                        (Formula.geq (r_x i j)
                                           (T_int.mk_add (r_y i k)
                                              (T_int.one ()))));
                             ]));
                 Formula.and_of
                 @@ List.init i ~f:(fun l ->
                        if use_ifte then
                          Formula.geq (rfun_x l)
                            (T_int.mk_add (rfun_y l) (T_int.one ()))
                        else
                          Formula.or_of
                          @@ List.init np ~f:(fun j ->
                                 Formula.and_of
                                   [
                                     disc_x l j;
                                     Formula.and_of
                                     @@ List.init np ~f:(fun k ->
                                            Formula.mk_imply (disc_y l k)
                                              (Formula.geq (r_x l j) (r_y l k)));
                                   ]));
               ])
    in
    Formula.and_of [ r_geq_zero; d_x_geq_zero; d_y_geq_zero; x_gt_y ]
  in
  let rfun_pos_neg_map, rfun_coeffs_bounds =
    let rfun_pos_neg_maps, phis =
      List.unzip
      @@ List.init nl ~f:(fun i ->
             let rfun_pos_neg_maps, phis =
               List.unzip
               @@ List.init np ~f:(fun j ->
                      let ts =
                        Array.to_list
                        @@ Array.slice rc.(i).(j) 1 (Array.length rc.(i).(j))
                      in
                      mk_bounds_of_coeffs_int norm_type ts lbrc ubrc berc)
             in
             (Set.Poly.union_list rfun_pos_neg_maps, Formula.and_of phis))
    in
    (Set.Poly.union_list rfun_pos_neg_maps, Formula.and_of phis)
  in
  let rfun_const_bounds =
    Formula.and_of
    @@ List.init nl ~f:(fun i ->
           Formula.and_of
           @@ List.init np ~f:(fun j ->
                  mk_bounds_of_const_int
                    rc.(i).(j).(0)
                    None ubrd
                    (Set.Poly.singleton Z.zero)))
  in
  let disc_pos_neg_map, disc_coeffs_bounds =
    let disc_pos_neg_maps, phis =
      List.unzip
      @@ List.init nl ~f:(fun i ->
             let disc_pos_neg_maps, phis =
               List.unzip
               @@ List.init
                    (if use_ifte then np - 1 else np)
                    ~f:(fun j ->
                      let disc_pos_neg_maps, phis =
                        List.unzip
                        @@ List.init ndc ~f:(fun k ->
                               let ts =
                                 Array.to_list
                                 @@ Array.slice
                                      dc.(i).(j).(k)
                                      1
                                      (Array.length dc.(i).(j).(k))
                               in
                               mk_bounds_of_coeffs_int norm_type ts lbdc ubdc
                                 bedc)
                      in
                      ( Set.Poly.union_list disc_pos_neg_maps,
                        Formula.and_of phis ))
             in
             (Set.Poly.union_list disc_pos_neg_maps, Formula.and_of phis))
    in
    (Set.Poly.union_list disc_pos_neg_maps, Formula.and_of phis)
  in
  let disc_const_bounds =
    Formula.and_of
    @@ List.init nl ~f:(fun i ->
           Formula.and_of
           @@ List.init
                (if use_ifte then np - 1 else np)
                ~f:(fun j ->
                  Formula.and_of
                  @@ List.init ndc ~f:(fun k ->
                         mk_bounds_of_const_int dc.(i).(j).(k).(0) None ubdd ds)))
  in
  let temp_params =
    let temp_params_fun =
      Set.Poly.of_list
      @@ List.map ~f:(Term.let_var >> fst)
      @@ (List.concat_map ~f:Array.to_list
         @@ List.concat_map ~f:Array.to_list
         @@ Array.to_list rc)
      @ List.concat_map ~f:Array.to_list
      @@ List.concat_map ~f:Array.to_list
      @@ List.concat_map ~f:Array.to_list
      @@ Array.to_list dc
    in
    merge
      [ rfun_pos_neg_map; disc_pos_neg_map; temp_params_fun; temp_params_quals ]
  in
  ( temp_params,
    hole_quals_map,
    tmpl,
    rfun_coeffs_bounds,
    rfun_const_bounds,
    disc_coeffs_bounds,
    disc_const_bounds )

let size_fun_apps =
  List.filter_map ~f:(function
    | v, T_dt.SDT dt ->
        Option.some @@ Datatype.app_size_fun dt (Term.mk_var v @@ T_dt.SDT dt)
    | _ -> None)

let gen_simplified_wf_predicate quals terms
    (shp, nl, ubrc, ubrd, ubdc, ubdd, ds) (norm_type, lbrc, lbdc, berc, bedc)
    params =
  assert (List.length params mod 2 = 0);
  let params_x, params_y = List.split_n params (List.length params / 2) in
  let x_terms, y_terms, _ =
    let txs = Set.Poly.of_list @@ List.map ~f:fst params_x in
    let tys = Set.Poly.of_list @@ List.map ~f:fst params_y in
    List.partition3_map ~f:(fun t ->
        let tvs = Term.tvs_of t in
        if Set.is_subset tvs ~of_:txs then `Fst t
        else if Set.is_subset tvs ~of_:tys then `Snd t
        else `Trd t)
    @@ size_fun_apps params
    @ List.filter terms ~f:T_irb.is_sirb
  in
  (* ToDo: does not hold for arbitrary terms *)
  assert (List.length x_terms = List.length y_terms);
  let irb_params = List.filter params ~f:(snd >> Term.is_irb_sort) in
  let size = List.length irb_params / 2 in
  let irb_params_x, irb_params_y = List.split_n irb_params size in
  let txs =
    List.map ~f:T_irb.to_int_if_rb (x_terms @ Term.of_sort_env irb_params_x)
  in
  let tys =
    List.map ~f:T_irb.to_int_if_rb (y_terms @ Term.of_sort_env irb_params_y)
  in
  let size = size + List.length x_terms in
  let np = List.length shp in
  let rc =
    Array.init np ~f:(fun _i ->
        Array.init nl ~f:(fun _j ->
            Array.init (size + 1) ~f:(fun _ ->
                Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt)))
  in
  let dc =
    Array.init np ~f:(fun i ->
        let ndc = List.nth_exn shp i in
        Array.init ndc ~f:(fun _j ->
            Array.init (size + 1) ~f:(fun _ ->
                Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt)))
  in
  let r_x i j =
    T_int.mk_sum
      rc.(i).(j).(0)
      (List.mapi ~f:(fun k -> T_int.mk_mult rc.(i).(j).(k + 1)) txs)
  in
  let r_y i j =
    T_int.mk_sum
      rc.(i).(j).(0)
      (List.mapi ~f:(fun k -> T_int.mk_mult rc.(i).(j).(k + 1)) tys)
  in
  let d_x i j =
    T_int.mk_sum
      dc.(i).(j).(0)
      (List.mapi ~f:(fun l -> T_int.mk_mult dc.(i).(j).(l + 1)) txs)
  in
  let d_y i j =
    T_int.mk_sum
      dc.(i).(j).(0)
      (List.mapi ~f:(fun l -> T_int.mk_mult dc.(i).(j).(l + 1)) tys)
  in
  let temp_params_quals, hole_quals_map, holes =
    let x2y = Formula.rename @@ tvar_map_of_sort_env_list params_x params_y in
    let quals = quals_over quals params_x in
    let temp_params_qualss, hole_quals_maps, holes =
      List.unzip3
      @@ List.init np ~f:(fun i ->
             let temp_params_quals, quals_x, hole =
               gen_hole_for_qualifiers (params, quals)
             in
             let quals_y =
               List.map quals_x ~f:(fun (b, (senv, q)) -> (b, (senv, x2y q)))
             in
             let hole_x_name = Ident.name_of_tvar hole ^ "_x" in
             let hole_y_name = Ident.name_of_tvar hole ^ "_y" in
             let hole_term_of name =
               Formula.mk_atom @@ Atom.pvar_app_of_senv (Ident.Pvar name) params
             in
             ( temp_params_quals,
               [
                 (Ident.Tvar hole_x_name, quals_x);
                 (Ident.Tvar hole_y_name, quals_y);
               ],
               (i, (hole_term_of hole_x_name, hole_term_of hole_y_name)) ))
    in
    (Set.Poly.union_list temp_params_qualss, List.concat hole_quals_maps, holes)
  in
  let hole_x i = fst @@ List.Assoc.find_exn ~equal:Stdlib.( = ) holes i in
  let hole_y i = snd @@ List.Assoc.find_exn ~equal:Stdlib.( = ) holes i in
  let disc_x i =
    let ndc = List.nth_exn shp i in
    Formula.and_of
    @@ hole_x i
       :: List.init ndc ~f:(fun j -> Formula.geq (d_x i j) (T_int.zero ()))
  in
  let disc_y i =
    let ndc = List.nth_exn shp i in
    Formula.and_of
    @@ hole_y i
       :: List.init ndc ~f:(fun j -> Formula.geq (d_y i j) (T_int.zero ()))
  in
  let tmpl =
    let d_y_geq_zero = Formula.or_of @@ List.init np ~f:(fun j -> disc_y j) in
    let ldec i j =
      Formula.or_of
      @@ List.init nl ~f:(fun k ->
             Formula.and_of
               [
                 Formula.geq (r_x i k) (T_int.zero ());
                 Formula.geq (r_x i k) (T_int.mk_add (r_y j k) (T_int.one ()));
                 Formula.and_of
                 @@ List.init k ~f:(fun l ->
                        Formula.or_of
                          [
                            Formula.and_of
                              [
                                Formula.leq
                                  (T_int.mk_add (r_x i l) (T_int.one ()))
                                  (T_int.zero ());
                                Formula.leq
                                  (T_int.mk_add (r_y j l) (T_int.one ()))
                                  (T_int.zero ());
                              ];
                            Formula.geq (r_x i l) (r_y j l);
                          ]);
               ])
    in
    let pdec =
      Formula.or_of
      @@ List.init np ~f:(fun i ->
             Formula.and_of
               [
                 disc_x i;
                 Formula.and_of
                 @@ List.init np ~f:(fun j ->
                        Formula.mk_imply (disc_y j) (ldec i j));
               ])
    in
    Formula.and_of [ d_y_geq_zero; pdec ]
  in
  let rfun_pos_neg_map, rfun_coeffs_bounds =
    let rfun_pos_neg_maps, phis =
      List.unzip
      @@ List.init np ~f:(fun i ->
             let rfun_pos_neg_maps, phis =
               List.unzip
               @@ List.init nl ~f:(fun j ->
                      let ts =
                        Array.to_list
                        @@ Array.slice rc.(i).(j) 1 (Array.length rc.(i).(j))
                      in
                      mk_bounds_of_coeffs_int norm_type ts lbrc ubrc berc)
             in
             (Set.Poly.union_list rfun_pos_neg_maps, Formula.and_of phis))
    in
    (Set.Poly.union_list rfun_pos_neg_maps, Formula.and_of phis)
  in
  let rfun_const_bounds =
    Formula.and_of
    @@ List.init np ~f:(fun i ->
           Formula.and_of
           @@ List.init nl ~f:(fun j ->
                  mk_bounds_of_const_int
                    rc.(i).(j).(0)
                    None ubrd
                    (Set.Poly.singleton Z.zero)))
  in
  let disc_pos_neg_map, disc_coeffs_bounds =
    let disc_pos_neg_maps, phis =
      List.unzip
      @@ List.init np ~f:(fun i ->
             let disc_pos_neg_maps, phis =
               let ndc = List.nth_exn shp i in
               List.unzip
               @@ List.init ndc ~f:(fun j ->
                      let ts =
                        Array.to_list
                        @@ Array.slice dc.(i).(j) 1 (Array.length dc.(i).(j))
                      in
                      mk_bounds_of_coeffs_int norm_type ts lbdc ubdc bedc)
             in
             (Set.Poly.union_list disc_pos_neg_maps, Formula.and_of phis))
    in
    (Set.Poly.union_list disc_pos_neg_maps, Formula.and_of phis)
  in
  let disc_const_bounds =
    Formula.and_of
    @@ List.init np ~f:(fun i ->
           let ndc = List.nth_exn shp i in
           Formula.and_of
           @@ List.init ndc ~f:(fun j ->
                  mk_bounds_of_const_int dc.(i).(j).(0) None ubdd ds))
  in
  let temp_params =
    let temp_params_fun =
      Set.Poly.of_list
      @@ List.map ~f:(Term.let_var >> fst)
      @@ (List.concat_map ~f:Array.to_list
         @@ List.concat_map ~f:Array.to_list
         @@ Array.to_list rc)
      @ List.concat_map ~f:Array.to_list
      @@ List.concat_map ~f:Array.to_list
      @@ Array.to_list dc
    in
    merge
      [ rfun_pos_neg_map; disc_pos_neg_map; temp_params_fun; temp_params_quals ]
  in
  ( temp_params,
    hole_quals_map,
    tmpl,
    rfun_coeffs_bounds,
    rfun_const_bounds,
    disc_coeffs_bounds,
    disc_const_bounds )

let gen_simplified_nwf_predicate quals terms (rcs, dcs, qds)
    (shp, nl, ubrc, ubrd, ubdc, ubdd, ds) (norm_type, lbrc, lbdc, berc, bedc)
    (params, (idxl : Ident.tvar), params_x, (idxr : Ident.tvar), params_y) =
  let find_and_update tbl key ~f =
    match Hashtbl.Poly.find tbl key with
    | Some data -> data
    | None ->
        let data = f key in
        Hashtbl.Poly.add_exn tbl ~key ~data;
        data
  in
  let terms_with terms params =
    size_fun_apps params @ Term.of_sort_env params @ terms_over terms params
  in
  let d_terms = List.filter ~f:T_int.is_sint @@ terms_with terms params in
  let rx_terms, ry_terms =
    ( List.filter ~f:T_int.is_sint @@ terms_with terms params_x,
      List.filter ~f:T_int.is_sint @@ terms_with terms params_y )
  in
  let rx_quals = quals_over quals (params @ params_x) in
  let ry_quals = quals_over quals (params @ params_y) in
  let d_size = List.length d_terms in
  let rx_size, ry_size = (List.length rx_terms, List.length ry_terms) in
  let ddx_size, ddy_size = (List.length rx_quals, List.length ry_quals) in
  let np = List.length shp in
  let rc_array size =
    Array.init np ~f:(fun _i ->
        Array.init nl ~f:(fun _j ->
            Array.init (size + 1) ~f:(fun _ ->
                Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt)))
  in
  let dc_array size =
    Array.init np ~f:(fun i ->
        let ndc = List.nth_exn shp i in
        Array.init ndc ~f:(fun _j ->
            Array.init (size + 1) ~f:(fun _ ->
                Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt)))
  in
  let qd_array size =
    Array.init np ~f:(fun _ ->
        Array.init size ~f:(fun _ ->
            Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt))
  in
  let rc_x =
    find_and_update rcs idxl ~f:(fun _ -> rc_array @@ (rx_size + d_size))
  in
  let rc_y =
    find_and_update rcs idxr ~f:(fun _ -> rc_array @@ (ry_size + d_size))
  in
  let dc_x =
    find_and_update dcs idxl ~f:(fun _ -> dc_array @@ (rx_size + d_size))
  in
  let dc_y =
    find_and_update dcs idxr ~f:(fun _ -> dc_array @@ (ry_size + d_size))
  in
  let qd_x = find_and_update qds idxl ~f:(fun _ -> qd_array ddx_size) in
  let qd_y = find_and_update qds idxr ~f:(fun _ -> qd_array ddy_size) in
  let r_x i j =
    T_int.mk_sum
      rc_x.(i).(j).(0)
      (List.mapi
         ~f:(fun k -> T_int.mk_mult rc_x.(i).(j).(k + 1))
         (d_terms @ rx_terms))
  in
  let r_y i j =
    T_int.mk_sum
      rc_y.(i).(j).(0)
      (List.mapi
         ~f:(fun k -> T_int.mk_mult rc_y.(i).(j).(k + 1))
         (d_terms @ ry_terms))
  in
  let d_x i j =
    T_int.mk_sum
      dc_x.(i).(j).(0)
      (List.mapi
         ~f:(fun l -> T_int.mk_mult dc_x.(i).(j).(l + 1))
         (d_terms @ rx_terms))
  in
  let d_y i j =
    T_int.mk_sum
      dc_y.(i).(j).(0)
      (List.mapi
         ~f:(fun l -> T_int.mk_mult dc_y.(i).(j).(l + 1))
         (d_terms @ ry_terms))
  in
  let temp_params_quals, hole_quals_map, holes =
    let x2y = Formula.rename @@ tvar_map_of_sort_env_list params_x params_y in
    let temp_params_qualss, hole_quals_maps, holes =
      List.unzip3
      @@ List.init np ~f:(fun i ->
             let params' = params @ params_x @ params_y in
             let temp_params_quals_x, quals_x, hole_x =
               gen_hole_for_qualifiers ~qds:(Some qd_x.(i)) (params', rx_quals)
             in
             let temp_params_quals_y, quals_y, hole_y =
               if Stdlib.(idxl = idxr) then
                 let quals_y =
                   List.map quals_x ~f:(fun (b, (senv, q)) ->
                       (b, (senv, x2y q)))
                 in
                 (temp_params_quals_x, quals_y, hole_x)
               else
                 gen_hole_for_qualifiers ~qds:(Some qd_y.(i)) (params', ry_quals)
             in
             let hole_x_name = Ident.name_of_tvar hole_x ^ "_x" in
             let hole_y_name = Ident.name_of_tvar hole_y ^ "_y" in
             let hole_term_of name params =
               Formula.mk_atom @@ Atom.pvar_app_of_senv (Ident.Pvar name) params
             in
             ( Set.union temp_params_quals_x temp_params_quals_y,
               [
                 (Ident.Tvar hole_x_name, quals_x);
                 (Ident.Tvar hole_y_name, quals_y);
               ],
               ( i,
                 ( hole_term_of hole_x_name params',
                   hole_term_of hole_y_name params' ) ) ))
    in
    (Set.Poly.union_list temp_params_qualss, List.concat hole_quals_maps, holes)
  in
  let hole_x i = fst @@ List.Assoc.find_exn ~equal:Stdlib.( = ) holes i in
  let hole_y i = snd @@ List.Assoc.find_exn ~equal:Stdlib.( = ) holes i in
  let disc_x i =
    let ndc = List.nth_exn shp i in
    Formula.and_of
    @@ hole_x i
       :: List.init ndc ~f:(fun j -> Formula.geq (d_x i j) (T_int.zero ()))
  in
  let disc_y i =
    let ndc = List.nth_exn shp i in
    Formula.and_of
    @@ hole_y i
       :: List.init ndc ~f:(fun j -> Formula.geq (d_y i j) (T_int.zero ()))
  in
  let tmpl =
    let d_y_geq_zero = Formula.or_of @@ List.init np ~f:(fun j -> disc_y j) in
    let ldec i j =
      Formula.or_of
      @@ List.init nl ~f:(fun k ->
             Formula.and_of
               [
                 Formula.geq (r_x i k) (T_int.zero ());
                 Formula.geq (r_x i k) (T_int.mk_add (r_y j k) (T_int.one ()));
                 Formula.and_of
                 @@ List.init k ~f:(fun l ->
                        Formula.or_of
                          [
                            Formula.and_of
                              [
                                Formula.leq
                                  (T_int.mk_add (r_x i l) (T_int.one ()))
                                  (T_int.zero ());
                                Formula.leq
                                  (T_int.mk_add (r_y j l) (T_int.one ()))
                                  (T_int.zero ());
                              ];
                            Formula.geq (r_x i l) (r_y j l);
                          ]);
               ])
    in
    let pdec =
      Formula.or_of
      @@ List.init np ~f:(fun i ->
             Formula.and_of
               [
                 disc_x i;
                 Formula.and_of
                 @@ List.init np ~f:(fun j ->
                        Formula.mk_imply (disc_y j) (ldec i j));
               ])
    in
    Formula.and_of [ d_y_geq_zero; pdec ]
  in
  let rfun_pos_neg_map, rfun_coeffs_bounds =
    let rfun_pos_neg_maps, phis =
      List.unzip
      @@ List.init np ~f:(fun i ->
             let rfun_pos_neg_maps_x, phis_x =
               List.unzip
               @@ List.init nl ~f:(fun j ->
                      let ts =
                        Array.to_list
                        @@ Array.slice
                             rc_x.(i).(j)
                             1
                             (Array.length rc_x.(i).(j))
                      in
                      mk_bounds_of_coeffs_int norm_type ts lbrc ubrc berc)
             in
             let rfun_pos_neg_maps_y, phis_y =
               if Stdlib.(idxl = idxr) then ([], [])
               else
                 List.unzip
                 @@ List.init nl ~f:(fun j ->
                        let ts =
                          Array.to_list
                          @@ Array.slice
                               rc_y.(i).(j)
                               1
                               (Array.length rc_y.(i).(j))
                        in
                        mk_bounds_of_coeffs_int norm_type ts lbrc ubrc berc)
             in
             ( Set.Poly.union_list (rfun_pos_neg_maps_x @ rfun_pos_neg_maps_y),
               Formula.and_of (phis_x @ phis_y) ))
    in
    (Set.Poly.union_list rfun_pos_neg_maps, Formula.and_of phis)
  in
  let rfun_const_bounds =
    Formula.and_of
    @@ List.init np ~f:(fun i ->
           Formula.and_of
           @@ List.init nl ~f:(fun j ->
                  mk_bounds_of_const_int
                    rc_x.(i).(j).(0)
                    None ubrd
                    (Set.Poly.singleton Z.zero)))
    @
    if Stdlib.(idxl = idxr) then []
    else
      List.init np ~f:(fun i ->
          Formula.and_of
          @@ List.init nl ~f:(fun j ->
                 mk_bounds_of_const_int
                   rc_y.(i).(j).(0)
                   None ubrd
                   (Set.Poly.singleton Z.zero)))
  in
  let disc_pos_neg_map, disc_coeffs_bounds =
    let disc_pos_neg_maps, phis =
      List.unzip
      @@ List.init np ~f:(fun i ->
             let disc_pos_neg_maps_x, phis_x =
               let ndc = List.nth_exn shp i in
               List.unzip
               @@ List.init ndc ~f:(fun j ->
                      let ts =
                        Array.to_list
                        @@ Array.slice
                             dc_x.(i).(j)
                             1
                             (Array.length dc_x.(i).(j))
                      in
                      mk_bounds_of_coeffs_int norm_type ts lbdc ubdc bedc)
             in
             let disc_pos_neg_maps_y, phis_y =
               if Stdlib.(idxl = idxr) then ([], [])
               else
                 let ndc = List.nth_exn shp i in
                 List.unzip
                 @@ List.init ndc ~f:(fun j ->
                        let ts =
                          Array.to_list
                          @@ Array.slice
                               dc_y.(i).(j)
                               1
                               (Array.length dc_y.(i).(j))
                        in
                        mk_bounds_of_coeffs_int norm_type ts lbdc ubdc bedc)
             in
             ( Set.Poly.union_list (disc_pos_neg_maps_x @ disc_pos_neg_maps_y),
               Formula.and_of (phis_x @ phis_y) ))
    in
    (Set.Poly.union_list disc_pos_neg_maps, Formula.and_of phis)
  in
  let disc_const_bounds =
    Formula.and_of
    @@ List.init np ~f:(fun i ->
           let ndc = List.nth_exn shp i in
           Formula.and_of
           @@ List.init ndc ~f:(fun j ->
                  mk_bounds_of_const_int dc_x.(i).(j).(0) None ubdd ds))
    @
    if Stdlib.(idxl = idxr) then []
    else
      List.init np ~f:(fun i ->
          let ndc = List.nth_exn shp i in
          Formula.and_of
          @@ List.init ndc ~f:(fun j ->
                 mk_bounds_of_const_int dc_y.(i).(j).(0) None ubdd ds))
  in
  let temp_params =
    let temp_params_fun =
      Set.Poly.of_list
      @@ List.map ~f:(Term.let_var >> fst)
      @@ (List.concat_map ~f:Array.to_list
         @@ List.concat_map ~f:Array.to_list
         @@ Array.to_list rc_x)
      @ (List.concat_map ~f:Array.to_list
        @@ List.concat_map ~f:Array.to_list
        @@ Array.to_list rc_y)
      @ (List.concat_map ~f:Array.to_list
        @@ List.concat_map ~f:Array.to_list
        @@ Array.to_list dc_x)
      @ List.concat_map ~f:Array.to_list
      @@ List.concat_map ~f:Array.to_list
      @@ Array.to_list dc_y
    in
    merge
      [ rfun_pos_neg_map; disc_pos_neg_map; temp_params_fun; temp_params_quals ]
  in
  ( temp_params,
    hole_quals_map,
    tmpl,
    rfun_coeffs_bounds,
    rfun_const_bounds,
    disc_coeffs_bounds,
    disc_const_bounds )
