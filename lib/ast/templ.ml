open Core
open Common.Ext
open Common.Combinator
open LogicOld

let avoid_ite_const = false
let avoid_ite_coeffs = false

let gen_params_0d size =
  Array.init size ~f:(fun _ ->
      Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt)

let gen_params_1d d1 size = Array.init d1 ~f:(fun _ -> gen_params_0d size)
let gen_params_2d d1 d2 size = Array.init d1 ~f:(fun _ -> gen_params_1d d2 size)

let gen_params_2d_flex d1 shp size =
  Array.init d1 ~f:(fun i -> gen_params_1d (List.nth_exn shp i) size)

let gen_params_2d_flex_variant d1 shp size =
  Array.init (max 1 d1) ~f:(fun i ->
      gen_params_1d (if d1 >= 1 then List.nth_exn shp i else 1) size)

let gen_params_3d_flex d1 d2 shp size =
  Array.init d1 ~f:(fun _ -> gen_params_2d_flex d2 shp size)

let mk_const_bounds_int t lb ub seeds =
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

let mk_const_bounds_real t lb ub seeds =
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

let mk_coeffs_bounds_of_int norm_type ts lb ub be =
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

let mk_coeffs_bounds_of_real norm_type ts lb ub be =
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

let quals_over quals params =
  let vs = Set.Poly.of_list @@ List.map ~f:fst params in
  List.filter quals ~f:(fun q -> Set.is_subset (Formula.tvs_of q) ~of_:vs)

let terms_over terms params =
  let vs = Set.Poly.of_list @@ List.map ~f:fst params in
  List.filter terms ~f:(fun t -> Set.is_subset (Term.tvs_of t) ~of_:vs)

type hole_qualifiers_map_elem = (Ident.tvar * (sort_env_list * Formula.t)) list
type hole_qualifiers_map = (Ident.tvar * hole_qualifiers_map_elem) list

let mk_pvar_app name params =
  Formula.mk_atom @@ Atom.pvar_app_of_senv (Ident.Pvar name) params

let gen_hole_for_qualifiers ?(qds = None) (params, quals) =
  let hole = Ident.mk_fresh_tvar ~prefix:(Some "hole") () in
  if List.is_empty quals then (Set.Poly.empty, [], hole)
  else
    let qds =
      match qds with
      | Some qds -> qds
      | None -> gen_params_0d (List.length quals)
    in
    let templ_params, templ_param_qual_map =
      List.unzip
      @@ List.mapi quals ~f:(fun i qual ->
             let (templ_param, sort), _ = Term.let_var qds.(i) in
             if false then
               print_endline
               @@ sprintf "%s |-> %s"
                    (Ident.name_of_tvar templ_param)
                    (Formula.str_of qual);
             ((templ_param, sort), (templ_param, (params, qual))))
    in
    ( Set.Poly.of_list templ_params,
      (templ_param_qual_map : hole_qualifiers_map_elem),
      hole )

let qual_env_of_hole_map (hole_qualifiers_map : hole_qualifiers_map) =
  List.map hole_qualifiers_map ~f:(fun (_, quals) ->
      List.fold quals ~init:Map.Poly.empty ~f:(fun acc (var, (_, phi)) ->
          Map.Poly.add_exn acc ~key:phi ~data:var))

(** Templates for conjunctive boolean combination of qualifiers *)

let gen_from_qualifiers (params, quals) =
  Logic.Term.mk_lambda params
  @@ Logic.ExtTerm.of_old_formula @@ Formula.and_of
  @@ List.concat_map quals ~f:(fun (templ_param, (_, params', qual)) ->
         let qual =
           let ren = ren_of_sort_env_list params' params in
           Formula.rename ren qual
         in
         let key = Term.mk_var templ_param T_int.SInt in
         let pos = Formula.mk_imply (Formula.gt key (T_int.zero ())) qual in
         let neg =
           Formula.mk_imply
             (Formula.lt key (T_int.zero ()))
             (Formula.mk_neg qual)
         in
         [ pos; neg ])

(** Templates for function variables *)

type templ_func = {
  templ_params : Logic.sort_env_map;
  hole_quals_map : hole_qualifiers_map;
  func : Term.t;
  expr_params_bounds : Formula.t;
  expr_coeffs_bounds : Formula.t;
  expr_const_bounds : Formula.t;
  cond_coeffs_bounds : Formula.t;
  cond_const_bounds : Formula.t;
}

let ite_templ cond templ1 templ2 =
  {
    templ_params = Map.force_merge templ1.templ_params templ2.templ_params;
    hole_quals_map = templ1.hole_quals_map @ templ2.hole_quals_map;
    func = T_bool.ifte cond templ1.func templ2.func;
    expr_params_bounds =
      Formula.mk_and templ1.expr_params_bounds templ2.expr_params_bounds;
    expr_coeffs_bounds =
      Formula.mk_and templ1.expr_coeffs_bounds templ2.expr_coeffs_bounds;
    expr_const_bounds =
      Formula.mk_and templ1.expr_const_bounds templ2.expr_const_bounds;
    cond_coeffs_bounds =
      Formula.mk_and templ1.cond_coeffs_bounds templ2.cond_coeffs_bounds;
    cond_const_bounds =
      Formula.mk_and templ1.cond_const_bounds templ2.cond_const_bounds;
  }

type fun_tfp = {
  terms : Term.t list (*(Term.t * Sort.t) list*);
  quals : Formula.t list;
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

type fun_tfsp = {
  lbec : Z.t option;
  lbcc : Z.t option;
  beec : Z.t option;
  becc : Z.t option;
}

let gen_cond_and_exps_of_fun tf_params tf_sub_params params (vret_opt, sret) =
  let nd = (*ToDo*) max 1 (List.length tf_params.shp) in

  let txs =
    List.map ~f:T_irb.to_int_if_rb
    @@ Term.of_sort_env (List.filter params ~f:(snd >> Term.is_irb_sort))
    @ List.filter tf_params.terms ~f:T_irb.is_sirb
  in
  let ec, dc =
    ( gen_params_0d nd,
      gen_params_2d_flex (nd - 1) tf_params.shp (List.length txs + 1) )
  in
  let r_x i =
    List.fold_right
      (List.mapi tf_params.terms ~f:(fun i t -> (i, t)))
      ~init:(Term.mk_dummy sret)
      ~f:(fun (j, t1) t2 ->
        T_bool.ifte (Formula.eq ec.(i) (T_int.from_int j)) t1 t2)
  in
  let d_x i j =
    T_int.mk_sum
      dc.(i).(j).(0)
      (List.mapi ~f:(fun k -> T_int.mk_mul dc.(i).(j).(k + 1)) txs)
  in
  let templ_params_quals, hole_quals_map, func =
    let rest, last = List.rest_last (List.init nd ~f:(fun i -> (i, r_x i))) in
    List.fold_right rest
      ~init:(Set.Poly.empty, [], snd last)
      ~f:(fun (i, t1) (templ_params_quals', hole_quals_map, t2) ->
        let params =
          match vret_opt with
          | None -> params
          | Some vret -> params @ [ (vret, sret) ]
        in
        let templ_params_quals, quals, hole =
          gen_hole_for_qualifiers (params, tf_params.quals)
        in
        ( Set.union templ_params_quals templ_params_quals',
          (hole, quals) :: hole_quals_map,
          let cond =
            Formula.and_of
            @@ mk_pvar_app (Ident.name_of_tvar hole) params
               :: List.init (List.nth_exn tf_params.shp i) ~f:(fun j ->
                      Formula.geq (d_x i j) (T_int.zero ()))
          in
          T_bool.ifte cond t1 t2 ))
  in
  let expr_params_map, expr_params_bounds =
    let params, bounds =
      List.unzip
      @@ List.init nd ~f:(fun i ->
             ( fst @@ Term.let_var ec.(i),
               [
                 Formula.geq ec.(i) (T_int.zero ());
                 Formula.lt ec.(i)
                   (T_int.from_int (List.length tf_params.terms));
               ] ))
    in
    (Set.Poly.of_list params, Formula.and_of @@ List.concat bounds)
  in
  let cond_pos_neg_map, cond_coeffs_bounds =
    let cond_pos_neg_mapss, phiss =
      List.unzip
      @@ List.init (nd - 1) ~f:(fun i ->
             List.unzip
             @@ List.init (List.nth_exn tf_params.shp i) ~f:(fun j ->
                    mk_coeffs_bounds_of_int 1
                      (Array.to_list
                      @@ Array.slice dc.(i).(j) 1 (Array.length dc.(i).(j)))
                      tf_sub_params.lbcc tf_params.ubcc tf_sub_params.becc))
    in
    ( Set.Poly.union_list @@ List.map ~f:Set.Poly.union_list cond_pos_neg_mapss,
      Formula.and_of @@ List.map ~f:Formula.and_of phiss )
  in
  let cond_const_bounds =
    Formula.and_of
    @@ List.init (nd - 1) ~f:(fun i ->
           Formula.and_of
           @@ List.init (List.nth_exn tf_params.shp i) ~f:(fun j ->
                  mk_const_bounds_int
                    dc.(i).(j).(0)
                    None tf_params.ubcd tf_params.cs))
  in
  let templ_params =
    let templ_params_fun =
      Set.Poly.of_list
      @@ List.map ~f:(Term.let_var >> fst)
      @@ List.concat_map ~f:Array.to_list
      @@ List.concat_map ~f:Array.to_list
      @@ Array.to_list dc
    in
    Map.of_set_exn @@ Logic.of_old_sort_env_set
    @@ Set.Poly.union_list
         [
           cond_pos_neg_map;
           templ_params_fun;
           templ_params_quals;
           expr_params_map;
         ]
  in
  {
    templ_params;
    hole_quals_map;
    func;
    expr_params_bounds;
    expr_coeffs_bounds = Formula.mk_true () (*Dummy*);
    expr_const_bounds = Formula.mk_true () (*Dummy*);
    cond_coeffs_bounds;
    cond_const_bounds;
  }

let gen_bool_fun tf_params tf_sub_params params (vret_opt, sret) : templ_func =
  let quals =
    match vret_opt with
    | None -> tf_params.quals
    | Some vret ->
        List.filter tf_params.quals ~f:(fun qual ->
            not @@ Set.mem (Formula.tvs_of qual) vret)
  in
  let terms =
    (* ToDo: tf_params.terms is not used *)
    List.map quals ~f:(fun q -> T_bool.of_formula q)
  in
  gen_cond_and_exps_of_fun
    { tf_params with terms; quals }
    tf_sub_params params (vret_opt, sret)

let gen_int_fun tf_params tf_sub_params params (vret_opt, sret) : templ_func =
  let nd = List.length tf_params.shp in
  let quals, ret_terms =
    match vret_opt with
    | None -> (tf_params.quals, [])
    | Some vret ->
        let quals, ret_quals =
          List.partition_tf tf_params.quals ~f:(fun qual ->
              not @@ Set.mem (Formula.tvs_of qual) vret)
        in
        if false then
          print_endline
          @@ sprintf "[%s] quals:\n" (Ident.name_of_tvar vret)
          ^ String.concat_map_list ~sep:"\n" ret_quals ~f:Formula.str_of;
        let ret_terms =
          List.mapi ~f:(fun i t -> (i, t))
          @@ List.filter_map ret_quals ~f:(fun phi ->
                 AffineTerm.extract_affine_term_from vret
                   (Evaluator.simplify_term >> Normalizer.normalize_term)
                   Normalizer.normalize phi)
        in
        (quals, ret_terms)
  in
  let ec = gen_params_0d (max 1 nd) in
  let gen_expr i exp_x =
    List.fold_right ret_terms ~init:exp_x ~f:(fun (j, t1) t2 ->
        T_bool.ifte (Formula.eq ec.(i) (T_int.from_int j)) t1 t2)
  in
  let expr_params_map, expr_params_bounds =
    if List.is_empty ret_terms then (Set.Poly.empty, Formula.mk_true ())
    else
      let params, bounds =
        List.unzip
        @@ List.init (Array.length ec) ~f:(fun i ->
               ( fst @@ Term.let_var ec.(i),
                 [
                   Formula.geq ec.(i) (T_int.zero ());
                   Formula.leq ec.(i) (T_int.from_int (List.length ret_terms));
                 ] ))
      in
      (Set.Poly.of_list params, Formula.and_of @@ List.concat bounds)
  in
  if nd <= 0 then
    {
      templ_params = Map.of_set_exn @@ Logic.of_old_sort_env_set expr_params_map;
      hole_quals_map = [];
      func = gen_expr 0 (T_int.zero ());
      expr_params_bounds;
      expr_coeffs_bounds = Formula.mk_true ();
      expr_const_bounds = Formula.mk_true ();
      cond_coeffs_bounds = Formula.mk_true ();
      cond_const_bounds = Formula.mk_true ();
    }
  else
    let txs =
      List.map ~f:T_irb.to_int_if_rb
      @@ Term.of_sort_env (List.filter params ~f:(snd >> Term.is_irb_sort))
      @ List.filter tf_params.terms ~f:T_irb.is_sirb
    in
    let rc, dc =
      ( gen_params_1d (max 1 nd) (List.length txs + 1),
        gen_params_2d_flex_variant (nd - 1) tf_params.shp (List.length txs + 1)
      )
    in
    let r_x i =
      T_int.mk_sum
        rc.(i).(0)
        (List.mapi ~f:(fun j -> T_int.mk_mul rc.(i).(j + 1)) txs)
    in
    let d_x i j =
      T_int.mk_sum
        dc.(i).(j).(0)
        (List.mapi ~f:(fun k -> T_int.mk_mul dc.(i).(j).(k + 1)) txs)
    in
    let templ_params_quals, hole_quals_map, func =
      let rest, last = List.rest_last (List.init nd ~f:(fun i -> (i, r_x i))) in
      List.fold_right rest
        ~init:(Set.Poly.empty, [], uncurry gen_expr last)
        ~f:(fun (i, t1) (templ_params_quals', hole_quals_map, t2) ->
          let params =
            match vret_opt with
            | None -> params
            | Some vret -> params @ [ (vret, sret) ]
          in
          let templ_params_quals, quals, hole =
            gen_hole_for_qualifiers (params, quals)
          in
          ( Set.union templ_params_quals templ_params_quals',
            (hole, quals) :: hole_quals_map,
            let cond =
              Formula.and_of
              @@ mk_pvar_app (Ident.name_of_tvar hole) params
                 :: List.init (List.nth_exn tf_params.shp i) ~f:(fun j ->
                        Formula.geq (d_x i j) (T_int.zero ()))
            in
            T_bool.ifte cond (gen_expr i t1) t2 ))
    in
    let expr_pos_neg_map, expr_coeffs_bounds =
      let expr_pos_neg_maps, phis =
        List.unzip
        @@ List.init nd ~f:(fun i ->
               mk_coeffs_bounds_of_int 1
                 (Array.to_list @@ Array.slice rc.(i) 1 (Array.length rc.(i)))
                 tf_sub_params.lbec tf_params.ubec tf_sub_params.beec)
      in
      (Set.Poly.union_list expr_pos_neg_maps, Formula.and_of phis)
    in
    let expr_const_bounds =
      Formula.and_of
      @@ List.init nd ~f:(fun i ->
             mk_const_bounds_int rc.(i).(0) None tf_params.ubed tf_params.es)
    in
    let cond_pos_neg_map, cond_coeffs_bounds =
      let cond_pos_neg_mapss, phiss =
        List.unzip
        @@ List.init (nd - 1) ~f:(fun i ->
               List.unzip
               @@ List.init (List.nth_exn tf_params.shp i) ~f:(fun j ->
                      mk_coeffs_bounds_of_int 1
                        (Array.to_list
                        @@ Array.slice dc.(i).(j) 1 (Array.length dc.(i).(j)))
                        tf_sub_params.lbcc tf_params.ubcc tf_sub_params.becc))
      in
      ( Set.Poly.union_list @@ List.map ~f:Set.Poly.union_list cond_pos_neg_mapss,
        Formula.and_of @@ List.map ~f:Formula.and_of phiss )
    in
    let cond_const_bounds =
      Formula.and_of
      @@ List.init (nd - 1) ~f:(fun i ->
             Formula.and_of
             @@ List.init (List.nth_exn tf_params.shp i) ~f:(fun j ->
                    mk_const_bounds_int
                      dc.(i).(j).(0)
                      None tf_params.ubcd tf_params.cs))
    in
    let templ_params =
      let templ_params_fun =
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
             templ_params_fun;
             templ_params_quals;
           ]
    in
    {
      templ_params;
      hole_quals_map;
      func;
      expr_params_bounds;
      expr_coeffs_bounds;
      expr_const_bounds;
      cond_coeffs_bounds;
      cond_const_bounds;
    }

let gen_real_fun tf_params tf_sub_params params ret =
  let template = gen_int_fun tf_params tf_sub_params params ret in
  { template with func = T_irb.mk_int_to_real template.func }

let gen_bv_fun tf_params tf_sub_params params ret =
  let template = gen_int_fun tf_params tf_sub_params params ret in
  let size = match ret with _, T_bv.SBV size -> size | _ -> None in
  { template with func = T_irb.mk_int_to_bv ~size template.func }

let gen_array_fun _tf_params _tf_sub_params _params (_vret_opt, sret) :
    templ_func =
  (*ToDo*)
  {
    templ_params = Map.Poly.empty;
    hole_quals_map = [];
    func = Term.mk_dummy sret;
    expr_params_bounds = Formula.mk_true ();
    expr_coeffs_bounds = Formula.mk_true ();
    expr_const_bounds = Formula.mk_true ();
    cond_coeffs_bounds = Formula.mk_true ();
    cond_const_bounds = Formula.mk_true ();
  }

let gen_dt_fun tf_params tf_sub_params params (vret_opt, sret) : templ_func =
  let quals =
    match vret_opt with
    | None -> tf_params.quals
    | Some vret ->
        List.filter tf_params.quals ~f:(fun qual ->
            not @@ Set.mem (Formula.tvs_of qual) vret)
  in
  let int_terms =
    List.dedup_and_sort ~compare:Stdlib.compare
    @@ List.filter ~f:T_int.is_sint
    @@ Term.of_sort_env params
    @ terms_over tf_params.terms params
  in
  let dc = gen_params_1d tf_params.ext (List.length int_terms + 1) in
  let ext_params_map =
    Set.Poly.of_list @@ List.concat
    @@ List.init tf_params.ext ~f:(fun i ->
           List.init
             (List.length int_terms + 1)
             ~f:(fun j -> fst @@ Term.let_var dc.(i).(j)))
  in
  let terms =
    Set.to_list
    @@ Datatype.enum_cons_terms tf_params.depth sret
    @@ Set.Poly.of_list
    @@ List.append (Term.of_sort_env params)
    @@ List.init tf_params.ext ~f:(fun i ->
           T_int.mk_sum dc.(i).(0)
           @@ List.mapi int_terms ~f:(fun j -> T_int.mk_mul dc.(i).(j + 1)))
  in
  let template =
    gen_cond_and_exps_of_fun
      { tf_params with terms; quals }
      tf_sub_params params (vret_opt, sret)
  in
  let expr_const_bounds =
    match tf_params.ubed with
    | Some ubed ->
        Formula.and_of
        @@ List.init tf_params.ext ~f:(fun i ->
               Formula.leq (T_int.mk_abs dc.(i).(0)) (T_int.mk_int ubed))
    | _ -> Formula.mk_true ()
  in
  let expr_coeffs_bounds =
    match tf_params.ubec with
    | Some ubec ->
        Formula.and_of
        @@ List.init tf_params.ext ~f:(fun i ->
               Formula.leq
                 (Array.foldi dc.(i) ~init:(T_int.zero ()) ~f:(fun j acc c ->
                      if j = 0 then acc else T_int.mk_add acc @@ T_int.mk_abs c))
                 (T_int.mk_int ubec))
    | _ -> Formula.mk_true ()
  in
  let templ_params =
    Map.force_merge template.templ_params
    @@ Map.of_set_exn
    @@ Logic.of_old_sort_env_set ext_params_map
  in
  { template with templ_params; expr_coeffs_bounds; expr_const_bounds }

let gen_prop_fun ~is_integ tf_params tf_sub_params params (vret, sret) :
    templ_func =
  let nd = List.length tf_params.shp in
  if nd <= 0 then
    {
      templ_params = Map.Poly.empty;
      hole_quals_map = [];
      func = T_int.zero ();
      expr_params_bounds = Formula.mk_true ();
      expr_coeffs_bounds = Formula.mk_true ();
      expr_const_bounds = Formula.mk_true ();
      cond_coeffs_bounds = Formula.mk_true ();
      cond_const_bounds = Formula.mk_true ();
    }
  else
    let txs =
      List.map ~f:T_irb.to_real_if_int
      @@ Term.of_sort_env (List.filter params ~f:(snd >> Term.is_ir_sort))
      @
      if is_integ then []
      else List.filter tf_params.terms ~f:T_irb.is_sint_sreal
    in
    let rc, dc =
      ( gen_params_1d (max 1 nd) (List.length txs + 1),
        gen_params_2d_flex_variant (nd - 1) tf_params.shp
          (if is_integ then List.length txs else List.length txs + 1) )
    in
    let r_x i =
      (if is_integ then Fn.id else T_real.mk_rabs ~info:Dummy)
      @@ T_real.mk_rsum
           (T_irb.mk_int_to_real rc.(i).(0))
           (List.mapi txs ~f:(fun j t ->
                T_real.mk_rmul (T_irb.mk_int_to_real rc.(i).(j + 1)) t))
    in
    let d_x i j =
      T_real.mk_rsum
        (T_irb.mk_int_to_real dc.(i).(j).(0))
        (List.mapi ~f:(fun k ->
             T_real.mk_rmul (T_irb.mk_int_to_real dc.(i).(j).(k + 1)))
        @@ if is_integ then List.initial txs else txs)
    in
    let templ_params_quals, hole_quals_map, func =
      let rest, last = List.rest_last (List.init nd ~f:(fun i -> (i, r_x i))) in
      let quals =
        List.filter tf_params.quals ~f:(fun qual ->
            let tvs = Formula.tvs_of qual in
            (not @@ Set.mem tvs vret)
            &&
            if is_integ then
              not @@ Set.mem tvs @@ fst @@ fst @@ Term.let_var
              @@ List.last_exn txs
            else true)
      in
      List.fold_right rest
        ~init:(Set.Poly.empty, [], snd last)
        ~f:(fun (i, t1) (templ_params_quals', hole_quals_map, t2) ->
          let params = params @ [ (vret, sret) ] in
          let templ_params_quals, quals, hole =
            gen_hole_for_qualifiers (params, quals)
          in
          ( Set.union templ_params_quals templ_params_quals',
            (hole, quals) :: hole_quals_map,
            let cond =
              Formula.and_of
              @@ mk_pvar_app (Ident.name_of_tvar hole) params
                 :: List.init (List.nth_exn tf_params.shp i) ~f:(fun j ->
                        Formula.geq (d_x i j) (T_real.rzero ()))
            in
            T_bool.ifte cond t1 t2 ))
    in
    let expr_pos_neg_map, expr_coeffs_bounds =
      let expr_pos_neg_maps, phis =
        List.unzip
        @@ List.init nd ~f:(fun i ->
               mk_coeffs_bounds_of_int 1
                 (Array.to_list @@ Array.slice rc.(i) 1 (Array.length rc.(i)))
                 tf_sub_params.lbec tf_params.ubec tf_sub_params.beec)
      in
      (Set.Poly.union_list expr_pos_neg_maps, Formula.and_of phis)
    in
    let expr_const_bounds =
      Formula.and_of
      @@ List.init nd ~f:(fun i ->
             mk_const_bounds_int rc.(i).(0) None tf_params.ubed tf_params.es)
    in
    let cond_pos_neg_map, cond_coeffs_bounds =
      let cond_pos_neg_mapss, phiss =
        List.unzip
        @@ List.init (nd - 1) ~f:(fun i ->
               List.unzip
               @@ List.init (List.nth_exn tf_params.shp i) ~f:(fun j ->
                      mk_coeffs_bounds_of_int 1
                        (Array.to_list
                        @@ Array.slice dc.(i).(j) 1 (Array.length dc.(i).(j)))
                        None tf_params.ubcc None))
      in
      ( Set.Poly.union_list @@ List.map ~f:Set.Poly.union_list cond_pos_neg_mapss,
        Formula.and_of @@ List.map ~f:Formula.and_of phiss )
    in
    let cond_const_bounds =
      Formula.and_of
      @@ List.init (nd - 1) ~f:(fun i ->
             Formula.and_of
             @@ List.init (List.nth_exn tf_params.shp i) ~f:(fun j ->
                    mk_const_bounds_int
                      dc.(i).(j).(0)
                      None tf_params.ubcd tf_params.cs))
    in
    let templ_params =
      let templ_params_fun =
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
             templ_params_fun;
             templ_params_quals;
           ]
    in
    {
      templ_params;
      hole_quals_map;
      func;
      expr_params_bounds = Formula.mk_true () (*Dummy*);
      expr_coeffs_bounds;
      expr_const_bounds;
      cond_coeffs_bounds;
      cond_const_bounds;
    }

let gen_fun ~ignore_bool tf_params tf_sub_params params ret : templ_func =
  let rec aux = function
    | [] ->
        (match ret with
        | _, T_bool.SBool -> gen_bool_fun
        | _, T_int.SInt -> gen_int_fun
        | _, T_real.SReal -> gen_real_fun
        | _, T_bv.SBV _ -> gen_bv_fun
        | _, T_array.SArray _ -> gen_array_fun
        | _, T_dt.SDT _ -> gen_dt_fun
        | _, sort ->
            failwith
            @@ sprintf "[gen_fun] %s not supported" (Term.str_of_sort sort))
          tf_params tf_sub_params params ret
    | (x, sort) :: xs ->
        assert (Term.is_bool_sort sort);
        let templ1 = aux xs in
        let templ2 = aux xs in
        ite_templ (Formula.of_bool_var x) templ1 templ2
  in
  aux
    (if ignore_bool then [] else List.filter params ~f:(snd >> Term.is_bool_sort))

let gen_prop ~ignore_bool ?(is_integ = false) tf_params tf_sub_params params ret
    : templ_func =
  let rec aux = function
    | [] -> (
        match ret with
        | _, T_real.SReal ->
            gen_prop_fun ~is_integ tf_params tf_sub_params params ret
        | _, T_tuple.STuple sorts when List.for_all sorts ~f:Term.is_real_sort
          ->
            gen_prop_fun ~is_integ tf_params tf_sub_params params ret
        | _, sort ->
            failwith
            @@ sprintf "[gen_prop] %s not supported" (Term.str_of_sort sort))
    | (x, sort) :: xs ->
        assert (Term.is_bool_sort sort);
        let templ1 = aux xs in
        let templ2 = aux xs in
        ite_templ (Formula.of_bool_var x) templ1 templ2
  in
  aux
    (if ignore_bool then [] else List.filter params ~f:(snd >> Term.is_bool_sort))

(** Templates for ordinary predicate variables *)

type templ_pred = {
  templ_params : Logic.sort_env_map;
  hole_quals_map : hole_qualifiers_map;
  pred : Formula.t;
  coeffs_bounds : Formula.t;
  consts_bounds : Formula.t;
  quals_bounds : Formula.t;
}

type pred_tfp = {
  terms : (Term.t * Sort.t) list;
  quals : Formula.t list;
  shp : int list;
  ubc : Z.t option;
  ubd : Z.t option;
  s : Z.t Set.Poly.t;
}

type pred_tfsp = { bec : Z.t option }

let gen_dnf ?(eq_atom = false) tf_params tfs_params params : templ_pred =
  let sort, num_ts =
    let terms =
      List.map params ~f:(fun (x, s) -> (Term.mk_var x s, s)) @ tf_params.terms
    in
    ( T_irb.sort_of terms,
      List.filter terms ~f:(function
        | _, T_int.SInt | _, T_real.SReal -> true
        | _, _ -> false) )
  in
  let ( templ_paramss,
        hole_quals_map,
        disjuncs,
        coeffs_bounds,
        consts_bounds,
        quals_bounds ) =
    List.unzip6
    @@ List.init (List.length tf_params.shp) ~f:(fun idx ->
           let templ_paramss, atoms, coeffs_bounds, consts_bounds, quals_bounds
               =
             (* generate affine equality (if eq_atom) or inequality (otherwise) templates *)
             List.unzip5
             @@ List.init (List.nth_exn tf_params.shp idx) ~f:(fun _ ->
                    let (coeffs, const), pred =
                      T_irb.(if eq_atom then eq_of else ineq_of) sort num_ts
                    in
                    let pos_neg_map, coeffs_bounds =
                      mk_coeffs_bounds_of_int 1 coeffs None tf_params.ubc
                        tfs_params.bec
                    in
                    let consts_bounds =
                      mk_const_bounds_int const None tf_params.ubd tf_params.s
                    in
                    let quals_bounds = (*ToDo*) Formula.mk_true () in
                    let templ_params =
                      Set.union pos_neg_map @@ Set.Poly.of_list
                      @@ List.map ~f:(Term.let_var >> fst) (const :: coeffs)
                    in
                    ( templ_params,
                      Formula.mk_atom pred,
                      coeffs_bounds,
                      consts_bounds,
                      quals_bounds ))
           in
           let templ_params_quals, quals, hole =
             gen_hole_for_qualifiers (params, tf_params.quals)
           in
           ( Set.Poly.union_list (templ_params_quals :: templ_paramss),
             (hole, quals),
             Formula.and_of
               (mk_pvar_app (Ident.name_of_tvar hole) params :: atoms),
             Formula.and_of coeffs_bounds,
             Formula.and_of consts_bounds,
             Formula.and_of quals_bounds ))
  in
  {
    templ_params =
      Map.of_set_exn @@ Logic.of_old_sort_env_set
      @@ Set.Poly.union_list templ_paramss;
    hole_quals_map;
    pred = Formula.or_of disjuncs;
    coeffs_bounds = Formula.and_of coeffs_bounds;
    consts_bounds = Formula.and_of consts_bounds;
    quals_bounds = Formula.and_of quals_bounds;
  }

(** Templates for functional predicate variables *)

type templ_func_pred = {
  templ_params : Logic.sort_env_map;
  hole_quals_map : hole_qualifiers_map;
  pred : Formula.t;
  expr_params_bounds : Formula.t;
  expr_coeffs_bounds : Formula.t;
  expr_const_bounds : Formula.t;
  cond_coeffs_bounds : Formula.t;
  cond_const_bounds : Formula.t;
}

let gen_fn_predicate ~ignore_bool tf_params tf_sub_params params :
    templ_func_pred =
  let params, (xret, sret) = List.rest_last params in
  (* assert (Fn.non Term.is_bool_sort (snd ret)); *)
  let templ =
    gen_fun ~ignore_bool tf_params tf_sub_params params (Some xret, sret)
  in
  {
    templ_params = templ.templ_params;
    hole_quals_map = templ.hole_quals_map;
    pred = Formula.eq (uncurry Term.mk_var (xret, sret)) templ.func;
    expr_params_bounds = templ.expr_params_bounds;
    expr_coeffs_bounds = templ.expr_coeffs_bounds;
    expr_const_bounds = templ.expr_const_bounds;
    cond_coeffs_bounds = templ.cond_coeffs_bounds;
    cond_const_bounds = templ.cond_const_bounds;
  }

(** Templates for non-empty predicate variables *)

type templ_ne_pred = {
  templ_params : Logic.sort_env_map;
  hole_quals_map : hole_qualifiers_map;
  pred : Formula.t;
  ne_constr : Formula.t;
  scope_constr : Formula.t;
  coeffs_bounds : Formula.t;
  consts_bounds : Formula.t;
}

type ne_pred_tfp = {
  terms : Term.t list (*(Term.t * Sort.t) list*);
  quals : Formula.t list;
  dep : int;
  ext : int;
  ubc : int;
  ubd : int;
}

let gen_bool_ne_template tfp b_j params (rv, rs) =
  let quals =
    List.dedup_and_sort ~compare:Stdlib.compare
      (Formula.mk_true () :: Formula.mk_false () :: quals_over tfp.quals params)
  in
  let pred =
    Formula.and_of
    @@ List.mapi quals ~f:(fun i qual ->
           Formula.mk_imply
             (Formula.eq b_j @@ T_int.mk_int @@ Z.of_int i)
             (Formula.eq (Term.mk_var rv rs) @@ T_bool.of_formula qual))
  in
  let scope_constr =
    Formula.and_of
      [
        Formula.geq b_j @@ T_int.zero ();
        Formula.leq b_j @@ T_int.mk_int @@ Z.of_int @@ List.length quals;
      ]
  in
  {
    templ_params = Map.Poly.empty;
    hole_quals_map = [] (* dummy*);
    pred;
    ne_constr = Formula.mk_true () (* dummy*);
    scope_constr;
    coeffs_bounds = Formula.mk_true ();
    consts_bounds = Formula.mk_true ();
  }

let gen_int_ne_template tfp b_j params (rv, rs) =
  if false then
    print_endline
    @@ sprintf "gen_int_ne_template terms: %s"
    @@ String.concat_map_list ~sep:"," tfp.terms ~f:Term.str_of;
  let int_terms =
    List.dedup_and_sort ~compare:Stdlib.compare
    @@ List.filter ~f:T_int.is_sint
    @@ Term.of_sort_env params
    @ terms_over tfp.terms params
  in
  let quals =
    let vs = Set.Poly.of_list ((rv, rs) :: params) in
    List.filter tfp.quals ~f:(fun phi ->
        match Normalizer.normalize phi with
        | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; _ ], _), _) as
          phi
          when AffineTerm.is_affine t1 ->
            let tvs = Formula.term_sort_env_of phi in
            Set.is_subset tvs ~of_:vs
            && Set.mem tvs (rv, rs)
            && Option.is_some
               @@ AffineTerm.extract_term_from_affine rv
                    (Evaluator.simplify_term >> Normalizer.normalize_term)
                    t1
        | _ -> false)
  in
  if false then
    print_endline
    @@ sprintf "gen_int_ne_template int_terms: %s"
    @@ String.concat_map_list ~sep:"," int_terms ~f:Term.str_of;
  let dc = gen_params_0d (List.length int_terms + 1) in
  let sel_terms, cond =
    let sel_terms, conds =
      List.unzip
      @@ List.filter_map int_terms ~f:(function
           | Term.FunApp (T_dt.DTSel (sel_name, dt, _sort), [ t ], _) as term ->
               Option.map (Datatype.look_up_cons_of_sel dt sel_name)
                 ~f:(fun cons ->
                   ( term,
                     Formula.mk_atom
                     @@ T_dt.mk_is_cons dt (Datatype.name_of_cons cons) t ))
           | _ -> None)
    in
    (Set.Poly.of_list sel_terms, Formula.and_of conds)
  in
  let pred =
    let pred_t =
      Formula.mk_imply cond
      @@ Formula.eq (Term.mk_var rv rs)
      @@ T_int.mk_sum dc.(0)
      @@ List.mapi int_terms ~f:(fun i t -> T_int.mk_mul dc.(i + 1) t)
    in
    let pred_f =
      Formula.mk_imply (Formula.mk_neg cond)
      @@ Formula.eq (Term.mk_var rv rs)
      @@ T_int.mk_sum dc.(0)
      @@ List.mapi int_terms ~f:(fun i t ->
             T_int.mk_mul
               (if Set.mem sel_terms t then T_int.zero () else dc.(i + 1))
               t)
    in
    Formula.and_of
    @@ Formula.mk_imply
         (Formula.eq b_j @@ T_int.mk_int Z.zero)
         (Formula.and_of [ pred_t; pred_f ])
       :: List.mapi quals ~f:(fun i qual ->
              Formula.mk_imply
                (Formula.eq b_j @@ T_int.mk_int @@ Z.of_int (i + 1))
                qual)
  in
  let consts_bounds =
    Formula.leq (T_int.mk_abs dc.(0)) (T_int.mk_int @@ Z.of_int tfp.ubd)
  in
  let coeffs_bounds =
    Formula.leq
      (Array.foldi dc ~init:(T_int.zero ()) ~f:(fun i acc c ->
           if i = 0 then acc else T_int.mk_add acc @@ T_int.mk_abs c))
      (T_int.mk_int @@ Z.of_int tfp.ubc)
  in
  let templ_params =
    Map.Poly.of_alist_exn @@ Array.to_list
    @@ Array.map dc ~f:(Term.let_var >> fst >> Logic.ExtTerm.of_old_sort_bind)
  in
  let scope_constr =
    Formula.and_of
      [
        Formula.geq b_j @@ T_int.zero ();
        Formula.leq b_j @@ T_int.mk_int @@ Z.of_int (List.length quals + 1);
      ]
  in
  {
    templ_params;
    hole_quals_map = [] (* dummy*);
    pred;
    ne_constr = Formula.mk_true () (* dummy*);
    scope_constr;
    coeffs_bounds;
    consts_bounds;
  }

let gen_dt_ne_template tfp b_j params (rv, rs) =
  let int_terms =
    List.dedup_and_sort ~compare:Stdlib.compare
    @@ List.filter ~f:T_int.is_sint
    @@ Term.of_sort_env params
    @ terms_over tfp.terms params
  in
  let dc = gen_params_1d tfp.ext (List.length int_terms + 1) in
  let cons_terms =
    let affines =
      List.init tfp.ext ~f:(fun i ->
          T_int.mk_sum dc.(i).(0)
          @@ List.mapi int_terms ~f:(fun j t -> T_int.mk_mul dc.(i).(j + 1) t))
    in
    Set.to_list
    @@ Datatype.enum_cons_terms tfp.dep rs
    @@ Set.Poly.of_list @@ List.append affines
    @@ List.map params ~f:(uncurry Term.mk_var)
  in
  let pred =
    Formula.and_of
    @@ List.mapi cons_terms ~f:(fun i t ->
           Formula.mk_imply
             (Formula.eq b_j @@ T_int.mk_int @@ Z.of_int i)
             (Formula.eq (Term.mk_var rv rs) t))
  in
  let scope_constr =
    Formula.and_of
      [
        Formula.geq b_j @@ T_int.zero ();
        Formula.leq b_j @@ T_int.mk_int @@ Z.of_int @@ List.length cons_terms;
      ]
  in
  let consts_bounds =
    Formula.and_of
    @@ List.init tfp.ext ~f:(fun i ->
           Formula.leq
             (T_int.mk_abs dc.(i).(0))
             (T_int.mk_int @@ Z.of_int tfp.ubd))
  in
  let coeffs_bounds =
    Formula.and_of
    @@ List.init tfp.ext ~f:(fun i ->
           Formula.leq
             (Array.foldi dc.(i) ~init:(T_int.zero ()) ~f:(fun j acc c ->
                  if j = 0 then acc else T_int.mk_add acc @@ T_int.mk_abs c))
             (T_int.mk_int @@ Z.of_int tfp.ubc))
  in
  let templ_params =
    Map.Poly.of_alist_exn @@ List.concat
    @@ List.init tfp.ext ~f:(fun i ->
           Array.to_list
           @@ Array.map dc.(i)
                ~f:(Term.let_var >> fst >> Logic.ExtTerm.of_old_sort_bind))
  in
  {
    templ_params;
    hole_quals_map = [] (* dummy*);
    pred;
    ne_constr = Formula.mk_true () (* dummy*);
    scope_constr;
    coeffs_bounds;
    consts_bounds;
  }

let gen_ne_template tfp params =
  let param_permutation =
    List.permutation_of @@ List.map params ~f:List.return
  in
  let bc = gen_params_0d (List.length params + 1) in
  let mk_select_i op i =
    Formula.mk_binop op (Formula.eq bc.(0) (T_int.mk_int @@ Z.of_int i))
  in
  let templs =
    List.mapi param_permutation ~f:(fun i params ->
        let templs =
          List.mapi params ~f:(fun j _ ->
              let params' = List.take params (j + 1) in
              let xs, r = (List.take params' j, List.last_exn params') in
              (match snd r with
              | T_dt.SDT _ -> gen_dt_ne_template
              | T_int.SInt -> gen_int_ne_template
              | T_bool.SBool -> gen_bool_ne_template
              | _ -> failwith "unsupported sort of ne predicate")
                tfp
                bc.(j + 1)
                xs r)
        in
        {
          templ_params =
            Map.force_merge_list @@ List.map templs ~f:(fun t -> t.templ_params);
          hole_quals_map = [] (* dummy*);
          pred =
            mk_select_i Formula.Imply i
            @@ Formula.and_of
            @@ List.map templs ~f:(fun t -> t.pred);
          ne_constr = Formula.mk_true () (* dummy*);
          scope_constr =
            mk_select_i Formula.Imply i
            @@ Formula.and_of
            @@ List.map templs ~f:(fun t -> t.scope_constr);
          coeffs_bounds =
            mk_select_i Formula.Imply i
            @@ Formula.and_of
            @@ List.map templs ~f:(fun t -> t.coeffs_bounds);
          consts_bounds =
            mk_select_i Formula.Imply i
            @@ Formula.and_of
            @@ List.map templs ~f:(fun t -> t.consts_bounds);
        })
  in
  let ne_constr =
    Formula.and_of
    @@ [
         Formula.geq bc.(0) @@ T_int.zero ();
         Formula.lt bc.(0)
         @@ T_int.mk_int @@ Z.of_int
         @@ List.length param_permutation;
       ]
    @ List.map templs ~f:(fun t -> t.ne_constr)
  in
  let templ_params =
    Map.force_merge_list
      ((Logic.of_old_sort_env_map @@ Map.Poly.of_alist_exn @@ Array.to_list
       @@ Array.map bc ~f:(Term.let_var >> fst))
      :: List.map templs ~f:(fun t -> t.templ_params))
  in
  {
    templ_params;
    hole_quals_map = List.concat_map templs ~f:(fun t -> t.hole_quals_map);
    pred = Formula.and_of @@ List.map templs ~f:(fun t -> t.pred);
    ne_constr;
    scope_constr =
      Formula.and_of @@ List.map templs ~f:(fun t -> t.scope_constr);
    coeffs_bounds =
      Formula.and_of @@ List.map templs ~f:(fun t -> t.coeffs_bounds);
    consts_bounds =
      Formula.and_of @@ List.map templs ~f:(fun t -> t.consts_bounds);
  }

(** Templates for admissible predicate variables *)

let gen_adm_predicate ~with_cond ~ignore_bool ~enable_lhs_param tf_params params
    : templ_func_pred =
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
        List.map ps ~f:(Formula.leq (T_int.zero ())),
        List.map2_exn ps xs ~f:(fun p x ->
            T_real.mk_rmul (T_irb.mk_int_to_real p) x) )
    else (Map.Poly.empty, [], [], xs)
  in
  let templs =
    List.map pxs ~f:(fun _ ->
        gen_prop ~ignore_bool tf_params
          { lbec = None; lbcc = None; beec = None; becc = None }
          params ret)
  in
  let b = Ident.mk_fresh_parameter () in
  let templ_params, pred =
    let templ_params =
      Map.force_merge_list
        (lhs_params :: List.map templs ~f:(fun t -> t.templ_params))
    in
    let funcs = List.map templs ~f:(fun t -> t.func) in
    if with_cond then
      match (xs, ps, pxs, funcs) with
      | [ x; score ], [ _; p2 ], [ px; pscore ], [ exp_x; exp_score ] ->
          ( Map.Poly.add_exn templ_params ~key:b ~data:Logic.BoolTerm.SBool,
            let p = T_real.mk_radd (T_real.rone ()) p2 in
            Formula.and_of
              [
                Formula.leq (T_real.rzero ()) x;
                Formula.leq px
                  (T_bool.ifte (Formula.of_bool_var b) exp_x
                     (T_real.mk_rmul score exp_x));
                Formula.leq
                  (T_real.mk_rmin exp_score p)
                  (T_real.mk_radd score pscore);
                (* min (e, p) <= p score where p>=1 *)
                Formula.leq score (T_real.rone ());
              ] )
      | _ -> assert false
    else
      ( templ_params,
        Formula.and_of
        @@ List.map3_exn xs pxs funcs ~f:(fun x px exp_x ->
               Formula.mk_and
                 (Formula.leq (T_real.rzero ()) x)
                 (Formula.leq px exp_x)) )
  in
  let expr_params_bounds =
    Formula.and_of @@ lhs_bounds
    @ List.map templs ~f:(fun t -> t.expr_params_bounds)
  in
  {
    templ_params;
    hole_quals_map = List.concat_map templs ~f:(fun t -> t.hole_quals_map);
    pred;
    expr_params_bounds;
    expr_coeffs_bounds =
      Formula.and_of @@ List.map templs ~f:(fun t -> t.expr_coeffs_bounds);
    expr_const_bounds =
      Formula.and_of @@ List.map templs ~f:(fun t -> t.expr_const_bounds);
    cond_coeffs_bounds =
      Formula.and_of @@ List.map templs ~f:(fun t -> t.cond_coeffs_bounds);
    cond_const_bounds =
      Formula.and_of @@ List.map templs ~f:(fun t -> t.cond_const_bounds);
  }

(** Templates for integrable predicate variables *)

let gen_integ_predicate ~ignore_bool ~enable_lhs_param tf_params params :
    templ_func_pred =
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
        List.map lhs_params ~f:(Formula.leq (T_int.zero ())),
        List.map2_exn lhs_params xs ~f:(fun p x ->
            T_real.mk_rmul
              (T_irb.mk_int_to_real
                 (*ToDo*) (T_int.mk_add p (T_int.mk_int Z.one)))
              x) )
    else (Map.Poly.empty, [], xs)
  in
  let templs =
    List.map xs ~f:(fun _ ->
        gen_prop ~ignore_bool ~is_integ:true tf_params
          { lbec = None; lbcc = None; beec = None; becc = None }
          params ret)
  in
  let templ_params =
    Map.force_merge_list
      (lhs_params :: List.map templs ~f:(fun t -> t.templ_params))
  in
  let pred =
    Formula.and_of
    @@ List.map2_exn xs
         (List.map templs ~f:(fun t -> t.func))
         ~f:(fun x exp_x ->
           Formula.mk_and
             (Formula.leq (T_real.rzero ()) x)
             (Formula.leq x exp_x))
  in
  let expr_params_bounds =
    Formula.and_of @@ lhs_bounds
    @ List.map templs ~f:(fun t -> t.expr_params_bounds)
  in
  {
    templ_params;
    hole_quals_map = List.concat_map templs ~f:(fun t -> t.hole_quals_map);
    pred;
    expr_params_bounds;
    expr_coeffs_bounds =
      Formula.and_of @@ List.map templs ~f:(fun t -> t.expr_coeffs_bounds);
    expr_const_bounds =
      Formula.and_of @@ List.map templs ~f:(fun t -> t.expr_const_bounds);
    cond_coeffs_bounds =
      Formula.and_of @@ List.map templs ~f:(fun t -> t.cond_coeffs_bounds);
    cond_const_bounds =
      Formula.and_of @@ List.map templs ~f:(fun t -> t.cond_const_bounds);
  }

(** Templates for well-founded predicate variables *)

type templ_wf_pred = {
  templ_params : Logic.sort_env_map;
  hole_quals_map : hole_qualifiers_map;
  pred : Formula.t;
  rfun_coeffs_bounds : Formula.t;
  rfun_const_bounds : Formula.t;
  disc_coeffs_bounds : Formula.t;
  disc_const_bounds : Formula.t;
}

type wf_pred_tfp = {
  terms : Term.t list (*(Term.t * Sort.t) list*);
  quals : Formula.t list;
  shp : int list;
  nl : int;
  ubrc : Z.t option;
  ubrd : Z.t option;
  ubdc : Z.t option;
  ubdd : Z.t option;
  ds : Z.t Set.Poly.t;
}

type wf_pred_tsfp = {
  norm_type : int;
  lbrc : Z.t option;
  lbdc : Z.t option;
  berc : Z.t option;
  bedc : Z.t option;
}

let gen_wf_predicate ~use_ifte tfp tsfp params : templ_wf_pred =
  assert (List.length params mod 2 = 0);
  let irb_params = List.filter params ~f:(snd >> Term.is_irb_sort) in
  let size = List.length irb_params / 2 in
  let txs, tys =
    let irb_params_x, irb_params_y = List.split_n irb_params size in
    ( List.map ~f:T_irb.to_int_if_rb (Term.of_sort_env irb_params_x),
      List.map ~f:T_irb.to_int_if_rb (Term.of_sort_env irb_params_y) )
  in
  let np = List.length tfp.shp in
  let rc, dc =
    ( gen_params_2d tfp.nl np (size + 1),
      gen_params_3d_flex tfp.nl
        (if use_ifte then np - 1 else np)
        tfp.shp (size + 1) )
  in
  let templ_params_quals, hole_quals_map, holes =
    let templ_params_qualsss, hole_quals_mapss, holess =
      let params_x, params_y = List.split_n params (List.length params / 2) in
      let x2y = Formula.rename @@ ren_of_sort_env_list params_x params_y in
      let quals = quals_over tfp.quals params_x in
      List.unzip3
      @@ List.init tfp.nl ~f:(fun i ->
             List.unzip3
             @@ List.init np ~f:(fun j ->
                    let templ_params_quals, quals_x, hole =
                      gen_hole_for_qualifiers (params, quals)
                    in
                    let quals_y =
                      List.map quals_x ~f:(Pair.map_snd (Pair.map_snd x2y))
                    in
                    let hole_x_name = Ident.name_of_tvar hole ^ "_x" in
                    let hole_y_name = Ident.name_of_tvar hole ^ "_y" in
                    ( templ_params_quals,
                      [
                        (Ident.Tvar hole_x_name, quals_x);
                        (Ident.Tvar hole_y_name, quals_y);
                      ],
                      ( (i, j),
                        ( mk_pvar_app hole_x_name params,
                          mk_pvar_app hole_y_name params ) ) )))
    in
    ( Set.Poly.union_list @@ List.map ~f:Set.Poly.union_list templ_params_qualsss,
      List.concat @@ List.concat hole_quals_mapss,
      List.concat holess )
  in
  let pred =
    let r_x i j =
      T_int.mk_sum
        rc.(i).(j).(0)
        (List.mapi ~f:(fun k -> T_int.mk_mul rc.(i).(j).(k + 1)) txs)
    in
    let r_y i j =
      T_int.mk_sum
        rc.(i).(j).(0)
        (List.mapi ~f:(fun k -> T_int.mk_mul rc.(i).(j).(k + 1)) tys)
    in
    let d_x i j k =
      T_int.mk_sum
        dc.(i).(j).(k).(0)
        (List.mapi ~f:(fun l -> T_int.mk_mul dc.(i).(j).(k).(l + 1)) txs)
    in
    let d_y i j k =
      T_int.mk_sum
        dc.(i).(j).(k).(0)
        (List.mapi ~f:(fun l -> T_int.mk_mul dc.(i).(j).(k).(l + 1)) tys)
    in
    let disc_x i j =
      Formula.and_of
      @@ (fst @@ List.Assoc.find_exn ~equal:Stdlib.( = ) holes (i, j))
         :: List.init (List.nth_exn tfp.shp j) ~f:(fun k ->
                Formula.geq (d_x i j k) (T_int.zero ()))
    in
    let disc_y i j =
      Formula.and_of
      @@ (snd @@ List.Assoc.find_exn ~equal:Stdlib.( = ) holes (i, j))
         :: List.init (List.nth_exn tfp.shp j) ~f:(fun k ->
                Formula.geq (d_y i j k) (T_int.zero ()))
    in
    let rfun_x i =
      let rest, last =
        List.rest_last (List.init np ~f:(fun j -> (j, r_x i j)))
      in
      List.fold_right rest ~init:(snd last) ~f:(fun (j, t1) t2 ->
          T_bool.ifte (disc_x i j) t1 t2)
    in
    let rfun_y i =
      let rest, last =
        List.rest_last (List.init np ~f:(fun j -> (j, r_y i j)))
      in
      List.fold_right rest ~init:(snd last) ~f:(fun (j, t1) t2 ->
          T_bool.ifte (disc_y i j) t1 t2)
    in
    let r_geq_zero =
      let f =
        if use_ifte then fun i -> Formula.geq (rfun_x i) (T_int.zero ())
        else fun i ->
          Formula.and_of
          @@ List.init np ~f:(fun j ->
                 Formula.mk_imply (disc_x i j)
                   (Formula.geq (r_x i j) (T_int.zero ())))
      in
      Formula.and_of @@ List.init tfp.nl ~f
    in
    let d_x_geq_zero =
      if use_ifte then Formula.mk_true ()
      else
        Formula.and_of
        @@ List.init tfp.nl ~f:(fun i ->
               Formula.or_of @@ List.init np ~f:(fun j -> disc_x i j))
    in
    let d_y_geq_zero =
      if use_ifte then Formula.mk_true ()
      else
        Formula.and_of
        @@ List.init tfp.nl ~f:(fun i ->
               Formula.or_of @@ List.init np ~f:(fun j -> disc_y i j))
    in
    let x_gt_y =
      let f =
        if use_ifte then fun i ->
          Formula.and_of
          @@ Formula.geq (rfun_x i) (T_int.mk_add (rfun_y i) (T_int.one ()))
             :: List.init i ~f:(fun l ->
                    Formula.geq (rfun_x l)
                      (T_int.mk_add (rfun_y l) (T_int.one ())))
        else fun i ->
          Formula.and_of
          @@ (Formula.or_of
             @@ List.init np ~f:(fun j ->
                    Formula.and_of
                    @@ disc_x i j
                       :: List.init np ~f:(fun k ->
                              Formula.mk_imply (disc_y i k)
                                (Formula.geq (r_x i j)
                                   (T_int.mk_add (r_y i k) (T_int.one ()))))))
             :: List.init i ~f:(fun l ->
                    Formula.or_of
                    @@ List.init np ~f:(fun j ->
                           Formula.and_of
                           @@ disc_x l j
                              :: List.init np ~f:(fun k ->
                                     Formula.mk_imply (disc_y l k)
                                       (Formula.geq (r_x l j) (r_y l k)))))
      in
      Formula.or_of @@ List.init tfp.nl ~f
    in
    Formula.and_of [ r_geq_zero; d_x_geq_zero; d_y_geq_zero; x_gt_y ]
  in
  let rfun_pos_neg_map, rfun_coeffs_bounds =
    let rfun_pos_neg_mapss, phiss =
      List.unzip
      @@ List.init tfp.nl ~f:(fun i ->
             List.unzip
             @@ List.init np ~f:(fun j ->
                    mk_coeffs_bounds_of_int tsfp.norm_type
                      (Array.to_list
                      @@ Array.slice rc.(i).(j) 1 (Array.length rc.(i).(j)))
                      tsfp.lbrc tfp.ubrc tsfp.berc))
    in
    ( Set.Poly.union_list @@ List.map ~f:Set.Poly.union_list rfun_pos_neg_mapss,
      Formula.and_of @@ List.map ~f:Formula.and_of phiss )
  in
  let rfun_const_bounds =
    Formula.and_of
    @@ List.init tfp.nl ~f:(fun i ->
           Formula.and_of
           @@ List.init np ~f:(fun j ->
                  mk_const_bounds_int
                    rc.(i).(j).(0)
                    None tfp.ubrd
                    (Set.Poly.singleton Z.zero)))
  in
  let disc_pos_neg_map, disc_coeffs_bounds =
    let disc_pos_neg_mapsss, phisss =
      List.unzip
      @@ List.init tfp.nl ~f:(fun i ->
             List.unzip
             @@ List.init
                  (if use_ifte then np - 1 else np)
                  ~f:(fun j ->
                    List.unzip
                    @@ List.init (List.nth_exn tfp.shp j) ~f:(fun k ->
                           mk_coeffs_bounds_of_int tsfp.norm_type
                             (Array.to_list
                             @@ Array.slice
                                  dc.(i).(j).(k)
                                  1
                                  (Array.length dc.(i).(j).(k)))
                             tsfp.lbdc tfp.ubdc tsfp.bedc)))
    in
    ( Set.Poly.union_list
      @@ List.map ~f:Set.Poly.union_list
      @@ List.map ~f:(List.map ~f:Set.Poly.union_list) disc_pos_neg_mapsss,
      Formula.and_of @@ List.map ~f:Formula.and_of
      @@ List.map ~f:(List.map ~f:Formula.and_of) phisss )
  in
  let disc_const_bounds =
    Formula.and_of
    @@ List.init tfp.nl ~f:(fun i ->
           Formula.and_of
           @@ List.init
                (if use_ifte then np - 1 else np)
                ~f:(fun j ->
                  Formula.and_of
                  @@ List.init (List.nth_exn tfp.shp j) ~f:(fun k ->
                         mk_const_bounds_int
                           dc.(i).(j).(k).(0)
                           None tfp.ubdd tfp.ds)))
  in
  let templ_params =
    let templ_params_fun =
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
    Map.of_set_exn @@ Logic.of_old_sort_env_set
    @@ Set.Poly.union_list
         [
           rfun_pos_neg_map;
           disc_pos_neg_map;
           templ_params_fun;
           templ_params_quals;
         ]
  in
  {
    templ_params;
    hole_quals_map;
    pred;
    rfun_coeffs_bounds;
    rfun_const_bounds;
    disc_coeffs_bounds;
    disc_const_bounds;
  }

let size_fun_apps =
  List.filter_map ~f:(function
    | v, T_dt.SDT dt ->
        Option.some @@ Datatype.app_size_fun dt (Term.mk_var v @@ T_dt.SDT dt)
    | _ -> None)

let gen_simplified_wf_predicate tfp tsfp params : templ_wf_pred =
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
    @ List.filter tfp.terms ~f:T_irb.is_sirb
  in
  (* ToDo: does not hold for arbitrary terms *)
  assert (List.length x_terms = List.length y_terms);
  let irb_params = List.filter params ~f:(snd >> Term.is_irb_sort) in
  let size = List.length irb_params / 2 in
  let txs, tys =
    let irb_params_x, irb_params_y = List.split_n irb_params size in
    ( List.map ~f:T_irb.to_int_if_rb (x_terms @ Term.of_sort_env irb_params_x),
      List.map ~f:T_irb.to_int_if_rb (y_terms @ Term.of_sort_env irb_params_y)
    )
  in
  let np = List.length tfp.shp in
  let rc, dc =
    ( gen_params_2d np tfp.nl (size + List.length x_terms + 1),
      gen_params_2d_flex np tfp.shp (size + List.length x_terms + 1) )
  in
  let templ_params_quals, hole_quals_map, holes =
    let x2y = Formula.rename @@ ren_of_sort_env_list params_x params_y in
    let quals = quals_over tfp.quals params_x in
    let templ_params_qualss, hole_quals_maps, holes =
      List.unzip3
      @@ List.init np ~f:(fun i ->
             let templ_params_quals, quals_x, hole =
               gen_hole_for_qualifiers (params, quals)
             in
             let quals_y =
               List.map quals_x ~f:(Pair.map_snd (Pair.map_snd x2y))
             in
             let hole_x_name = Ident.name_of_tvar hole ^ "_x" in
             let hole_y_name = Ident.name_of_tvar hole ^ "_y" in
             ( templ_params_quals,
               [
                 (Ident.Tvar hole_x_name, quals_x);
                 (Ident.Tvar hole_y_name, quals_y);
               ],
               ( i,
                 (mk_pvar_app hole_x_name params, mk_pvar_app hole_y_name params)
               ) ))
    in
    (Set.Poly.union_list templ_params_qualss, List.concat hole_quals_maps, holes)
  in
  let pred =
    let r_x i j =
      T_int.mk_sum
        rc.(i).(j).(0)
        (List.mapi ~f:(fun k -> T_int.mk_mul rc.(i).(j).(k + 1)) txs)
    in
    let r_y i j =
      T_int.mk_sum
        rc.(i).(j).(0)
        (List.mapi ~f:(fun k -> T_int.mk_mul rc.(i).(j).(k + 1)) tys)
    in
    let d_x i j =
      T_int.mk_sum
        dc.(i).(j).(0)
        (List.mapi ~f:(fun l -> T_int.mk_mul dc.(i).(j).(l + 1)) txs)
    in
    let d_y i j =
      T_int.mk_sum
        dc.(i).(j).(0)
        (List.mapi ~f:(fun l -> T_int.mk_mul dc.(i).(j).(l + 1)) tys)
    in
    let disc_x i =
      Formula.and_of
      @@ (fst @@ List.Assoc.find_exn ~equal:Stdlib.( = ) holes i)
         :: List.init (List.nth_exn tfp.shp i) ~f:(fun j ->
                Formula.geq (d_x i j) (T_int.zero ()))
    in
    let disc_y i =
      Formula.and_of
      @@ (snd @@ List.Assoc.find_exn ~equal:Stdlib.( = ) holes i)
         :: List.init (List.nth_exn tfp.shp i) ~f:(fun j ->
                Formula.geq (d_y i j) (T_int.zero ()))
    in
    let d_y_geq_zero = Formula.or_of @@ List.init np ~f:(fun j -> disc_y j) in
    let ldec i j =
      Formula.or_of
      @@ List.init tfp.nl ~f:(fun k ->
             Formula.and_of
             @@ Formula.geq (r_x i k) (T_int.zero ())
                :: Formula.geq (r_x i k) (T_int.mk_add (r_y j k) (T_int.one ()))
                :: List.init k ~f:(fun l ->
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
                         ]))
    in
    let pdec =
      Formula.or_of
      @@ List.init np ~f:(fun i ->
             Formula.and_of
             @@ disc_x i
                :: List.init np ~f:(fun j ->
                       Formula.mk_imply (disc_y j) (ldec i j)))
    in
    Formula.and_of [ d_y_geq_zero; pdec ]
  in
  let rfun_pos_neg_map, rfun_coeffs_bounds =
    let rfun_pos_neg_mapss, phiss =
      List.unzip
      @@ List.init np ~f:(fun i ->
             List.unzip
             @@ List.init tfp.nl ~f:(fun j ->
                    mk_coeffs_bounds_of_int tsfp.norm_type
                      (Array.to_list
                      @@ Array.slice rc.(i).(j) 1 (Array.length rc.(i).(j)))
                      tsfp.lbrc tfp.ubrc tsfp.berc))
    in
    ( Set.Poly.union_list @@ List.map ~f:Set.Poly.union_list rfun_pos_neg_mapss,
      Formula.and_of @@ List.map ~f:Formula.and_of phiss )
  in
  let rfun_const_bounds =
    Formula.and_of
    @@ List.init np ~f:(fun i ->
           Formula.and_of
           @@ List.init tfp.nl ~f:(fun j ->
                  mk_const_bounds_int
                    rc.(i).(j).(0)
                    None tfp.ubrd
                    (Set.Poly.singleton Z.zero)))
  in
  let disc_pos_neg_map, disc_coeffs_bounds =
    let disc_pos_neg_mapss, phiss =
      List.unzip
      @@ List.init np ~f:(fun i ->
             List.unzip
             @@ List.init (List.nth_exn tfp.shp i) ~f:(fun j ->
                    mk_coeffs_bounds_of_int tsfp.norm_type
                      (Array.to_list
                      @@ Array.slice dc.(i).(j) 1 (Array.length dc.(i).(j)))
                      tsfp.lbdc tfp.ubdc tsfp.bedc))
    in
    ( Set.Poly.union_list @@ List.map ~f:Set.Poly.union_list disc_pos_neg_mapss,
      Formula.and_of @@ List.map ~f:Formula.and_of phiss )
  in
  let disc_const_bounds =
    Formula.and_of
    @@ List.init np ~f:(fun i ->
           Formula.and_of
           @@ List.init (List.nth_exn tfp.shp i) ~f:(fun j ->
                  mk_const_bounds_int dc.(i).(j).(0) None tfp.ubdd tfp.ds))
  in
  let templ_params =
    let templ_params_fun =
      Set.Poly.of_list
      @@ List.map ~f:(Term.let_var >> fst)
      @@ (List.concat_map ~f:Array.to_list
         @@ List.concat_map ~f:Array.to_list
         @@ Array.to_list rc)
      @ List.concat_map ~f:Array.to_list
      @@ List.concat_map ~f:Array.to_list
      @@ Array.to_list dc
    in
    Map.of_set_exn @@ Logic.of_old_sort_env_set
    @@ Set.Poly.union_list
         [
           rfun_pos_neg_map;
           disc_pos_neg_map;
           templ_params_fun;
           templ_params_quals;
         ]
  in
  {
    templ_params;
    hole_quals_map;
    pred;
    rfun_coeffs_bounds;
    rfun_const_bounds;
    disc_coeffs_bounds;
    disc_const_bounds;
  }

let gen_simplified_nwf_predicate (rcs, dcs, qds) tfp tsfp
    (params, (idxl : Ident.tvar), params_x, (idxr : Ident.tvar), params_y) :
    templ_wf_pred =
  let d_terms, rx_terms, ry_terms =
    let terms_with terms params =
      size_fun_apps params @ Term.of_sort_env params @ terms_over terms params
    in
    ( List.filter ~f:T_int.is_sint @@ terms_with tfp.terms params,
      List.filter ~f:T_int.is_sint @@ terms_with tfp.terms params_x,
      List.filter ~f:T_int.is_sint @@ terms_with tfp.terms params_y )
  in
  let rx_quals = quals_over tfp.quals (params @ params_x) in
  let ry_quals = quals_over tfp.quals (params @ params_y) in
  let np = List.length tfp.shp in
  let rc_x, rc_y, dc_x, dc_y, qd_x, qd_y =
    let find_and_update tbl key ~f =
      match Hashtbl.Poly.find tbl key with
      | Some data -> data
      | None ->
          let data = f key in
          Hashtbl.Poly.add_exn tbl ~key ~data;
          data
    in
    let d_size = List.length d_terms in
    let rx_size, ry_size = (List.length rx_terms, List.length ry_terms) in
    let ddx_size, ddy_size = (List.length rx_quals, List.length ry_quals) in
    ( find_and_update rcs idxl ~f:(fun _ ->
          gen_params_2d np tfp.nl (rx_size + d_size + 1)),
      find_and_update rcs idxr ~f:(fun _ ->
          gen_params_2d np tfp.nl (ry_size + d_size + 1)),
      find_and_update dcs idxl ~f:(fun _ ->
          gen_params_2d_flex np tfp.shp (rx_size + d_size + 1)),
      find_and_update dcs idxr ~f:(fun _ ->
          gen_params_2d_flex np tfp.shp (ry_size + d_size + 1)),
      find_and_update qds idxl ~f:(fun _ -> gen_params_1d np ddx_size),
      find_and_update qds idxr ~f:(fun _ -> gen_params_1d np ddy_size) )
  in
  let templ_params_quals, hole_quals_map, holes =
    let x2y = Formula.rename @@ ren_of_sort_env_list params_x params_y in
    let templ_params_qualss, hole_quals_maps, holes =
      List.unzip3
      @@ List.init np ~f:(fun i ->
             let params' = params @ params_x @ params_y in
             let templ_params_quals_x, quals_x, hole_x =
               gen_hole_for_qualifiers ~qds:(Some qd_x.(i)) (params', rx_quals)
             in
             let templ_params_quals_y, quals_y, hole_y =
               if Stdlib.(idxl = idxr) then
                 let quals_y =
                   List.map quals_x ~f:(Pair.map_snd (Pair.map_snd x2y))
                 in
                 (templ_params_quals_x, quals_y, hole_x)
               else
                 gen_hole_for_qualifiers ~qds:(Some qd_y.(i)) (params', ry_quals)
             in
             let hole_x_name = Ident.name_of_tvar hole_x ^ "_x" in
             let hole_y_name = Ident.name_of_tvar hole_y ^ "_y" in
             ( Set.union templ_params_quals_x templ_params_quals_y,
               [
                 (Ident.Tvar hole_x_name, quals_x);
                 (Ident.Tvar hole_y_name, quals_y);
               ],
               ( i,
                 ( mk_pvar_app hole_x_name params',
                   mk_pvar_app hole_y_name params' ) ) ))
    in
    (Set.Poly.union_list templ_params_qualss, List.concat hole_quals_maps, holes)
  in
  let pred =
    let r_x i j =
      T_int.mk_sum
        rc_x.(i).(j).(0)
        (List.mapi (d_terms @ rx_terms) ~f:(fun k ->
             T_int.mk_mul rc_x.(i).(j).(k + 1)))
    in
    let r_y i j =
      T_int.mk_sum
        rc_y.(i).(j).(0)
        (List.mapi (d_terms @ ry_terms) ~f:(fun k ->
             T_int.mk_mul rc_y.(i).(j).(k + 1)))
    in
    let d_x i j =
      T_int.mk_sum
        dc_x.(i).(j).(0)
        (List.mapi (d_terms @ rx_terms) ~f:(fun l ->
             T_int.mk_mul dc_x.(i).(j).(l + 1)))
    in
    let d_y i j =
      T_int.mk_sum
        dc_y.(i).(j).(0)
        (List.mapi (d_terms @ ry_terms) ~f:(fun l ->
             T_int.mk_mul dc_y.(i).(j).(l + 1)))
    in
    let disc_x i =
      Formula.and_of
      @@ (fst @@ List.Assoc.find_exn ~equal:Stdlib.( = ) holes i)
         :: List.init (List.nth_exn tfp.shp i) ~f:(fun j ->
                Formula.geq (d_x i j) (T_int.zero ()))
    in
    let disc_y i =
      Formula.and_of
      @@ (snd @@ List.Assoc.find_exn ~equal:Stdlib.( = ) holes i)
         :: List.init (List.nth_exn tfp.shp i) ~f:(fun j ->
                Formula.geq (d_y i j) (T_int.zero ()))
    in
    let d_y_geq_zero = Formula.or_of @@ List.init np ~f:(fun j -> disc_y j) in
    let ldec i j =
      Formula.or_of
      @@ List.init tfp.nl ~f:(fun k ->
             Formula.and_of
             @@ Formula.geq (r_x i k) (T_int.zero ())
                :: Formula.geq (r_x i k) (T_int.mk_add (r_y j k) (T_int.one ()))
                :: List.init k ~f:(fun l ->
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
                         ]))
    in
    let pdec =
      Formula.or_of
      @@ List.init np ~f:(fun i ->
             Formula.and_of
             @@ disc_x i
                :: List.init np ~f:(fun j ->
                       Formula.mk_imply (disc_y j) (ldec i j)))
    in
    Formula.and_of [ d_y_geq_zero; pdec ]
  in
  let rfun_pos_neg_map, rfun_coeffs_bounds =
    let rfun_pos_neg_maps, phis =
      List.unzip
      @@ List.init np ~f:(fun i ->
             let rfun_pos_neg_maps_x, phis_x =
               List.unzip
               @@ List.init tfp.nl ~f:(fun j ->
                      mk_coeffs_bounds_of_int tsfp.norm_type
                        (Array.to_list
                        @@ Array.slice
                             rc_x.(i).(j)
                             1
                             (Array.length rc_x.(i).(j)))
                        tsfp.lbrc tfp.ubrc tsfp.berc)
             in
             let rfun_pos_neg_maps_y, phis_y =
               if Stdlib.(idxl = idxr) then ([], [])
               else
                 List.unzip
                 @@ List.init tfp.nl ~f:(fun j ->
                        mk_coeffs_bounds_of_int tsfp.norm_type
                          (Array.to_list
                          @@ Array.slice
                               rc_y.(i).(j)
                               1
                               (Array.length rc_y.(i).(j)))
                          tsfp.lbrc tfp.ubrc tsfp.berc)
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
           @@ List.init tfp.nl ~f:(fun j ->
                  mk_const_bounds_int
                    rc_x.(i).(j).(0)
                    None tfp.ubrd
                    (Set.Poly.singleton Z.zero)))
    @
    if Stdlib.(idxl = idxr) then []
    else
      List.init np ~f:(fun i ->
          Formula.and_of
          @@ List.init tfp.nl ~f:(fun j ->
                 mk_const_bounds_int
                   rc_y.(i).(j).(0)
                   None tfp.ubrd
                   (Set.Poly.singleton Z.zero)))
  in
  let disc_pos_neg_map, disc_coeffs_bounds =
    let disc_pos_neg_maps, phis =
      List.unzip
      @@ List.init np ~f:(fun i ->
             let disc_pos_neg_maps_x, phis_x =
               List.unzip
               @@ List.init (List.nth_exn tfp.shp i) ~f:(fun j ->
                      mk_coeffs_bounds_of_int tsfp.norm_type
                        (Array.to_list
                        @@ Array.slice
                             dc_x.(i).(j)
                             1
                             (Array.length dc_x.(i).(j)))
                        tsfp.lbdc tfp.ubdc tsfp.bedc)
             in
             let disc_pos_neg_maps_y, phis_y =
               if Stdlib.(idxl = idxr) then ([], [])
               else
                 List.unzip
                 @@ List.init (List.nth_exn tfp.shp i) ~f:(fun j ->
                        mk_coeffs_bounds_of_int tsfp.norm_type
                          (Array.to_list
                          @@ Array.slice
                               dc_y.(i).(j)
                               1
                               (Array.length dc_y.(i).(j)))
                          tsfp.lbdc tfp.ubdc tsfp.bedc)
             in
             ( Set.Poly.union_list (disc_pos_neg_maps_x @ disc_pos_neg_maps_y),
               Formula.and_of (phis_x @ phis_y) ))
    in
    (Set.Poly.union_list disc_pos_neg_maps, Formula.and_of phis)
  in
  let disc_const_bounds =
    Formula.and_of
    @@ List.init np ~f:(fun i ->
           Formula.and_of
           @@ List.init (List.nth_exn tfp.shp i) ~f:(fun j ->
                  mk_const_bounds_int dc_x.(i).(j).(0) None tfp.ubdd tfp.ds))
    @
    if Stdlib.(idxl = idxr) then []
    else
      List.init np ~f:(fun i ->
          Formula.and_of
          @@ List.init (List.nth_exn tfp.shp i) ~f:(fun j ->
                 mk_const_bounds_int dc_y.(i).(j).(0) None tfp.ubdd tfp.ds))
  in
  let templ_params =
    let templ_params_fun =
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
    Map.of_set_exn @@ Logic.of_old_sort_env_set
    @@ Set.Poly.union_list
         [
           rfun_pos_neg_map;
           disc_pos_neg_map;
           templ_params_fun;
           templ_params_quals;
         ]
  in
  {
    templ_params;
    hole_quals_map;
    pred;
    rfun_coeffs_bounds;
    rfun_const_bounds;
    disc_coeffs_bounds;
    disc_const_bounds;
  }

(** Templates for probabilistic predicate variables *)

type templ_prob_pred = {
  templ_params : sort_env_map;
  templ_constrs : Formula.t list;
  prob_pred : Term.t;
}

let mk_affine terms =
  let templ_params_list =
    List.init
      (List.length terms + 1)
      ~f:(fun _ ->
        ( (*Ident.mk_fresh_parameter ()*)
          Ident.mk_fresh_tvar ~prefix:(Some "param") (),
          T_real.SReal ))
  in
  let cs = List.map templ_params_list ~f:(uncurry2 Term.mk_var) in
  {
    templ_params = Map.Poly.of_alist_exn templ_params_list;
    templ_constrs = [];
    prob_pred =
      List.fold2_exn ~init:(List.hd_exn cs) (List.tl_exn cs) terms
        ~f:(fun acc c t -> T_real.mk_radd acc (T_real.mk_rmul c t));
  }

let terms_of degree args =
  let xs = List.map args ~f:(uncurry2 Term.mk_var) in
  Set.to_list
  @@ Set.Poly.filter_map (Set.subsets_with_duplicates xs degree) ~f:(function
       | [] -> None
       | t :: ts -> Some (T_real.mk_rprod t ts))

let gen_prob_template ~use_orig_ite ~num_conds ~cond_degree ~term_degree args
    body : templ_prob_pred =
  let rec aux = function
    | Term.FunApp (T_bool.IfThenElse, [ cond; t1; t2 ], _) when use_orig_ite ->
        let t1' = aux t1 in
        let t2' = aux t2 in
        {
          templ_params = Map.force_merge t1'.templ_params t2'.templ_params;
          templ_constrs = t1'.templ_constrs @ t2'.templ_constrs;
          prob_pred = T_bool.mk_if_then_else cond t1'.prob_pred t2'.prob_pred;
        }
    | _ -> mk_affine @@ terms_of term_degree args
  in
  List.fold_right (List.init num_conds ~f:Fn.id) ~init:(aux body) ~f:(fun _ t ->
      let cond = mk_affine @@ terms_of cond_degree args in
      let t' = aux body in
      {
        templ_params =
          Map.force_merge_list
            [ cond.templ_params; t'.templ_params; t.templ_params ];
        templ_constrs = cond.templ_constrs @ t'.templ_constrs @ t.templ_constrs;
        prob_pred =
          T_bool.mk_if_then_else
            (T_bool.of_formula @@ Formula.geq cond.prob_pred (T_real.rzero ()))
            t'.prob_pred t.prob_pred;
      })

let underapprox_of ~cond_degree ~term_degree args t =
  let res =
    match term_degree with
    | None ->
        { templ_params = Map.Poly.empty; templ_constrs = []; prob_pred = t }
    | Some term_degree ->
        let rec aux = function
          | Term.FunApp (T_bool.IfThenElse, [ cond; t1; t2 ], _) ->
              let t1' = aux t1 in
              let t2' = aux t2 in
              {
                templ_params = Map.force_merge t1'.templ_params t2'.templ_params;
                templ_constrs = t1'.templ_constrs @ t2'.templ_constrs;
                prob_pred =
                  T_bool.mk_if_then_else cond t1'.prob_pred t2'.prob_pred;
              }
          | Term.FunApp (T_real.RAdd, [ t1; t2 ], _) ->
              let t1' = aux t1 in
              let t2' = aux t2 in
              {
                templ_params = Map.force_merge t1'.templ_params t2'.templ_params;
                templ_constrs = t1'.templ_constrs @ t2'.templ_constrs;
                prob_pred = T_real.mk_radd t1'.prob_pred t2'.prob_pred;
              }
          | t ->
              let c =
                mk_affine (* ToDo: support conditional expressions *)
                @@ terms_of term_degree args
              in
              {
                templ_params = c.templ_params;
                templ_constrs =
                  c.templ_constrs
                  @ Formula.mk_range_real c.prob_pred Q.zero Q.one;
                prob_pred = T_real.mk_rmul c.prob_pred t;
              }
        in
        aux t
  in
  match cond_degree with
  | None -> (None, res)
  | Some cond_degree ->
      let cond = mk_affine @@ terms_of cond_degree args in
      ( Some cond.prob_pred,
        {
          templ_params = Map.force_merge res.templ_params cond.templ_params;
          templ_constrs = res.templ_constrs @ cond.templ_constrs;
          prob_pred =
            T_bool.mk_if_then_else
              (T_bool.of_formula @@ Formula.geq cond.prob_pred (T_real.rzero ()))
              res.prob_pred (T_real.rzero ());
        } )
