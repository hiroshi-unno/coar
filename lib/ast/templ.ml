open Core
open Common.Ext
open Common.Util
open Common.Combinator
open LogicOld

let avoid_ite_const = false
let avoid_ite_coeffs = false

let gen_params_0d sort size =
  Array.init size ~f:(fun i ->
      Term.mk_var
        (Ident.mk_fresh_parameter ())
        (if i = 0 && Term.is_bv_sort sort then sort else T_int.SInt))

let gen_params_1d sort d1 size =
  Array.init d1 ~f:(fun _ -> gen_params_0d sort size)

let gen_params_2d sort d1 d2 size =
  Array.init d1 ~f:(fun _ -> gen_params_1d sort d2 size)

let gen_params_2d_flex sort d1 shp size =
  Array.init d1 ~f:(fun i -> gen_params_1d sort (List.nth_exn shp i) size)

let gen_params_2d_flex_variant sort d1 shp size =
  Array.init (max 1 d1) ~f:(fun i ->
      gen_params_1d sort (if d1 >= 1 then List.nth_exn shp i else 1) size)

let gen_params_3d_flex sort d1 d2 shp size =
  Array.init d1 ~f:(fun _ -> gen_params_2d_flex sort d2 shp size)

let mk_const_bounds_int t lb ub seeds =
  let t = T_irb.cast (Term.sort_of t, T_int.SInt) t in
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
  if avoid_ite_coeffs && norm_type = 1 then (* ToDO: support bitvectors *)
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
    let ts =
      List.map ts ~f:(fun t -> T_irb.cast (Term.sort_of t, T_int.SInt) t)
    in
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

let quals_over_set quals params =
  let vs = Set.Poly.of_list @@ List.map ~f:fst params in
  Set.filter quals ~f:(fun q -> Set.is_subset (Formula.tvs_of q) ~of_:vs)

let terms_over terms params =
  let vs = Set.Poly.of_list @@ List.map ~f:fst params in
  List.filter terms ~f:(fun t -> Set.is_subset (Term.tvs_of t) ~of_:vs)

let terms_over_set terms params =
  let vs = Set.Poly.of_list @@ List.map ~f:fst params in
  Set.filter terms ~f:(fun t -> Set.is_subset (Term.tvs_of t) ~of_:vs)

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
      | None -> gen_params_0d T_int.SInt (List.length quals)
    in
    let templ_params, templ_param_qual_map =
      List.unzip
      @@ List.mapi quals ~f:(fun i qual ->
          let (templ_param, sort), _ =
            try Term.let_var qds.(i)
            with _ -> failwith (sprintf "qds.(%d) not defined" i)
          in
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
      let qual = Formula.rename (ren_of_sort_env_list params' params) qual in
      let key = Term.mk_var templ_param T_int.SInt in
      let pos = Formula.(mk_imply (gt key (T_int.zero ())) qual) in
      let neg = Formula.(mk_imply (lt key (T_int.zero ())) (mk_neg qual)) in
      [ pos; neg ])

(** Templates for function variables *)

type templ_func = {
  templ_params : Logic.sort_env_map;
  hole_quals_map : hole_qualifiers_map;
  func : Term.t;
  expr_selectors_bounds : Formula.t;
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
    expr_selectors_bounds =
      Formula.mk_and templ1.expr_selectors_bounds templ2.expr_selectors_bounds;
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
  consts : Term.t list;
  terms : Term.t list;
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
  let nd = List.length tf_params.shp in
  if nd <= 0 then
    {
      templ_params = Map.Poly.empty;
      hole_quals_map = [];
      func = T_int.zero ();
      expr_selectors_bounds = Formula.mk_true ();
      expr_coeffs_bounds = Formula.mk_true ();
      expr_const_bounds = Formula.mk_true ();
      cond_coeffs_bounds = Formula.mk_true ();
      cond_const_bounds = Formula.mk_true ();
    }
  else
    let terms = terms_over tf_params.terms params in
    let txs =
      List.map ~f:T_irb.to_int_if_rb
      @@ List.filter ~f:T_irb.is_sirb
      @@ List.map ~f:(uncurry Term.mk_var) params
      @ terms
    in
    let ec, dc =
      ( gen_params_0d T_int.SInt nd,
        gen_params_2d_flex T_int.SInt (nd - 1) tf_params.shp
          (List.length txs + 1) )
    in
    let r_x i =
      List.fold_right (List.mapi terms ~f:Pair.make) ~init:(Term.mk_dummy sret)
        ~f:(fun (j, t) -> T_bool.ifte (Formula.eq ec.(i) (T_int.from_int j)) t)
    in
    let d_x i j =
      T_int.mk_sum
        dc.(i).(j).(0)
        (List.mapi txs ~f:(fun k -> T_int.mk_mul dc.(i).(j).(k + 1)))
    in
    let templ_params_quals, hole_quals_map, func =
      let rest, last = List.rest_last (List.init nd ~f:(fun i -> (i, r_x i))) in
      let params =
        match vret_opt with
        | None -> params
        | Some vret -> params @ [ (vret, sret) ]
      in
      List.fold_right rest
        ~init:(Set.Poly.empty, [], snd last)
        ~f:(fun (i, t1) (templ_params_quals', hole_quals_map, t2) ->
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
    let expr_selectors_map, expr_selectors_bounds =
      let params, bounds =
        List.unzip
        @@ List.init nd ~f:(fun i ->
            ( fst @@ Term.let_var ec.(i),
              [
                Formula.geq ec.(i) (T_int.zero ());
                Formula.lt ec.(i) (T_int.from_int (List.length terms));
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
             expr_selectors_map;
           ]
    in
    {
      templ_params;
      hole_quals_map;
      func;
      expr_selectors_bounds;
      expr_coeffs_bounds = Formula.mk_true () (*Dummy*);
      expr_const_bounds = Formula.mk_true () (*Dummy*);
      cond_coeffs_bounds;
      cond_const_bounds;
    }

let gen_bool_fun tf_params tf_sub_params params (vret_opt, sret) : templ_func =
  let quals = quals_over tf_params.quals params in
  gen_cond_and_exps_of_fun
    {
      tf_params with
      terms =
        (* ToDo: tf_params.terms is not used *)
        List.map quals ~f:T_bool.of_formula;
      quals;
    }
    tf_sub_params params (vret_opt, sret)

let gen_sel_expr sel_terms sel default =
  T_int.mk_case (List.length sel_terms + 1) sel (default :: sel_terms)

let gen_irb_fun tf_params tf_sub_params params (vret_opt, sret) : templ_func =
  let terms = terms_over tf_params.terms params in
  let quals, sel_terms =
    let quals = quals_over tf_params.quals params in
    if false then
      print_endline
      @@ sprintf "[%s] quals:\n%s"
           (Option.str_of "" Ident.name_of_tvar vret_opt)
           (String.concat_map_list ~sep:"\n" quals ~f:Formula.str_of);
    if false then
      print_endline
      @@ sprintf "[%s] terms:\n%s"
           (Option.str_of "" Ident.name_of_tvar vret_opt)
           (String.concat_map_list ~sep:"\n" terms ~f:Term.str_of);
    let consts =
      List.filter tf_params.consts ~f:(Term.sort_of >> Stdlib.( = ) sret)
    in
    if false then
      print_endline
      @@ sprintf "[%s] consts:\n%s"
           (Option.str_of "" Ident.name_of_tvar vret_opt)
           (String.concat_map_list ~sep:"\n" consts ~f:Term.str_of);
    let sel_terms =
      List.unique
      @@ List.filter terms ~f:(fun t -> Stdlib.(Term.sort_of t = sret))
      @ (if false (*ToDo*) then []
         else
           List.concat_map consts ~f:(fun c ->
               match Term.sort_of c with
               | T_int.SInt when true -> [ c ]
               | T_real.SReal when true -> [ c ]
               | T_bv.SBV _ as s ->
                   [
                     c;
                     Evaluator.simplify_term
                     @@ T_irb.sub_of s c (T_irb.one_of s);
                     (*Evaluator.simplify_term
                     @@ T_irb.add_of s c (T_irb.one_of s);*)
                   ]
               | _ -> []))
      @
      match sret with
      | T_int.SInt when false (*ToDo*) ->
          [
            T_int.mk_int @@ min_num 32 true;
            T_int.mk_int @@ max_num 32 true;
            T_int.mk_int @@ min_num 32 false;
            T_int.mk_int @@ max_num 32 false;
          ]
      | T_bv.SBV size ->
          [
            T_bv.bvmin ~size ~signed:(Some true) ();
            T_bv.bvmax ~size ~signed:(Some true) ();
            T_bv.bvmin ~size ~signed:(Some false) ();
            T_bv.bvmax ~size ~signed:(Some false) ();
          ]
      | _ -> []
    in
    if false then
      print_endline
      @@ sprintf "[gen_irb_fun] sel_terms: %s"
           (String.concat_map_list ~sep:", " ~f:Term.str_of sel_terms);
    (quals, sel_terms)
  in
  let nd = List.length tf_params.shp in
  let ec = gen_params_0d T_int.SInt (max 1 nd) in
  let expr_selectors_bounds =
    Formula.and_of
    @@ List.init (Array.length ec) ~f:(fun i ->
        Formula.and_of
        @@ Formula.mk_range ec.(i) Z.zero (Z.of_int (List.length sel_terms)))
  in
  if nd <= 0 then
    {
      templ_params =
        Map.Poly.of_alist_exn @@ Logic.of_old_sort_env_list
        @@ List.map ~f:(Term.let_var >> fst)
        @@ Array.to_list ec;
      hole_quals_map = [];
      func = gen_sel_expr sel_terms ec.(0) (Term.mk_dummy sret);
      expr_selectors_bounds;
      expr_coeffs_bounds = Formula.mk_true ();
      expr_const_bounds = Formula.mk_true ();
      cond_coeffs_bounds = Formula.mk_true ();
      cond_const_bounds = Formula.mk_true ();
    }
  else
    let txs =
      List.filter ~f:T_irb.is_sirb
      @@ List.map ~f:(uncurry Term.mk_var) params
      @ terms
    in
    let num_terms = List.map txs ~f:(fun t -> (t, Term.sort_of t)) in
    let num_sort = T_irb.num_sort_of num_terms in
    let rc, dc =
      ( gen_params_1d sret nd (List.length txs + 1),
        gen_params_2d_flex_variant num_sort (nd - 1) tf_params.shp
          (List.length txs + 1) )
    in
    let r_x i = T_irb.affine_exp_of sret rc.(i) num_terms in
    let d_x i j = T_irb.affine_exp_of num_sort dc.(i).(j) num_terms in
    let templ_params_quals, hole_quals_map, func =
      let rest, last = List.rest_last (List.init nd ~f:(fun i -> (i, r_x i))) in
      let params =
        match vret_opt with
        | None -> params
        | Some vret -> params @ [ (vret, sret) ]
      in
      List.fold_right rest
        ~init:
          (Set.Poly.empty, [], gen_sel_expr sel_terms ec.(fst last) (snd last))
        ~f:(fun (i, t1) (templ_params_quals', hole_quals_map, t2) ->
          let templ_params_quals, quals, hole =
            gen_hole_for_qualifiers (params, quals)
          in
          ( Set.union templ_params_quals templ_params_quals',
            (hole, quals) :: hole_quals_map,
            let cond =
              Formula.and_of
              @@ mk_pvar_app (Ident.name_of_tvar hole) params
                 :: List.init (List.nth_exn tf_params.shp i) ~f:(fun j ->
                     Formula.mk_atom
                     @@ T_irb.geq_of num_sort (d_x i j) (T_irb.zero_of num_sort))
            in
            T_bool.ifte cond (gen_sel_expr sel_terms ec.(i) t1) t2 ))
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
        @@ Array.to_list ec
        @ (List.concat_map ~f:Array.to_list @@ Array.to_list rc)
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
      expr_selectors_bounds;
      expr_coeffs_bounds;
      expr_const_bounds;
      cond_coeffs_bounds;
      cond_const_bounds;
    }

let gen_dt_fun tf_params tf_sub_params params (vret_opt, sret) : templ_func =
  let quals = quals_over tf_params.quals params in
  let int_terms =
    List.dedup_and_sort ~compare:Stdlib.compare
    @@ List.filter ~f:T_int.is_sint
    @@ Term.of_sort_env params
    @ terms_over tf_params.terms params
  in
  let dc = gen_params_1d T_int.SInt tf_params.ext (List.length int_terms + 1) in
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
    @@ Set.Poly.of_list @@ Term.of_sort_env params
    @ List.init tf_params.ext ~f:(fun i ->
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
      func = T_real.rzero ();
      expr_selectors_bounds = Formula.mk_true ();
      expr_coeffs_bounds = Formula.mk_true ();
      expr_const_bounds = Formula.mk_true ();
      cond_coeffs_bounds = Formula.mk_true ();
      cond_const_bounds = Formula.mk_true ();
    }
  else
    let terms = terms_over tf_params.terms params in
    let txs =
      List.map ~f:T_irb.to_real_if_int
      @@ List.filter ~f:T_irb.is_sint_sreal
      @@ List.map ~f:(uncurry Term.mk_var) params
      @ if is_integ then [] else terms
    in
    let rc, dc =
      ( gen_params_1d T_int.SInt nd (List.length txs + 1),
        gen_params_2d_flex_variant T_int.SInt (nd - 1) tf_params.shp
          (if is_integ then List.length txs else List.length txs + 1) )
    in
    let r_x i =
      (if is_integ then Fn.id else T_real.mk_rabs ~info:Dummy)
      @@ T_real.mk_rsum
           (T_irb.mk_int_to_real rc.(i).(0))
           (List.mapi txs ~f:(fun j ->
                T_real.mk_rmul (T_irb.mk_int_to_real rc.(i).(j + 1))))
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
      let params = params @ [ (vret, sret) ] in
      let quals =
        List.filter ~f:(fun qual ->
            let tvs = Formula.tvs_of qual in
            (not is_integ)
            || not
               @@ Set.mem tvs (fst @@ fst @@ Term.let_var @@ List.last_exn txs))
        @@ quals_over tf_params.quals params
      in
      List.fold_right rest
        ~init:(Set.Poly.empty, [], snd last)
        ~f:(fun (i, t1) (templ_params_quals', hole_quals_map, t2) ->
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
      expr_selectors_bounds = Formula.mk_true () (*Dummy*);
      expr_coeffs_bounds;
      expr_const_bounds;
      cond_coeffs_bounds;
      cond_const_bounds;
    }

let gen_fun_bool_branch ~ignore_bool ~f params : templ_func =
  let rec aux = function
    | [] -> f ()
    | (x, sort) :: xs ->
        assert (Term.is_bool_sort sort);
        let templ1 = aux xs in
        let templ2 = aux xs in
        ite_templ (Formula.of_bool_var x) templ1 templ2
  in
  aux
    (if ignore_bool then [] else List.filter params ~f:(snd >> Term.is_bool_sort))

let rec gen_fun ~ignore_bool tf_params tf_sub_params params ret : templ_func =
  gen_fun_bool_branch ~ignore_bool
    ~f:(fun () ->
      (match ret with
      | _, T_bool.SBool -> gen_bool_fun
      | _, (T_int.SInt | T_real.SReal | T_bv.SBV _) -> gen_irb_fun
      | _, T_array.SArray _ -> gen_array_fun
      | _, T_dt.SDT _ -> gen_dt_fun
      | _, sort ->
          failwith
          @@ sprintf "[gen_fun] %s not supported" (Term.str_of_sort sort))
        tf_params tf_sub_params params ret)
    params

and gen_array_fun tf_params tf_sub_params params (vret_opt, sret) : templ_func =
  match sret with
  | T_array.SArray (sidx, selm) -> (
      try
        assert (tf_params.depth <> 0);
        let templ_elem =
          gen_fun ~ignore_bool:true tf_params tf_sub_params params
            (vret_opt, selm)
          (*ToDo:sidx is ignored*)
        in
        {
          templ_elem with
          func = T_array.mk_const_array sidx selm templ_elem.func;
        }
      with _ ->
        {
          templ_params = Map.Poly.empty;
          hole_quals_map = [];
          func = Term.mk_dummy sret;
          expr_selectors_bounds = Formula.mk_true ();
          expr_coeffs_bounds = Formula.mk_true ();
          expr_const_bounds = Formula.mk_true ();
          cond_coeffs_bounds = Formula.mk_true ();
          cond_const_bounds = Formula.mk_true ();
        })
  | _ -> failwith "gen_array_fun"

let gen_prop ~ignore_bool ?(is_integ = false) tf_params tf_sub_params params ret
    : templ_func =
  gen_fun_bool_branch ~ignore_bool
    ~f:(fun () ->
      (match ret with
      | _, T_real.SReal -> gen_prop_fun
      | _, T_tuple.STuple sorts when List.for_all sorts ~f:Term.is_real_sort ->
          gen_prop_fun
      | _, sort ->
          failwith
          @@ sprintf "[gen_prop] %s not supported" (Term.str_of_sort sort))
        ~is_integ tf_params tf_sub_params params ret)
    params

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
  consts : Term.t list;
  terms : Term.t list;
  quals : Formula.t list;
  shp : int list;
  ubc : Z.t option;
  ubd : Z.t option;
  s : Z.t Set.Poly.t;
}

type pred_tfsp = { bec : Z.t option }

let gen_dnf ?(eq_atom = false) ~br_bools ~only_bools tf_params tfs_params params
    : templ_pred =
  let terms =
    let terms =
      List.map ~f:(fun t -> (t, Term.sort_of t))
      @@ Term.of_sort_env params
      @ terms_over tf_params.terms params
    in
    if only_bools then List.filter terms ~f:(snd >> Term.is_bool_sort)
    else terms
  in
  let gen_atom_templ =
    (* generate template affine equality (if eq_atom) or inequality (otherwise) *)
    T_irb.(if eq_atom then eq_of else ineq_of) @@ T_irb.num_sort_of terms
  in
  let num_ts = T_irb.num_terms_of terms in
  let ( templ_paramss,
        hole_quals_map,
        disjuncs,
        coeffs_bounds,
        consts_bounds,
        quals_bounds ) =
    List.unzip6
    @@ List.init (List.length tf_params.shp) ~f:(fun idx ->
        let templ_paramss, preds, coeffs_bounds, consts_bounds, quals_bounds =
          List.unzip5
          @@ List.init (List.nth_exn tf_params.shp idx) ~f:(fun _ ->
              let templ_params, coeffs_const_list, pred =
                if br_bools then T_irb.br_bools_of gen_atom_templ terms
                else gen_atom_templ num_ts
              in
              let templ_paramss, coeffs_bounds, consts_bounds, quals_bounds =
                List.unzip4
                @@ List.map coeffs_const_list ~f:(fun (coeffs, const) ->
                    let pos_neg_map, coeffs_bound =
                      mk_coeffs_bounds_of_int 1 coeffs None tf_params.ubc
                        tfs_params.bec
                    in
                    let consts_bound =
                      mk_const_bounds_int const None tf_params.ubd tf_params.s
                    in
                    let quals_bound = (*ToDo*) Formula.mk_true () in
                    let templ_params =
                      Set.union pos_neg_map @@ Set.Poly.of_list
                      @@ List.map ~f:(Term.let_var >> fst) (const :: coeffs)
                    in
                    (templ_params, coeffs_bound, consts_bound, quals_bound))
              in
              ( Set.Poly.union_list @@ (templ_params :: templ_paramss),
                pred,
                Formula.and_of coeffs_bounds,
                Formula.and_of consts_bounds,
                Formula.and_of quals_bounds ))
        in
        let templ_params_quals, quals, hole =
          gen_hole_for_qualifiers (params, tf_params.quals)
        in
        ( Set.Poly.union_list (templ_params_quals :: templ_paramss),
          (hole, quals),
          Formula.and_of (mk_pvar_app (Ident.name_of_tvar hole) params :: preds),
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
  expr_selectors_bounds : Formula.t;
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
    expr_selectors_bounds = templ.expr_selectors_bounds;
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
  consts : Term.t list;
  terms : Term.t list;
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
            && not @@ Set.is_empty
               @@ AffineTerm.extract_term (rv, rs)
                    (Evaluator.simplify_term >> Normalizer.normalize_term)
                    t1
        | _ -> false)
  in
  if false then
    print_endline
    @@ sprintf "gen_int_ne_template int_terms: %s"
    @@ String.concat_map_list ~sep:"," int_terms ~f:Term.str_of;
  let dc = gen_params_0d T_int.SInt (List.length int_terms + 1) in
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
  let dc = gen_params_1d T_int.SInt tfp.ext (List.length int_terms + 1) in
  let cons_terms =
    let affines =
      List.init tfp.ext ~f:(fun i ->
          T_int.mk_sum dc.(i).(0)
          @@ List.mapi int_terms ~f:(fun j t -> T_int.mk_mul dc.(i).(j + 1) t))
    in
    Set.to_list
    @@ Datatype.enum_cons_terms tfp.dep rs
    @@ Set.Poly.of_list @@ affines
    @ List.map params ~f:(uncurry Term.mk_var)
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
        Formula.leq (T_int.mk_abs dc.(i).(0)) (T_int.mk_int @@ Z.of_int tfp.ubd))
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
  let bc = gen_params_0d T_int.SInt (List.length params + 1) in
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
      let lhs_params = List.map coeffs ~f:(Fn.flip Term.mk_var T_int.SInt) in
      ( Map.Poly.of_alist_exn
        @@ List.map coeffs ~f:(fun c -> (c, Logic.IntTerm.SInt)),
        lhs_params,
        List.map lhs_params ~f:(Formula.leq (T_int.zero ())),
        List.map2_exn lhs_params xs ~f:(fun p x ->
            T_real.mk_rmul (T_irb.mk_int_to_real p) x) )
    else (Map.Poly.empty, [], [], xs)
  in
  let templs =
    List.map pxs ~f:(fun _ ->
        gen_prop ~ignore_bool tf_params
          { lbec = None; lbcc = None; beec = None; becc = None }
          params ret)
  in
  let templ_params, pred =
    let templ_params =
      Map.force_merge_list
        (lhs_params :: List.map templs ~f:(fun t -> t.templ_params))
    in
    let funcs = List.map templs ~f:(fun t -> t.func) in
    if with_cond then
      match (xs, ps, pxs, funcs) with
      | [ x; score ], [ _; p2 ], [ px; pscore ], [ exp_x; exp_score ] ->
          let b = Ident.mk_fresh_parameter () in
          ( Map.Poly.add_exn templ_params ~key:b ~data:Logic.BoolTerm.SBool,
            let p = T_real.(mk_radd (rone ()) p2) in
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
  let expr_selectors_bounds =
    Formula.and_of @@ lhs_bounds
    @ List.map templs ~f:(fun t -> t.expr_selectors_bounds)
  in
  {
    templ_params;
    hole_quals_map = List.concat_map templs ~f:(fun t -> t.hole_quals_map);
    pred;
    expr_selectors_bounds;
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
  let lhs_params, lhs_bounds, pxs =
    if enable_lhs_param then
      let coeffs = List.map xs ~f:(fun _ -> Ident.mk_fresh_parameter ()) in
      let lhs_params = List.map coeffs ~f:(Fn.flip Term.mk_var T_int.SInt) in
      ( Map.Poly.of_alist_exn
        @@ List.map coeffs ~f:(fun c -> (c, Logic.IntTerm.SInt)),
        List.map lhs_params ~f:(Formula.leq (T_int.zero ())),
        List.map2_exn lhs_params xs ~f:(fun p x ->
            T_real.mk_rmul
              (T_irb.mk_int_to_real (*ToDo*) T_int.(mk_add p (mk_int Z.one)))
              x) )
    else (Map.Poly.empty, [], xs)
  in
  let templs =
    List.map pxs ~f:(fun _ ->
        gen_prop ~ignore_bool ~is_integ:true tf_params
          { lbec = None; lbcc = None; beec = None; becc = None }
          params ret)
  in
  let templ_params, pred =
    let templ_params =
      Map.force_merge_list
        (lhs_params :: List.map templs ~f:(fun t -> t.templ_params))
    in
    ( templ_params,
      Formula.and_of
      @@ List.map2_exn pxs
           (List.map templs ~f:(fun t -> t.func))
           ~f:(fun x exp_x ->
             Formula.mk_and
               (Formula.leq (T_real.rzero ()) x)
               (Formula.leq x exp_x)) )
  in
  let expr_selectors_bounds =
    Formula.and_of @@ lhs_bounds
    @ List.map templs ~f:(fun t -> t.expr_selectors_bounds)
  in
  {
    templ_params;
    hole_quals_map = List.concat_map templs ~f:(fun t -> t.hole_quals_map);
    pred;
    expr_selectors_bounds;
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
  rfun_selectors_bounds : Formula.t;
  rfun_coeffs_bounds : Formula.t;
  rfun_const_bounds : Formula.t;
  disc_coeffs_bounds : Formula.t;
  disc_const_bounds : Formula.t;
}

type wf_pred_tfp = {
  consts : Term.t list;
  terms : Term.t list;
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
  let txs, tys =
    let irb_params = List.filter params ~f:(snd >> Term.is_irb_sort) in
    let size = List.length irb_params / 2 in
    let irb_params_x, irb_params_y = List.split_n irb_params size in
    ( List.map ~f:T_irb.to_int_if_rb (Term.of_sort_env irb_params_x),
      List.map ~f:T_irb.to_int_if_rb (Term.of_sort_env irb_params_y) )
  in
  let np = List.length tfp.shp in
  let rc, dc =
    ( gen_params_2d T_int.SInt tfp.nl np (List.length txs + 1),
      gen_params_3d_flex T_int.SInt tfp.nl
        (if use_ifte then np - 1 else np)
        tfp.shp
        (List.length txs + 1) )
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
                 Formula.geq (rfun_x l) (T_int.mk_add (rfun_y l) (T_int.one ())))
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
                   mk_const_bounds_int dc.(i).(j).(k).(0) None tfp.ubdd tfp.ds)))
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
    rfun_selectors_bounds = Formula.mk_true ();
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

let ts_of_sort_env_list params tfp =
  let consts =
    if true then [] else List.unique @@ List.filter tfp.consts ~f:T_irb.is_sirb
  in
  consts @ Term.of_sort_env params

let sel_terms_of quals terms =
  List.unique
  (* filter out trivial candidates *)
  @@ List.filter_map ~f:(fun t ->
      if
        Term.is_var t
        || T_int.(is_neg t && (Term.is_var @@ fst @@ let_neg t))
        || T_real.(is_rneg t && (Term.is_var @@ fst @@ let_rneg t))
        || T_bv.(is_bvneg t && (Term.is_var @@ Triple.snd @@ let_bvneg t))
      then None
      else Some t)
  @@ List.map ~f:(fun t ->
      if
        T_int.(
          is_add t
          && (is_int @@ Triple.fst @@ let_add t)
          && Z.Compare.(let_int @@ Triple.fst @@ let_add t <= Z.zero))
      then Triple.snd @@ T_int.let_add t
      else t)
  @@ List.map ~f:(Normalizer.normalize_term >> Evaluator.simplify_term)
  @@ List.filter ~f:(Term.fvs_of >> Set.is_empty >> not)
  @@ List.filter ~f:T_irb.is_sirb
  @@ terms
  @ List.concat_map quals ~f:(function
    | Formula.Atom (Atom.App (Predicate.Psym psym, [ lhs; rhs ], _), _) -> (
        match (Term.sort_of lhs, psym) with
        | T_int.SInt, T_bool.(Eq | Neq) ->
            let t1 = T_int.mk_sub rhs lhs in
            let t2 = T_int.mk_sub lhs rhs in
            let tabs = T_bool.ifte (Formula.geq t1 (T_int.zero ())) t1 t2 in
            let tmod_dist8 =
              T_bool.ifte
                (Formula.mk_atom @@ T_int.mk_geq t1 (T_int.zero ()))
                t1
                (T_int.mk_sub (T_int.mk_int (Z.of_int 256)) t2)
            in
            (t1 :: t2 :: (if false then [ tabs ] else []))
            @ if false then [ tmod_dist8 ] else []
        | T_int.SInt, T_int.(Leq | Lt | Geq | Gt) ->
            let t1 = T_int.mk_sub rhs lhs in
            let t2 = T_int.mk_sub lhs rhs in
            [ t1; t2 ]
        | T_real.SReal, T_bool.(Eq | Neq) ->
            let t1 = T_int.mk_sub rhs lhs in
            let t2 = T_int.mk_sub lhs rhs in
            let tabs = T_bool.ifte (Formula.geq t1 (T_real.rzero ())) t1 t2 in
            t1 :: t2 :: (if false then [ tabs ] else [])
        | T_real.SReal, T_real.(RLeq | RLt | RGeq | RGt) ->
            let t1 = T_int.mk_sub rhs lhs in
            let t2 = T_int.mk_sub lhs rhs in
            [ t1; t2 ]
        | T_bv.SBV size, T_bool.(Eq | Neq) ->
            let t1 = T_bv.mk_bvsub ~size rhs lhs in
            let t2 = T_bv.mk_bvsub ~size lhs rhs in
            let tabs =
              T_bool.ifte
                (Formula.mk_atom
                @@ T_bv.mk_bvgeq ~size ~signed:(Some true) t1
                     (T_bv.bvzero ~size ()))
                t1 t2
            in
            let tmod_dist8 =
              T_bool.ifte
                (Formula.mk_atom
                @@ T_bv.mk_bvgeq ~size ~signed:(Some true) t1
                     (T_bv.bvzero ~size ()))
                t1
                (T_bv.mk_bvsub ~size (T_bv.mk_bvnum ~size (Z.of_int 256)) t2)
            in
            (t1 :: t2 :: (if true then [ tabs ] else []))
            @ if true then [ tmod_dist8 ] else []
        | T_bv.SBV size, T_bv.(BVLeq _ | BVLt _ | BVGeq _ | BVGt _) ->
            let t1 = T_bv.mk_bvsub ~size rhs lhs in
            let t2 = T_bv.mk_bvsub ~size lhs rhs in
            [ t1; t2 ]
        | _ -> [])
    | _ -> [])

let mk_decrease ?(strict = true) tfp tsfp np params num_sort
    (rc, dc, ren_x_y, quals_x, num_txs, num_tys, sel_terms_x) =
  let templ_params_quals, hole_quals_map, holes =
    let templ_params_qualss, hole_quals_maps, holes =
      List.unzip3
      @@ List.init np ~f:(fun i ->
          let templ_params_quals, quals_x, hole =
            gen_hole_for_qualifiers (params, quals_x)
          in
          let quals_y =
            List.map quals_x
              ~f:(Pair.map_snd (Pair.map_snd (Formula.rename ren_x_y)))
          in
          let hole_x_name = Ident.name_of_tvar hole ^ "_x" in
          let hole_y_name = Ident.name_of_tvar hole ^ "_y" in
          ( templ_params_quals,
            [
              (Ident.Tvar hole_x_name, quals_x);
              (Ident.Tvar hole_y_name, quals_y);
            ],
            (i, (mk_pvar_app hole_x_name params, mk_pvar_app hole_y_name params))
          ))
    in
    (Set.Poly.union_list templ_params_qualss, List.concat hole_quals_maps, holes)
  in
  let pred =
    let r_x i j =
      gen_sel_expr sel_terms_x rc.(i).(j).(Array.length rc.(i).(j) - 1)
      @@ T_irb.affine_exp_of num_sort rc.(i).(j) num_txs
    in
    let sel_terms_y = List.map sel_terms_x ~f:(Term.rename ren_x_y) in
    let r_y i j =
      gen_sel_expr sel_terms_y rc.(i).(j).(Array.length rc.(i).(j) - 1)
      @@ T_irb.affine_exp_of num_sort rc.(i).(j) num_tys
    in
    let d_x i j = T_irb.affine_exp_of num_sort dc.(i).(j) num_txs in
    let d_y i j = T_irb.affine_exp_of num_sort dc.(i).(j) num_tys in
    let disc_x i =
      Formula.and_of
      @@ (if false then []
          else [ fst @@ List.Assoc.find_exn ~equal:Stdlib.( = ) holes i ])
      @ List.init (List.nth_exn tfp.shp i) ~f:(fun j ->
          Formula.mk_atom
          @@ T_irb.geq_of num_sort (d_x i j) (T_irb.zero_of num_sort))
    in
    let disc_y i =
      Formula.and_of
      @@ (if false then []
          else [ snd @@ List.Assoc.find_exn ~equal:Stdlib.( = ) holes i ])
      @ List.init (List.nth_exn tfp.shp i) ~f:(fun j ->
          Formula.mk_atom
          @@ T_irb.geq_of num_sort (d_y i j) (T_irb.zero_of num_sort))
    in
    let d_y_geq_zero = Formula.or_of @@ List.init np ~f:disc_y in
    let ldec i j =
      let phi =
        Formula.or_of
        @@ List.init tfp.nl ~f:(fun k ->
            Formula.and_of
            @@ (Formula.mk_atom
               @@ T_irb.geq_of num_sort (r_x i k) (T_irb.zero_of num_sort))
               :: T_irb.gt_of num_sort (r_x i k) (r_y j k)
               :: List.init k ~f:(fun l ->
                   Formula.or_of
                     [
                       Formula.and_of
                         [
                           T_irb.gt_of num_sort (T_irb.zero_of num_sort)
                             (r_x i l);
                           T_irb.gt_of num_sort (T_irb.zero_of num_sort)
                             (r_y j l);
                         ];
                       Formula.mk_atom
                       @@ T_irb.geq_of num_sort (r_x i l) (r_y j l);
                     ]))
      in
      if strict then phi
      else
        Formula.or_of
          [
            phi;
            Formula.and_of
            @@ List.init tfp.nl ~f:(fun l ->
                Formula.or_of
                  [
                    Formula.and_of
                      [
                        T_irb.gt_of num_sort (T_irb.zero_of num_sort) (r_x i l);
                        T_irb.gt_of num_sort (T_irb.zero_of num_sort) (r_y j l);
                      ];
                    Formula.mk_atom @@ T_irb.geq_of num_sort (r_x i l) (r_y j l);
                  ]);
          ]
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
  let rfun_selectors_bounds =
    Formula.and_of
    @@ List.init np ~f:(fun i ->
        Formula.and_of
        @@ List.init tfp.nl ~f:(fun j ->
            let tx = rc.(i).(j).(Array.length rc.(i).(j) - 1) in
            Formula.and_of
            @@ Formula.mk_range tx Z.zero (Z.of_int @@ List.length sel_terms_x)))
  in
  let rfun_pos_neg_map, rfun_coeffs_bounds =
    let rfun_pos_neg_mapss, phiss =
      List.unzip
      @@ List.init np ~f:(fun i ->
          List.unzip
          @@ List.init tfp.nl ~f:(fun j ->
              mk_coeffs_bounds_of_int tsfp.norm_type
                (Array.to_list
                @@ Array.slice rc.(i).(j) 1 (Array.length rc.(i).(j) - 1))
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
    let disc_pos_neg_maps, phis =
      List.unzip
      @@ List.init np ~f:(fun i ->
          let disc_pos_neg_maps, phis =
            List.unzip
            @@ List.init (List.nth_exn tfp.shp i) ~f:(fun j ->
                mk_coeffs_bounds_of_int tsfp.norm_type
                  (Array.to_list
                  @@ Array.slice dc.(i).(j) 1 (Array.length dc.(i).(j)))
                  tsfp.lbdc tfp.ubdc tsfp.bedc)
          in
          (Set.Poly.union_list disc_pos_neg_maps, Formula.and_of phis))
    in
    (Set.Poly.union_list disc_pos_neg_maps, Formula.and_of phis)
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
    rfun_selectors_bounds;
    rfun_coeffs_bounds;
    rfun_const_bounds;
    disc_coeffs_bounds;
    disc_const_bounds;
  }

let gen_simplified_wf_predicate tfp tsfp params : templ_wf_pred =
  assert (List.length params mod 2 = 0);
  let params_x, params_y = List.split_n params (List.length params / 2) in
  let ren_x_y, ren_y_x =
    ( ren_of_sort_env_list params_x params_y,
      ren_of_sort_env_list params_y params_x )
  in
  let quals_x = quals_over tfp.quals params_x in
  let sel_terms_x =
    sel_terms_of quals_x
      (List.map ~f:(Term.rename ren_y_x) (size_fun_apps params @ tfp.terms))
  in
  let txs, tys =
    let irb_params = List.filter params ~f:(snd >> Term.is_irb_sort) in
    let size = List.length irb_params / 2 in
    let irb_params_x, irb_params_y = List.split_n irb_params size in
    (ts_of_sort_env_list irb_params_x tfp, ts_of_sort_env_list irb_params_y tfp)
  in
  let num_txs = List.map txs ~f:(fun t -> (t, Term.sort_of t)) in
  let num_tys = List.map tys ~f:(fun t -> (t, Term.sort_of t)) in
  let num_sort = T_irb.num_sort_of (num_txs @ num_tys) in
  let sel_terms_x =
    List.map sel_terms_x ~f:(fun t -> T_irb.cast (Term.sort_of t, num_sort) t)
  in
  if false then
    print_endline
    @@ sprintf "[gen_simplified_wf_predicate] sel_terms_x: %s"
         (String.concat_map_list ~sep:", " ~f:Term.str_of sel_terms_x);
  let np = List.length tfp.shp in
  let rc, dc =
    ( gen_params_2d num_sort np tfp.nl (List.length txs + 1 + 1 (*selector*)),
      gen_params_2d_flex num_sort np tfp.shp (List.length txs + 1) )
  in
  mk_decrease tfp tsfp np params num_sort
    (rc, dc, ren_x_y, quals_x, num_txs, num_tys, sel_terms_x)

let find_and_update tbl key ~f =
  match Hashtbl.Poly.find tbl key with
  | Some data -> data
  | None ->
      let data = f key in
      Hashtbl.Poly.add_exn tbl ~key ~data;
      data

let mk_decrease ?(strict = true) tfp tsfp np params num_sort
    (rc_x, dc_x, qd_x, tag_x, quals_x, num_txs, sel_terms_x)
    (rc_y, dc_y, qd_y, tag_y, quals_y, num_tys, sel_terms_y) =
  let templ_params_quals, hole_quals_map, holes =
    let templ_params_qualss, hole_quals_maps, holes =
      List.unzip3
      @@ List.init np ~f:(fun i ->
          let templ_params_quals_x, quals_x, hole_x =
            if false then
              print_endline @@ "quals_x: "
              ^ String.concat_map_list ~sep:", " ~f:Formula.str_of quals_x;
            gen_hole_for_qualifiers ~qds:(Some qd_x.(i)) (params, quals_x)
          in
          let templ_params_quals_y, quals_y, hole_y =
            if false then
              print_endline @@ "quals_y: "
              ^ String.concat_map_list ~sep:", " ~f:Formula.str_of quals_y;
            gen_hole_for_qualifiers ~qds:(Some qd_y.(i)) (params, quals_y)
          in
          let hole_x_name = Ident.name_of_tvar hole_x ^ "_x" in
          let hole_y_name = Ident.name_of_tvar hole_y ^ "_y" in
          ( Set.union templ_params_quals_x templ_params_quals_y,
            [
              (Ident.Tvar hole_x_name, quals_x);
              (Ident.Tvar hole_y_name, quals_y);
            ],
            (i, (mk_pvar_app hole_x_name params, mk_pvar_app hole_y_name params))
          ))
    in
    (Set.Poly.union_list templ_params_qualss, List.concat hole_quals_maps, holes)
  in
  let pred =
    let r_x i j =
      gen_sel_expr sel_terms_x rc_x.(i).(j).(Array.length rc_x.(i).(j) - 1)
      @@ T_irb.affine_exp_of num_sort rc_x.(i).(j) num_txs
    in
    let r_y i j =
      gen_sel_expr sel_terms_y rc_y.(i).(j).(Array.length rc_y.(i).(j) - 1)
      @@ T_irb.affine_exp_of num_sort rc_y.(i).(j) num_tys
    in
    let d_x i j = T_irb.affine_exp_of num_sort dc_x.(i).(j) num_txs in
    let d_y i j = T_irb.affine_exp_of num_sort dc_y.(i).(j) num_tys in
    let disc_x i =
      Formula.and_of
      @@ (fst @@ List.Assoc.find_exn ~equal:Stdlib.( = ) holes i)
         :: List.init (List.nth_exn tfp.shp i) ~f:(fun j ->
             Formula.mk_atom
             @@ T_irb.geq_of num_sort (d_x i j) (T_irb.zero_of num_sort))
    in
    let disc_y i =
      Formula.and_of
      @@ (snd @@ List.Assoc.find_exn ~equal:Stdlib.( = ) holes i)
         :: List.init (List.nth_exn tfp.shp i) ~f:(fun j ->
             Formula.mk_atom
             @@ T_irb.geq_of num_sort (d_y i j) (T_irb.zero_of num_sort))
    in
    let d_y_geq_zero = Formula.or_of @@ List.init np ~f:disc_y in
    let ldec i j =
      let phi =
        Formula.or_of
        @@ List.init tfp.nl ~f:(fun k ->
            Formula.and_of
            @@ (Formula.mk_atom
               @@ T_irb.geq_of num_sort (r_x i k) (T_irb.zero_of num_sort))
               :: T_irb.gt_of num_sort (r_x i k) (r_y j k)
               :: List.init k ~f:(fun l ->
                   Formula.or_of
                     [
                       Formula.and_of
                         [
                           T_irb.gt_of num_sort (T_irb.zero_of num_sort)
                             (r_x i l);
                           T_irb.gt_of num_sort (T_irb.zero_of num_sort)
                             (r_y j l);
                         ];
                       Formula.mk_atom
                       @@ T_irb.geq_of num_sort (r_x i l) (r_y j l);
                     ]))
      in
      if strict then phi
      else
        Formula.or_of
          [
            phi;
            Formula.and_of
            @@ List.init tfp.nl ~f:(fun l ->
                Formula.or_of
                  [
                    Formula.and_of
                      [
                        T_irb.gt_of num_sort (T_irb.zero_of num_sort) (r_x i l);
                        T_irb.gt_of num_sort (T_irb.zero_of num_sort) (r_y j l);
                      ];
                    Formula.mk_atom @@ T_irb.geq_of num_sort (r_x i l) (r_y j l);
                  ]);
          ]
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
  let rfun_selectors_bounds =
    Formula.and_of
    @@ List.init np ~f:(fun i ->
        Formula.and_of @@ List.concat
        @@ List.init tfp.nl ~f:(fun j ->
            Formula.mk_range
              rc_x.(i).(j).(Array.length rc_x.(i).(j) - 1)
              Z.zero
              (Z.of_int @@ List.length sel_terms_x)
            @ Formula.mk_range
                rc_y.(i).(j).(Array.length rc_y.(i).(j) - 1)
                Z.zero
                (Z.of_int @@ List.length sel_terms_y)))
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
                  @@ Array.slice rc_x.(i).(j) 1 (Array.length rc_x.(i).(j) - 1)
                  )
                  tsfp.lbrc tfp.ubrc tsfp.berc)
          in
          let rfun_pos_neg_maps_y, phis_y =
            if Stdlib.(tag_x = tag_y) then ([], [])
            else
              List.unzip
              @@ List.init tfp.nl ~f:(fun j ->
                  mk_coeffs_bounds_of_int tsfp.norm_type
                    (Array.to_list
                    @@ Array.slice rc_y.(i).(j) 1 (Array.length rc_y.(i).(j) - 1)
                    )
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
    if Stdlib.(tag_x = tag_y) then []
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
                  @@ Array.slice dc_x.(i).(j) 1 (Array.length dc_x.(i).(j)))
                  tsfp.lbdc tfp.ubdc tsfp.bedc)
          in
          let disc_pos_neg_maps_y, phis_y =
            if Stdlib.(tag_x = tag_y) then ([], [])
            else
              List.unzip
              @@ List.init (List.nth_exn tfp.shp i) ~f:(fun j ->
                  mk_coeffs_bounds_of_int tsfp.norm_type
                    (Array.to_list
                    @@ Array.slice dc_y.(i).(j) 1 (Array.length dc_y.(i).(j)))
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
    if Stdlib.(tag_x = tag_y) then []
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
    rfun_selectors_bounds;
    rfun_coeffs_bounds;
    rfun_const_bounds;
    disc_coeffs_bounds;
    disc_const_bounds;
  }

let gen_simplified_nwf_predicate (rcs, dcs, qds) tfp tsfp
    ( params_shared,
      (tag_x : Ident.tvar),
      params_x,
      (tag_y : Ident.tvar),
      params_y ) (quals_x, terms_x) (quals_y, terms_y) : templ_wf_pred =
  let params = params_shared @ params_x @ params_y in
  let sel_terms_x =
    sel_terms_of quals_x (size_fun_apps (params_shared @ params_x) @ terms_x)
  in
  let sel_terms_y =
    sel_terms_of quals_y (size_fun_apps (params_shared @ params_y) @ terms_y)
  in
  if false then
    print_endline
    @@ sprintf "[gen_simplified_nwf_predicate] sel_terms_x: %s"
         (String.concat_map_list ~sep:", " ~f:Term.str_of sel_terms_x);
  if false then
    print_endline
    @@ sprintf "[gen_simplified_nwf_predicate] sel_terms_y: %s"
         (String.concat_map_list ~sep:", " ~f:Term.str_of sel_terms_y);
  let num_txs, num_tys =
    let txs, tys =
      ( ts_of_sort_env_list (params_shared @ params_x) tfp,
        ts_of_sort_env_list (params_shared @ params_y) tfp )
    in
    ( List.map txs ~f:(fun t -> (t, Term.sort_of t)),
      List.map tys ~f:(fun t -> (t, Term.sort_of t)) )
  in
  let num_sort = T_irb.num_sort_of (num_txs @ num_tys) in
  let sel_terms_x =
    List.map sel_terms_x ~f:(fun t -> T_irb.cast (Term.sort_of t, num_sort) t)
  in
  let sel_terms_y =
    List.map sel_terms_y ~f:(fun t -> T_irb.cast (Term.sort_of t, num_sort) t)
  in
  let np = List.length tfp.shp in
  let rc_x, rc_y, dc_x, dc_y, qd_x, qd_y =
    ( find_and_update rcs tag_x ~f:(fun _ ->
          gen_params_2d num_sort np tfp.nl
            (List.length num_txs + 1 + 1 (*selector*))),
      find_and_update rcs tag_y ~f:(fun _ ->
          gen_params_2d num_sort np tfp.nl
            (List.length num_tys + 1 + 1 (*selector*))),
      find_and_update dcs tag_x ~f:(fun _ ->
          gen_params_2d_flex num_sort np tfp.shp (List.length num_txs + 1)),
      find_and_update dcs tag_y ~f:(fun _ ->
          gen_params_2d_flex num_sort np tfp.shp (List.length num_tys + 1)),
      find_and_update qds tag_x ~f:(fun _ ->
          gen_params_1d num_sort np (List.length quals_x)),
      find_and_update qds tag_y ~f:(fun _ ->
          gen_params_1d num_sort np (List.length quals_y)) )
  in
  mk_decrease ~strict:true tfp tsfp np params num_sort
    (rc_x, dc_x, qd_x, tag_x, quals_x, num_txs, sel_terms_x)
    (rc_y, dc_y, qd_y, tag_y, quals_y, num_tys, sel_terms_y)

let merge_list op ts =
  List.fold ~init:(List.hd_exn ts) (List.tl_exn ts) ~f:(fun t1 t2 ->
      {
        templ_params = Map.force_merge t1.templ_params t2.templ_params;
        hole_quals_map = t1.hole_quals_map @ t2.hole_quals_map;
        pred = op [ t1.pred; t2.pred ];
        rfun_selectors_bounds =
          Formula.and_of [ t1.rfun_selectors_bounds; t2.rfun_selectors_bounds ];
        rfun_coeffs_bounds =
          Formula.and_of [ t1.rfun_coeffs_bounds; t2.rfun_coeffs_bounds ];
        rfun_const_bounds =
          Formula.and_of [ t1.rfun_const_bounds; t2.rfun_const_bounds ];
        disc_coeffs_bounds =
          Formula.and_of [ t1.disc_coeffs_bounds; t2.disc_coeffs_bounds ];
        disc_const_bounds =
          Formula.and_of [ t1.disc_const_bounds; t2.disc_const_bounds ];
      })

let gen_simplified_parity_predicate (rcs, dcs, qds)
    (max_pri, sigma, trunc, acc_set) tfp tsfp
    ((tag_x : Ident.tvar), params_x, (tag_y : Ident.tvar), params_y)
    (quals_x, terms_x) (quals_y, terms_y) : templ_wf_pred =
  let params = params_x @ params_y in
  let sel_terms_x = sel_terms_of quals_x (size_fun_apps params_x @ terms_x) in
  let sel_terms_y = sel_terms_of quals_y (size_fun_apps params_y @ terms_y) in
  if false then
    print_endline
    @@ sprintf "[gen_simplified_parity_predicate] sel_terms_x: %s"
         (String.concat_map_list ~sep:", " ~f:Term.str_of sel_terms_x);
  if false then
    print_endline
    @@ sprintf "[gen_simplified_parity_predicate] sel_terms_y: %s"
         (String.concat_map_list ~sep:", " ~f:Term.str_of sel_terms_y);
  let num_txs, num_tys =
    let txs, tys =
      (ts_of_sort_env_list params_x tfp, ts_of_sort_env_list params_y tfp)
    in
    ( List.map txs ~f:(fun t -> (t, Term.sort_of t)),
      List.map tys ~f:(fun t -> (t, Term.sort_of t)) )
  in
  let num_sort = T_irb.num_sort_of (num_txs @ num_tys) in
  let sel_terms_x =
    List.map sel_terms_x ~f:(fun t -> T_irb.cast (Term.sort_of t, num_sort) t)
  in
  let sel_terms_y =
    List.map sel_terms_y ~f:(fun t -> T_irb.cast (Term.sort_of t, num_sort) t)
  in
  let np = List.length tfp.shp in
  let rc_x, rc_y, dc_x, dc_y, qd_x, qd_y =
    ( find_and_update rcs tag_x ~f:(fun _ ->
          Array.init max_pri ~f:(fun _ ->
              gen_params_2d num_sort np tfp.nl
                (List.length num_txs + 1 + 1 (*selector*)))),
      find_and_update rcs tag_y ~f:(fun _ ->
          Array.init max_pri ~f:(fun _ ->
              gen_params_2d num_sort np tfp.nl
                (List.length num_tys + 1 + 1 (*selector*)))),
      find_and_update dcs tag_x ~f:(fun _ ->
          Array.init max_pri ~f:(fun _ ->
              gen_params_2d_flex num_sort np tfp.shp (List.length num_txs + 1))),
      find_and_update dcs tag_y ~f:(fun _ ->
          Array.init max_pri ~f:(fun _ ->
              gen_params_2d_flex num_sort np tfp.shp (List.length num_tys + 1))),
      find_and_update qds tag_x ~f:(fun _ ->
          gen_params_1d num_sort np (List.length quals_x)),
      find_and_update qds tag_y ~f:(fun _ ->
          gen_params_1d num_sort np (List.length quals_y)) )
  in
  if false then (
    print_endline
      (Ident.name_of_tvar tag_x ^ ": " ^ Int.to_string (List.length quals_x));
    print_endline
      (Ident.name_of_tvar tag_y ^ ": " ^ Int.to_string (List.length quals_y)));
  let pril = trunc @@ Map.Poly.find_exn sigma tag_x in
  let templ =
    merge_list Formula.or_of
    @@ List.init pril ~f:(fun i ->
        merge_list Formula.and_of
        @@ mk_decrease ~strict:true tfp tsfp np params num_sort
             (rc_x.(i), dc_x.(i), qd_x, tag_x, quals_x, num_txs, sel_terms_x)
             (rc_y.(i), dc_y.(i), qd_y, tag_y, quals_y, num_tys, sel_terms_y)
           :: List.init i ~f:(fun j ->
               mk_decrease ~strict:false tfp tsfp np params num_sort
                 (rc_x.(j), dc_x.(j), qd_x, tag_x, quals_x, num_txs, sel_terms_x)
                 (rc_y.(j), dc_y.(j), qd_y, tag_y, quals_y, num_tys, sel_terms_y)))
  in
  if Set.mem acc_set pril then
    merge_list Formula.or_of
    @@ [
         templ;
         merge_list Formula.and_of
         @@ List.init pril ~f:(fun j ->
             mk_decrease ~strict:false tfp tsfp np params num_sort
               (rc_x.(j), dc_x.(j), qd_x, tag_x, quals_x, num_txs, sel_terms_x)
               (rc_y.(j), dc_y.(j), qd_y, tag_y, quals_y, num_tys, sel_terms_y));
       ]
  else templ

(** Templates for quantitative predicate variables *)

type templ_quant_pred = {
  templ_params : sort_env_map;
  templ_constrs : Formula.t list;
  quant_pred : Term.t;
}

let mk_affine ?(coeffs = None) terms =
  let templ_params_list =
    List.init
      (List.length terms + 1)
      ~f:(fun _ ->
        ( (*Ident.mk_fresh_parameter ()*)
          Ident.mk_fresh_tvar ~prefix:(Some "param") (),
          T_real.SReal ))
  in
  let cs = Term.of_sort_env templ_params_list in
  (match coeffs with None -> () | Some r -> r := !r @ List.tl_exn cs);
  {
    templ_params = Map.Poly.of_alist_exn templ_params_list;
    templ_constrs = [];
    quant_pred =
      List.fold2_exn ~init:(List.hd_exn cs) (List.tl_exn cs) terms
        ~f:(fun acc c t -> T_real.mk_radd acc (T_real.mk_rmul c t));
  }

let terms_of degree args =
  Set.to_list
  @@ Set.Poly.filter_map
       (Set.subsets_with_duplicates (Term.of_sort_env args) degree)
       ~f:(function [] -> None | t :: ts -> Some (T_real.mk_rprod t ts))

let gen_quant_template ?(coeffs = None) ~use_orig_ite ~num_conds ~cond_degree
    ~term_degree args body annots : templ_quant_pred =
  let rec aux = function
    | Term.FunApp (T_bool.IfThenElse, [ cond; t1; t2 ], _) when use_orig_ite ->
        let t1' = aux t1 in
        let t2' = aux t2 in
        {
          templ_params = Map.force_merge t1'.templ_params t2'.templ_params;
          templ_constrs = t1'.templ_constrs @ t2'.templ_constrs;
          quant_pred = T_bool.mk_if_then_else cond t1'.quant_pred t2'.quant_pred;
        }
    | _ -> mk_affine ~coeffs @@ terms_of term_degree args
  in
  let init =
    List.fold_right annots ~init:(aux body) ~f:(fun cond t ->
        let t' =
          if false then aux body
          else mk_affine ~coeffs @@ terms_of term_degree args
        in
        {
          templ_params =
            Map.force_merge_list [ t'.templ_params; t.templ_params ];
          templ_constrs = t'.templ_constrs @ t.templ_constrs;
          quant_pred =
            T_bool.mk_if_then_else (T_bool.of_formula cond) t'.quant_pred
              t.quant_pred;
        })
  in
  List.fold_right (List.init num_conds ~f:Fn.id) ~init ~f:(fun _ t ->
      let cond = mk_affine @@ terms_of cond_degree args in
      let t' =
        if true then aux body
        else mk_affine ~coeffs @@ terms_of term_degree args
      in
      {
        templ_params =
          Map.force_merge_list
            [ cond.templ_params; t'.templ_params; t.templ_params ];
        templ_constrs = cond.templ_constrs @ t'.templ_constrs @ t.templ_constrs;
        quant_pred =
          T_bool.mk_if_then_else
            (T_bool.of_formula @@ Formula.geq cond.quant_pred (T_real.rzero ()))
            t'.quant_pred t.quant_pred;
      })

let gen_quant_pc_template conds terms =
  let rest, last = List.rest_last terms in
  snd
  @@ List.fold_right rest
       ~init:(List.rev conds, last)
       ~f:(fun t1 (conds, t2) ->
         ( List.tl_exn conds,
           T_bool.mk_if_then_else
             (T_bool.of_formula
             @@ Formula.geq (List.hd_exn conds) (T_real.rzero ()))
             t1 t2 ))

let underapprox_of ~cond_degree ~term_degree args t =
  let res =
    match term_degree with
    | None ->
        { templ_params = Map.Poly.empty; templ_constrs = []; quant_pred = t }
    | Some term_degree ->
        let rec aux = function
          | Term.FunApp (T_bool.IfThenElse, [ cond; t1; t2 ], _) ->
              let t1' = aux t1 in
              let t2' = aux t2 in
              {
                templ_params = Map.force_merge t1'.templ_params t2'.templ_params;
                templ_constrs = t1'.templ_constrs @ t2'.templ_constrs;
                quant_pred =
                  T_bool.mk_if_then_else cond t1'.quant_pred t2'.quant_pred;
              }
          | Term.FunApp (T_real.RAdd, [ t1; t2 ], _) ->
              let t1' = aux t1 in
              let t2' = aux t2 in
              {
                templ_params = Map.force_merge t1'.templ_params t2'.templ_params;
                templ_constrs = t1'.templ_constrs @ t2'.templ_constrs;
                quant_pred = T_real.mk_radd t1'.quant_pred t2'.quant_pred;
              }
          | Term.FunApp
              (FVar ((Ident.Tvar ("min" | "max") as fvar), sargs, sret), args, _)
            ->
              let args = List.map args ~f:aux in
              {
                templ_params =
                  Map.force_merge_list
                    (List.map args ~f:(fun a -> a.templ_params));
                templ_constrs =
                  List.concat_map args ~f:(fun a -> a.templ_constrs);
                quant_pred =
                  Term.mk_fvar_app fvar sargs sret
                    (List.map args ~f:(fun a -> a.quant_pred));
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
                  @ Formula.mk_range_real c.quant_pred Q.zero Q.one;
                quant_pred = T_real.mk_rmul c.quant_pred t;
              }
        in
        aux t
  in
  match cond_degree with
  | None -> (None, res)
  | Some cond_degree ->
      let cond = mk_affine @@ terms_of cond_degree args in
      ( Some cond.quant_pred,
        {
          templ_params = Map.force_merge res.templ_params cond.templ_params;
          templ_constrs = res.templ_constrs @ cond.templ_constrs;
          quant_pred =
            T_bool.mk_if_then_else
              (T_bool.of_formula
              @@ Formula.geq cond.quant_pred (T_real.rzero ()))
              res.quant_pred (T_real.rzero ());
        } )
