open Core
open Common.Util
open Ast
open Ast.LogicOld

let avoid_ite_const = false
let avoid_ite_coeffs = false

let mk_bounds_of_const t lb ub seeds =
  Formula.or_of @@
  List.map (Set.Poly.to_list seeds) ~f:(fun n ->
      if avoid_ite_const && Option.for_all lb ~f:(fun n -> Z.Compare.(n >= Z.zero)) &&
         Option.for_all ub ~f:(fun n -> Z.Compare.(n >= Z.zero)) then
        Formula.mk_or
          (Formula.and_of @@ Formula.mk_range_opt (T_int.mk_sub t (T_int.mk_int n)) lb ub)
          (Formula.and_of @@ Formula.mk_range_opt (T_int.mk_sub (T_int.mk_int n) t) lb ub)
      else
        let norm = T_int.abs @@ T_int.mk_sub t (T_int.mk_int n) in
        Formula.and_of @@ Formula.mk_range_opt norm lb ub)

let mk_bounds_of_coeffs norm_type ts lb ub be =
  if avoid_ite_coeffs && norm_type = 1 then
    let xps, xns = List.unzip @@ List.map ts ~f:(fun t ->
        let xp, xn =
          if Term.is_var t then
            let Ident.Tvar x, _, _ = Term.let_var t in
            Ident.Tvar (x ^ "#pos"(*ToDo*)), Ident.Tvar (x ^ "#neg"(*ToDo*))
          else (Ident.mk_fresh_tvar (), Ident.mk_fresh_tvar ()) in
        (xp, T_int.SInt), (xn, T_int.SInt)) in
    let tps = List.map xps ~f:(uncurry Term.mk_var) in
    let tns = List.map xns ~f:(uncurry Term.mk_var) in
    let ts' = List.map2_exn tps tns ~f:(fun tp tn -> T_int.mk_sub tp tn) in
    let norm = T_int.mk_sum (T_int.zero ()) (tps @ tns) in
    Set.Poly.of_list (xps @ xns),
    Formula.and_of @@
    List.map (tps @ tns) ~f:(fun t -> Formula.geq t (T_int.zero ())) @
    List.map2_exn ts ts' ~f:Formula.eq @
    Formula.mk_range_opt norm lb ub @
    match be with
    | None -> []
    | Some be -> List.concat_map ts' ~f:(fun t -> Formula.mk_range t (Z.neg be) be)
  else
    let norm =
      if norm_type = 1 then T_int.l1_norm ts
      else if norm_type = 2 then T_int.l2_norm_sq ts
      else assert false
    in
    Set.Poly.empty,
    Formula.and_of @@
    Formula.mk_range_opt norm lb ub @
    match be with
    | None -> []
    | Some be -> List.concat_map ts ~f:(fun t -> Formula.mk_range t (Z.neg be) be)

let gen_from_qualifiers (params, quals) =
  Logic.Term.mk_lambda
    (List.map ~f:Logic.ExtTerm.of_old_sort_bind @@ SortEnv.list_of params) @@
  Logic.ExtTerm.of_old_formula @@ 
  Formula.and_of @@ List.concat_map quals ~f:(fun (temp_param, (_, params', qual)) ->
      let map = Map.Poly.of_alist_exn (List.map2_exn ~f:(fun (x', _) (x, _) -> x', x) (SortEnv.list_of params') (SortEnv.list_of params)) in
      let qual = Formula.rename map qual in
      let key = Term.mk_var temp_param T_int.SInt in
      let pos = Formula.mk_imply (Formula.gt key (T_int.zero ())) qual in
      let neg = Formula.mk_imply (Formula.lt key (T_int.zero ())) (Formula.mk_neg qual) in
      [pos; neg])

let gen_hole_for_qualifiers (params, quals) =
  let hole = Ident.mk_fresh_tvar ~prefix:(Some "hole") () in
  if List.is_empty quals then Set.Poly.empty, [], hole
  else
    let temp_params, temp_param_qual_map =
      List.unzip @@ List.map quals ~f:(fun qual ->
          let temp_param = Ident.mk_fresh_parameter () in
          (temp_param, T_int.SInt),
          (temp_param, (SortEnv.of_list params, qual)))
    in
    Set.Poly.of_list temp_params, temp_param_qual_map, hole

let gen_wf_predicate use_ifte quals _terms
    (nl, np, ubrc, ubrd, ndc, ubdc, ubdd, ds)
    (norm_type, lbrc, lbdc, berc, bedc) params =
  assert (List.length params mod 2 = 0);
  let int_params = List.filter params ~f:(function _, T_int.SInt -> true | _ -> false) in
  let size = List.length int_params / 2 in
  let txs = List.map ~f:(uncurry Term.mk_var) (List.take int_params size) in
  let tys = List.map ~f:(uncurry Term.mk_var) (List.drop int_params size) in
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
  let temp_params_fun =
    Set.Poly.of_list @@ List.map ~f:(fun t -> let x, s, _ = Term.let_var t in x, s) @@
    ((List.concat_map ~f:Array.to_list @@ List.concat_map ~f:Array.to_list @@ Array.to_list rc) @
     (List.concat_map ~f:Array.to_list @@ List.concat_map ~f:Array.to_list @@ List.concat_map ~f:Array.to_list @@ Array.to_list dc))
  in
  let r_x i j =
    T_int.mk_sum rc.(i).(j).(0)
      (List.mapi ~f:(fun k -> T_int.mk_mult rc.(i).(j).(k + 1)) txs)
  in
  let r_y i j =
    T_int.mk_sum rc.(i).(j).(0)
      (List.mapi ~f:(fun k -> T_int.mk_mult rc.(i).(j).(k + 1)) tys)
  in
  let d_x i j k =
    T_int.mk_sum dc.(i).(j).(k).(0)
      (List.mapi ~f:(fun l -> T_int.mk_mult dc.(i).(j).(k).(l + 1)) txs)
  in
  let d_y i j k =
    T_int.mk_sum dc.(i).(j).(k).(0)
      (List.mapi ~f:(fun l -> T_int.mk_mult dc.(i).(j).(k).(l + 1)) tys)
  in
  let temp_params_quals, hole_quals_map, holes =
    let params_x, params_y = List.split_n params (List.length params / 2) in
    let quals = List.filter quals ~f:(fun q -> Set.Poly.is_subset (Formula.fvs_of q) ~of_:(Set.Poly.of_list @@ List.map ~f:fst params_x)) in
    List.init nl ~f:(fun i ->
        List.init np ~f:(fun j ->
            let temp_params_quals, quals_x, hole = gen_hole_for_qualifiers (params, quals) in
            let quals_y = List.map quals_x ~f:(fun (b, (senv, q)) -> b, (senv, Formula.rename (SortEnv.from_to (SortEnv.of_list params_x) (SortEnv.of_list params_y)) q)) in
            let hole_x_name = Ident.name_of_tvar hole ^ "_x" in
            let hole_y_name = Ident.name_of_tvar hole ^ "_y" in
            let hole_term_of name =
              Formula.mk_atom @@
              Atom.mk_pvar_app (Ident.Pvar name)
                (List.map ~f:snd params)
                (List.map ~f:(uncurry Term.mk_var) params)
            in
            temp_params_quals,
            [(Ident.Tvar hole_x_name, quals_x); (Ident.Tvar hole_y_name, quals_y)],
            ((i, j), (hole_term_of hole_x_name, hole_term_of hole_y_name)))
        |> List.unzip3
        |> (fun (temp_params_qualss, hole_quals_maps, holes) ->
            Set.Poly.union_list temp_params_qualss,
            List.concat hole_quals_maps,
            holes))
    |> List.unzip3
    |> (fun (temp_params_qualss, hole_quals_maps, holess) ->
        Set.Poly.union_list temp_params_qualss,
        List.concat hole_quals_maps,
        List.concat holess)
  in
  let hole_x i j = fst @@ List.Assoc.find_exn ~equal:Stdlib.(=) holes (i, j) in
  let hole_y i j = snd @@ List.Assoc.find_exn ~equal:Stdlib.(=) holes (i, j) in
  let disc_x i j =
    Formula.and_of @@ hole_x i j :: List.init ndc ~f:(fun k ->
        Formula.geq (d_x i j k) (T_int.zero ()))
  in
  let disc_y i j =
    Formula.and_of @@ hole_y i j :: List.init ndc ~f:(fun k ->
        Formula.geq (d_y i j k) (T_int.zero ()))
  in
  let rfun_x i =
    let ts = List.init np ~f:(fun j -> (j, r_x i j)) in
    List.fold_right (List.take ts (List.length ts - 1)) ~init:(snd @@ List.last_exn ts)
      ~f:(fun (j, t1) t2 -> T_bool.ifte (disc_x i j) t1 t2)
  in
  let rfun_y i =
    let ts = List.init np ~f:(fun j -> (j, r_y i j)) in
    List.fold_right (List.take ts (List.length ts - 1)) ~init:(snd @@ List.last_exn ts)
      ~f:(fun (j, t1) t2 -> T_bool.ifte (disc_y i j) t1 t2)
  in
  let tmpl =
    let r_geq_zero =
      if use_ifte then
        Formula.and_of @@ List.init nl ~f:(fun i ->
            Formula.geq (rfun_x i) (T_int.zero ()))
      else
        Formula.and_of @@ List.init nl ~f:(fun i ->
            Formula.and_of @@ List.init np ~f:(fun j ->
                Formula.mk_imply (disc_x i j) (Formula.geq (r_x i j) (T_int.zero ()))))
    in
    let d_x_geq_zero =
      if use_ifte then Formula.mk_true ()
      else
        Formula.and_of @@ List.init nl ~f:(fun i ->
            Formula.or_of @@ List.init np ~f:(fun j ->
                disc_x i j))
    in
    let d_y_geq_zero =
      if use_ifte then Formula.mk_true ()
      else
        Formula.and_of @@ List.init nl ~f:(fun i ->
            Formula.or_of @@ List.init np ~f:(fun j ->
                disc_y i j))
    in
    let x_gt_y =
      Formula.or_of @@ List.init nl ~f:(fun i ->
          Formula.and_of [
            if use_ifte then
              Formula.geq (rfun_x i) (T_int.mk_add (rfun_y i) (T_int.one ()))
            else
              Formula.or_of @@ List.init np ~f:(fun j ->
                  Formula.and_of [
                    disc_x i j;
                    Formula.and_of @@ List.init np ~f:(fun k ->
                        Formula.mk_imply
                          (disc_y i k)
                          (Formula.geq (r_x i j) (T_int.mk_add (r_y i k) (T_int.one ()))));
                  ]);
            Formula.and_of @@ List.init i ~f:(fun l ->
                if use_ifte then
                  Formula.geq (rfun_x l) (T_int.mk_add (rfun_y l) (T_int.one ()))
                else
                  Formula.or_of @@ List.init np ~f:(fun j ->
                      Formula.and_of [
                        disc_x l j;
                        Formula.and_of @@ List.init np ~f:(fun k ->
                            Formula.mk_imply
                              (disc_y l k)
                              (Formula.geq (r_x l j) (r_y l k)));
                      ]));
          ])
    in
    Formula.and_of [ r_geq_zero; d_x_geq_zero; d_y_geq_zero; x_gt_y ]
  in
  let rfun_pos_neg_map, rfun_coeffs_bounds =
    let rfun_pos_neg_maps, phis =
      List.unzip @@ List.init nl ~f:(fun i ->
          let rfun_pos_neg_maps, phis =
            List.unzip @@ List.init np ~f:(fun j ->
                let ts =
                  Array.slice rc.(i).(j) 1 (Array.length rc.(i).(j))
                  |> Array.to_list
                in
                mk_bounds_of_coeffs norm_type ts lbrc ubrc berc) in
          Set.Poly.union_list rfun_pos_neg_maps, Formula.and_of phis) in
    Set.Poly.union_list rfun_pos_neg_maps, Formula.and_of phis
  in
  let rfun_const_bounds =
    Formula.and_of @@ List.init nl ~f:(fun i ->
        Formula.and_of @@ List.init np ~f:(fun j ->
            mk_bounds_of_const rc.(i).(j).(0) None ubrd (Set.Poly.singleton Z.zero)))
  in
  let disc_pos_neg_map, disc_coeffs_bounds =
    let disc_pos_neg_maps, phis =
      List.unzip @@ List.init nl ~f:(fun i ->
          let disc_pos_neg_maps, phis =
            List.unzip @@ List.init (if use_ifte then np - 1 else np) ~f:(fun j ->
                let disc_pos_neg_maps, phis =
                  List.unzip @@ List.init ndc ~f:(fun k ->
                      let ts =
                        Array.slice dc.(i).(j).(k) 1 (Array.length dc.(i).(j).(k))
                        |> Array.to_list
                      in
                      mk_bounds_of_coeffs norm_type ts lbdc ubdc bedc) in
                Set.Poly.union_list disc_pos_neg_maps, Formula.and_of phis) in
          Set.Poly.union_list disc_pos_neg_maps, Formula.and_of phis) in
    Set.Poly.union_list disc_pos_neg_maps, Formula.and_of phis
  in
  let disc_const_bounds =
    Formula.and_of @@ List.init nl ~f:(fun i ->
        Formula.and_of @@ List.init (if use_ifte then np - 1 else np) ~f:(fun j ->
            Formula.and_of @@ List.init ndc ~f:(fun k ->
                mk_bounds_of_const dc.(i).(j).(k).(0) None ubdd ds)))
  in
  let temp_params =
    Logic.SortMap.of_set @@ Set.Poly.map ~f:Logic.ExtTerm.of_old_sort_bind @@
    Set.Poly.union_list [rfun_pos_neg_map; disc_pos_neg_map; temp_params_fun; temp_params_quals]
  in
  temp_params, hole_quals_map, tmpl,
  rfun_coeffs_bounds, rfun_const_bounds, disc_coeffs_bounds, disc_const_bounds

let gen_simplified_wf_predicate quals _terms
    (nl, np, ubrc, ubrd, ndc, ubdc, ubdd, ds)
    (norm_type, lbrc, lbdc, berc, bedc) params =
  assert (List.length params mod 2 = 0);
  let int_params = List.filter params ~f:(function _, T_int.SInt -> true | _ -> false) in
  let size = List.length int_params / 2 in
  let txs = List.map ~f:(uncurry Term.mk_var) (List.take int_params size) in
  let tys = List.map ~f:(uncurry Term.mk_var) (List.drop int_params size) in
  let rc =
    Array.init np ~f:(fun _i ->
        Array.init nl ~f:(fun _j ->
            Array.init (size + 1) ~f:(fun _ ->
                Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt)))
  in
  let dc =
    Array.init np ~f:(fun _i ->
        Array.init ndc ~f:(fun _j ->
            Array.init (size + 1) ~f:(fun _ ->
                Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt)))
  in
  let temp_params_fun =
    Set.Poly.of_list @@ List.map ~f:(fun t -> let x, s, _ = Term.let_var t in x, s) @@
    ((List.concat_map ~f:Array.to_list @@ List.concat_map ~f:Array.to_list @@ Array.to_list rc) @
     (List.concat_map ~f:Array.to_list @@ List.concat_map ~f:Array.to_list @@ Array.to_list dc))
  in
  let r_x i j =
    T_int.mk_sum rc.(i).(j).(0)
      (List.mapi ~f:(fun k -> T_int.mk_mult rc.(i).(j).(k + 1)) txs)
  in
  let r_y i j =
    T_int.mk_sum rc.(i).(j).(0)
      (List.mapi ~f:(fun k -> T_int.mk_mult rc.(i).(j).(k + 1)) tys)
  in
  let d_x i j =
    T_int.mk_sum dc.(i).(j).(0)
      (List.mapi ~f:(fun l -> T_int.mk_mult dc.(i).(j).(l + 1)) txs)
  in
  let d_y i j =
    T_int.mk_sum dc.(i).(j).(0)
      (List.mapi ~f:(fun l -> T_int.mk_mult dc.(i).(j).(l + 1)) tys)
  in
  let temp_params_quals, hole_quals_map, holes =
    let params_x, params_y = List.split_n params (List.length params / 2) in
    let quals = List.filter quals ~f:(fun q -> Set.Poly.is_subset (Formula.fvs_of q) ~of_:(Set.Poly.of_list @@ List.map ~f:fst params_x)) in
    List.init np ~f:(fun i ->
        let temp_params_quals, quals_x, hole = gen_hole_for_qualifiers (params, quals) in
        let quals_y = List.map quals_x ~f:(fun (b, (senv, q)) -> b, (senv, Formula.rename (SortEnv.from_to (SortEnv.of_list params_x) (SortEnv.of_list params_y)) q)) in
        let hole_x_name = Ident.name_of_tvar hole ^ "_x" in
        let hole_y_name = Ident.name_of_tvar hole ^ "_y" in
        let hole_term_of name =
          Formula.mk_atom @@
          Atom.mk_pvar_app (Ident.Pvar name)
            (List.map ~f:snd params)
            (List.map ~f:(uncurry Term.mk_var) params)
        in
        temp_params_quals,
        [(Ident.Tvar hole_x_name, quals_x); (Ident.Tvar hole_y_name, quals_y)],
        (i, (hole_term_of hole_x_name, hole_term_of hole_y_name)))
    |> List.unzip3
    |> (fun (temp_params_qualss, hole_quals_maps, holes) ->
        Set.Poly.union_list temp_params_qualss,
        List.concat hole_quals_maps,
        holes)
  in
  let hole_x i = fst @@ List.Assoc.find_exn ~equal:Stdlib.(=) holes i in
  let hole_y i = snd @@ List.Assoc.find_exn ~equal:Stdlib.(=) holes i in
  let disc_x i =
    Formula.and_of @@ hole_x i :: List.init ndc ~f:(fun j ->
        Formula.geq (d_x i j) (T_int.zero ()))
  in
  let disc_y i =
    Formula.and_of @@ hole_y i :: List.init ndc ~f:(fun j ->
        Formula.geq (d_y i j) (T_int.zero ()))
  in
  let tmpl =
    let d_y_geq_zero = Formula.or_of @@ List.init np ~f:(fun j -> disc_y j) in
    let ldec i j =
      Formula.or_of @@ List.init nl ~f:(fun k ->
          Formula.and_of [
            Formula.geq (r_x i k) (T_int.zero ());
            Formula.geq (r_x i k) (T_int.mk_add (r_y j k) (T_int.one ()));
            Formula.and_of @@ List.init k ~f:(fun l ->
                Formula.or_of [
                  Formula.and_of [
                    Formula.leq (T_int.mk_add (r_x i l) (T_int.one ())) (T_int.zero ());
                    Formula.leq (T_int.mk_add (r_y j l) (T_int.one ())) (T_int.zero ())
                  ];
                  Formula.geq (r_x i l) (r_y j l)
                ])
          ])
    in
    let pdec =
      Formula.or_of @@ List.init np ~f:(fun i ->
          Formula.and_of [
            disc_x i;
            Formula.and_of @@ List.init np ~f:(fun j ->
                Formula.mk_imply (disc_y j) (ldec i j))
          ])
    in
    Formula.and_of [ d_y_geq_zero; pdec ]
  in
  let rfun_pos_neg_map, rfun_coeffs_bounds =
    let rfun_pos_neg_maps, phis =
      List.unzip @@ List.init np ~f:(fun i ->
          let rfun_pos_neg_maps, phis =
            List.unzip @@ List.init nl ~f:(fun j ->
                let ts =
                  Array.slice rc.(i).(j) 1 (Array.length rc.(i).(j))
                  |> Array.to_list
                in
                mk_bounds_of_coeffs norm_type ts lbrc ubrc berc) in
          Set.Poly.union_list rfun_pos_neg_maps, Formula.and_of phis) in
    Set.Poly.union_list rfun_pos_neg_maps, Formula.and_of phis
  in
  let rfun_const_bounds =
    Formula.and_of @@ List.init np ~f:(fun i ->
        Formula.and_of @@ List.init nl ~f:(fun j ->
            mk_bounds_of_const rc.(i).(j).(0) None ubrd (Set.Poly.singleton Z.zero)))
  in
  let disc_pos_neg_map, disc_coeffs_bounds =
    let disc_pos_neg_maps, phis =
      List.unzip @@ List.init np ~f:(fun i ->
          let disc_pos_neg_maps, phis =
            List.unzip @@ List.init ndc ~f:(fun j ->
                let ts =
                  Array.slice dc.(i).(j) 1 (Array.length dc.(i).(j))
                  |> Array.to_list
                in
                mk_bounds_of_coeffs norm_type ts lbdc ubdc bedc) in
          Set.Poly.union_list disc_pos_neg_maps, Formula.and_of phis) in
    Set.Poly.union_list disc_pos_neg_maps, Formula.and_of phis
  in
  let disc_const_bounds =
    Formula.and_of @@ List.init np ~f:(fun i ->
        Formula.and_of @@ List.init ndc ~f:(fun j ->
            mk_bounds_of_const dc.(i).(j).(0) None ubdd ds))
  in
  let temp_params =
    Logic.SortMap.of_set @@ Set.Poly.map ~f:Logic.ExtTerm.of_old_sort_bind @@
    Set.Poly.union_list [rfun_pos_neg_map; disc_pos_neg_map; temp_params_fun; temp_params_quals]
  in
  temp_params, hole_quals_map, tmpl,
  rfun_coeffs_bounds, rfun_const_bounds, disc_coeffs_bounds, disc_const_bounds

let gen_int_fun quals _terms
    (nd, nc, ubec, ubed, es, ubcc, ubcd, cs) (lbec, lbcc, beec, becc) ?(ret = None) params :
  Logic.SortMap.t *
  (Ident.tvar * (Ident.tvar * (SortEnv.t * Formula.t)) list) list *
  Term.t * Formula.t * Formula.t * Formula.t * Formula.t =
  let int_params = List.filter params ~f:(function _, T_int.SInt -> true | _ -> false) in
  let txs = List.map ~f:(uncurry Term.mk_var) int_params in
  let size = List.length int_params in
  let gen_params_1d nd =
    Array.init nd ~f:(fun _i ->
        Array.init (size + 1) ~f:(fun _ ->
            Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt))
  in
  let gen_params_2d nd nc =
    Array.init nd ~f:(fun _i ->
        Array.init nc ~f:(fun _j ->
            Array.init (size + 1) ~f:(fun _ ->
                Term.mk_var (Ident.mk_fresh_parameter ()) T_int.SInt)))
  in
  let rc, dc = (gen_params_1d nd, gen_params_2d (nd - 1) nc) in
  let temp_params_fun =
    Set.Poly.of_list @@ List.map ~f:(fun t -> let x, s, _ = Term.let_var t in x, s) @@
    ((List.concat_map ~f:Array.to_list @@ Array.to_list rc) @
     (List.concat_map ~f:Array.to_list @@ List.concat_map ~f:Array.to_list @@ Array.to_list dc))
  in
  let r_x i =
    T_int.mk_sum rc.(i).(0)
      (List.mapi ~f:(fun j -> T_int.mk_mult rc.(i).(j + 1)) txs)
  in
  let d_x i j =
    T_int.mk_sum dc.(i).(j).(0)
      (List.mapi ~f:(fun k -> T_int.mk_mult dc.(i).(j).(k + 1)) txs)
  in
  let temp_params_quals, hole_quals_map, exp_x =
    let ts = List.init nd ~f:(fun i -> (i, r_x i)) in
    List.fold_right
      (List.take ts (List.length ts - 1))
      ~init:(Set.Poly.empty, [], snd @@ List.last_exn ts)
      ~f:(fun (i, t1) (temp_params_quals', hole_quals_map, t2) ->
          let params = match ret with None -> params | Some ret -> params @ [ret] in
          let temp_params_quals, quals, hole = gen_hole_for_qualifiers (params, quals) in
          let hole_term =
            Formula.mk_atom @@
            Atom.mk_pvar_app (Ident.Pvar (Ident.name_of_tvar hole))
              (List.map ~f:snd params)
              (List.map ~f:(uncurry Term.mk_var) params)
          in
          Set.Poly.union temp_params_quals temp_params_quals',
          (hole, quals) :: hole_quals_map,
          T_bool.ifte
            ( Formula.and_of @@
              hole_term :: List.init nc ~f:(fun j -> Formula.geq (d_x i j) (T_int.zero ())) )
            t1 t2)
  in
  let expr_pos_neg_map, expr_coeffs_bounds =
    let expr_pos_neg_maps, phis =
      List.unzip @@ List.init nd ~f:(fun i ->
          let ts = Array.slice rc.(i) 1 (Array.length rc.(i)) |> Array.to_list in
          mk_bounds_of_coeffs 1 ts lbec ubec beec) in
    Set.Poly.union_list expr_pos_neg_maps, Formula.and_of phis
  in
  let expr_const_bounds =
    Formula.and_of @@ List.init nd ~f:(fun i -> mk_bounds_of_const rc.(i).(0) None ubed es)
  in
  let cond_pos_neg_map, cond_coeffs_bounds =
    let cond_pos_neg_maps, phis =
      List.unzip @@ List.init (nd - 1) ~f:(fun i ->
          let maps, phis =
            List.unzip @@ List.init nc ~f:(fun j ->
                let ts =
                  Array.slice dc.(i).(j) 1 (Array.length dc.(i).(j)) |> Array.to_list
                in
                mk_bounds_of_coeffs 1 ts lbcc ubcc becc) in
          Set.Poly.union_list maps, Formula.and_of phis) in
    Set.Poly.union_list cond_pos_neg_maps, Formula.and_of phis
  in
  let cond_const_bounds =
    Formula.and_of @@
    List.init (nd - 1) ~f:(fun i ->
        Formula.and_of @@
        List.init nc ~f:(fun j -> mk_bounds_of_const dc.(i).(j).(0) None ubcd cs))
  in
  let temp_params =
    Logic.SortMap.of_set @@ Set.Poly.map ~f:Logic.ExtTerm.of_old_sort_bind @@
    Set.Poly.union_list [expr_pos_neg_map; cond_pos_neg_map; temp_params_fun; temp_params_quals]
  in
  temp_params, hole_quals_map, exp_x,
  expr_coeffs_bounds, expr_const_bounds, cond_coeffs_bounds, cond_const_bounds
let gen_int_bool_fun ignore_bool quals terms
    (nd, nc, ubec, ubed, es, ubcc, ubcd, cs) (lbec, lbcc, beec, becc) ?(ret = None) params :
  Logic.SortMap.t *
  (Ident.tvar * (Ident.tvar * (SortEnv.t * Formula.t)) list) list *
  Term.t * Formula.t * Formula.t * Formula.t * Formula.t =
  let rec aux = function
    | [] ->
      gen_int_fun quals terms
        (nd, nc, ubec, ubed, es, ubcc, ubcd, cs)
        (lbec, lbcc, beec, becc)
        params ~ret
    | (x, sort) :: xs ->
      assert (Stdlib.(=) sort T_bool.SBool);
      let temp_params1, hole_quals_map1, exp_x1,
          expr_coeffs_bounds1,
          expr_const_bounds1,
          cond_coeffs_bounds1,
          cond_const_bounds1 = aux xs
      in
      let temp_params2, hole_quals_map2, exp_x2,
          expr_coeffs_bounds2,
          expr_const_bounds2,
          cond_coeffs_bounds2,
          cond_const_bounds2 = aux xs
      in
      Logic.SortMap.merge temp_params1 temp_params2,
      hole_quals_map1 @ hole_quals_map2,
      T_bool.ifte (Formula.of_bool_var x) exp_x1 exp_x2,
      Formula.mk_and expr_coeffs_bounds1 expr_coeffs_bounds2,
      Formula.mk_and expr_const_bounds1 expr_const_bounds2,
      Formula.mk_and cond_coeffs_bounds1 cond_coeffs_bounds2,
      Formula.mk_and cond_const_bounds1 cond_const_bounds2
  in
  aux (if ignore_bool then [] else List.filter params ~f:(function _, T_bool.SBool -> true | _ -> false))
let gen_fn_predicate ignore_bool quals terms
    (nd, nc, ubec, ubed, es, ubcc, ubcd, cs) (lbec, lbcc, beec, becc) params :
  Logic.SortMap.t *
  (Ident.tvar * (Ident.tvar * (SortEnv.t * Formula.t)) list) list *
  Formula.t * Formula.t * Formula.t * Formula.t * Formula.t =
  let params, ret = List.take params (List.length params - 1), List.last_exn params in
  assert (Stdlib.(<>) (snd ret) T_bool.SBool);
  let temp_params, hole_quals_map, exp_x,
      expr_coeffs_bounds, expr_const_bounds, cond_coeffs_bounds, cond_const_bounds =
    gen_int_bool_fun ignore_bool quals terms
      (nd, nc, ubec, ubed, es, ubcc, ubcd, cs)
      (lbec, lbcc, beec, becc) params ~ret:(Some ret)
  in
  temp_params, hole_quals_map, Formula.eq (uncurry Term.mk_var ret) exp_x,
  expr_coeffs_bounds, expr_const_bounds, cond_coeffs_bounds, cond_const_bounds


let gen_dnf eq_atom quals terms (nd, nc, _depth, ubc, ubd, s) bec params :
  Logic.SortMap.t *
  (Ident.tvar * (Ident.tvar * (SortEnv.t * Formula.t)) list) list *
  Formula.t * Formula.t * Formula.t * Formula.t =
  List.init nd ~f:(fun _ ->
      List.init nc ~f:(fun _ ->
          let _, (params, tmpl) =
            Arith.atom_of ~eq:eq_atom @@ (List.map params ~f:(fun (x, s) -> Term.mk_var x s, s) @ terms)
          in
          let (coeffs, const) = params in
          let cnstr_of_const = mk_bounds_of_const const None ubd s in
          let pos_neg_map, cnstr_of_coeffs =
            mk_bounds_of_coeffs 1 coeffs None ubc bec in
          let cnstr_of_quals = (*ToDo*)Formula.mk_true () in
          let temp_params =
            Set.Poly.union pos_neg_map @@
            Set.Poly.of_list @@ List.map ~f:(fun v -> let x, s, _ = Term.let_var v in x, s) @@
            const :: coeffs
          in
          temp_params, cnstr_of_const, cnstr_of_coeffs, cnstr_of_quals, Formula.mk_atom tmpl)
      |> List.unzip5
      |> (fun (temp_paramss, cnstr_of_consts, cnstr_of_coeffs, cnstr_of_quals, atoms) ->
          let temp_params_quals, quals, hole = gen_hole_for_qualifiers (params, quals) in
          let hole_term =
            Formula.mk_atom @@
            Atom.mk_pvar_app (Ident.Pvar (Ident.name_of_tvar hole))
              (List.map ~f:snd params)
              (List.map ~f:(uncurry Term.mk_var) params)
          in
          Set.Poly.union_list (temp_params_quals :: temp_paramss),
          (hole, quals),
          Formula.and_of cnstr_of_consts,
          Formula.and_of cnstr_of_coeffs,
          Formula.and_of cnstr_of_quals,
          Formula.and_of (hole_term :: atoms)))
  |> List.unzip6
  |> (fun (temp_paramss, hole_quals_map, cnstr_of_consts, cnstr_of_coeffs, cnstr_of_quals, disj) ->
      let temp_params =
        Logic.SortMap.of_set @@ Set.Poly.map ~f:Logic.ExtTerm.of_old_sort_bind @@
        Set.Poly.union_list temp_paramss
      in
      temp_params,
      hole_quals_map,
      Formula.or_of disj,
      Formula.and_of cnstr_of_coeffs,
      Formula.and_of cnstr_of_consts,
      Formula.and_of cnstr_of_quals)
