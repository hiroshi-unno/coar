open Core
open Typedtree
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open Ast.Ident
open Ast.LogicOld
open Preprocessing

module Make (Config : Config.ConfigType) = struct
  let config = Config.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_module_name "Cgen"

  module MBcgen = MBcgen.Make ((
    struct
      let config = MBcgen.Config.{ verbose = config.verbose }
    end :
      MBcgen.Config.ConfigType))

  module MBcsol = MBcsol.Make ((
    struct
      let config = MBcsol.Config.{ verbose = config.verbose; elim_pure = false }
    end :
      MBcsol.Config.ConfigType))

  type mode = OCaml | HFL_Expectation of bool (* whether conditional *)
  type constr = Formula.t

  type item =
    | Skip
    | Check of (tvar * Assertion.t) list
    | Infer of
        (tvar
        * (tvar * Assertion.direction) list (* priority *)
        * (tvar * SolSpace.space_flag * int) list (* solution space *))
        list

  (** Refinement Type Inference *)

  let mu_preds = ref Map.Poly.empty (*ToDo*)
  let nu_preds = ref Map.Poly.empty (*ToDo*)

  (** refinement types of constructors *)

  let inst_pvs_dtrenv = ref Set.Poly.empty
  let dtrenv = ref Map.Poly.empty

  let get_penv_dtrenv bpvs =
    Set.Poly.union_list
    @@ List.map
         ~f:
           (Rtype.pred_sort_env_of_val
              ~bpvs
                (*cannot omit since users can specify refinement types for constructors*))
    @@ Map.Poly.data !dtrenv

  let get_pvs_dtrenv bpvs = Set.Poly.map ~f:fst @@ get_penv_dtrenv bpvs

  let of_constructor ~config cons_name dt =
    let open Rtype in
    let rec inner svmap dep_args =
      let make sort =
        if config.gen_ref_type_temp_for_constructors then
          val_of_sort ~config ~refine:true ~svmap dep_args sort
        else simple_val_of_sort ~config ~svmap sort
      in
      function
      | [] ->
          let params = List.map (Datatype.params_of dt) ~f:make in
          let pred =
            let x = mk_fresh_tvar_with "x" in
            let ret = Term.mk_var x (T_dt.SDT dt) in
            ( x,
              Formula.eq ret @@ T_dt.mk_cons dt cons_name
              @@ List.map ~f:fst dep_args )
            (*Formula.and_of @@
              (Formula.mk_atom @@ T_dt.mk_is_cons dt cons_name ret) ::
              List.mapi dom ~f:(fun i (arg_i, _) ->
                Formula.eq arg_i @@
                T_dt.mk_sel dt (Datatype.mk_name_of_sel cons_name i) ret)*)
          in
          mk_rdt params dt pred
      | sort :: sorts ->
          let x = mk_fresh_tvar_with "x" in
          let c =
            pure_comp_of_val ~config
            @@ inner svmap (dep_args @ [ (Term.mk_var x sort, sort) ]) sorts
          in
          mk_rarrow x (make sort) c @@ mk_fresh_trivial_pred ()
    in
    match Map.Poly.find !dtrenv cons_name with
    | Some _ ->
        failwith
        @@ sprintf
             "the refinement type template for the constructor %s already \
              generated"
             cons_name
    | None ->
        let svs = Datatype.svs_of dt (* ToDo: does it work for GADTs? *) in
        let pvenv, svmap =
          if config.enable_pred_poly_for_constructors then
            let svpvs =
              Set.Poly.map svs ~f:(fun sv -> (sv, Ident.mk_fresh_pvar ()))
            in
            ( Map.of_set_exn
              @@ Set.Poly.map svpvs ~f:(fun (sv, pv) -> (pv, [ Sort.SVar sv ])),
              Map.of_set_exn
              @@ Set.Poly.map svpvs ~f:(fun (sv, pv) ->
                     ( sv,
                       let sort = Sort.SVar sv in
                       Rtype.mk_rbase sort
                       @@
                       let tv = Ident.mk_fresh_tvar () in
                       ( tv,
                         Formula.mk_atom
                         @@ Atom.mk_pvar_app pv [ sort ] [ Term.mk_var tv sort ]
                       ) )) )
          else (Map.Poly.empty, Map.Poly.empty)
        in
        let t =
          mk_type_poly ~config svs @@ pure_comp_of_val ~config
          @@ (if config.enable_pred_poly_for_constructors then
                pure_comp_of_val ~config
                >> mk_pred_poly ~config pvenv Set.Poly.empty
              else Fn.id)
          @@ inner svmap []
          @@ Datatype.sorts_of_cons_name dt cons_name
        in
        Debug.print
        @@ lazy (sprintf "assigning %s : %s" cons_name @@ str_of_val ~config t);
        dtrenv := Map.Poly.add_exn !dtrenv ~key:cons_name ~data:t;
        t

  let update_dtrenv_with_renv renv = dtrenv := Map.update_with !dtrenv renv

  let update_dtrenv_with_dts ~config dts =
    let open Datatype in
    update_dtrenv_with_renv @@ Map.Poly.of_alist_exn
    @@ List.concat_map dts ~f:(fun datatype ->
           List.concat_map datatype.dts ~f:(fun dt ->
               List.map dt.conses ~f:(fun cons ->
                   (cons.name, of_constructor ~config cons.name datatype))))

  (** auxiliary functions for constraint generation *)

  let instantiate_val_con positive ~config dom kind_map
      (cty, args_sorts_opt, ret_ty) =
    let open Rtype in
    let svs, ty0 = let_type_poly cty in
    let params, ret_sort, _pred = let_rgeneral ret_ty in
    let penv, constrs, ty = let_pred_poly ty0 in
    let args, ret = args_ret_of_val ty in
    let svmap =
      match (sort_of_val ret, ret_sort) with
      | T_dt.SDT dt1, T_dt.SDT dt2
        when String.(Datatype.name_of dt1 = Datatype.name_of dt2) ->
          Map.Poly.of_alist_exn
          @@ List.filter_map ~f:(function
               | Sort.SVar svar, t -> Some (svar, t)
               | sort, t ->
                   (* ToDo: check that t is without refinement *)
                   assert (Stdlib.(sort = sort_of_val t));
                   None)
          @@ List.zip_exn (Datatype.params_of dt1) params
      | _ -> failwith "instantiate_val_con"
    in
    let sort, sub =
      match args_sorts_opt with
      | Some args_sorts ->
          let sort = Sort.mk_fun @@ args_sorts @ [ sort_of_val ret_ty ] in
          ( sort,
            Map.Poly.filter_keys ~f:(Set.mem svs)
            @@ tsub_of_val ~config Map.Poly.empty (ty, sort) )
      | None ->
          let sub =
            Map.Poly.filter_keys ~f:(Set.mem svs)
            @@ tsub_of_val ~config Map.Poly.empty (ret, sort_of_val ret_ty)
          in
          let args_sorts =
            List.map ~f:(snd >> sort_of_val >> Term.subst_sorts_sort sub) args
          in
          (Sort.mk_fun @@ args_sorts @ [ sort_of_val ret_ty ], sub)
    in
    let svmap = update_svmap_with_sub ~config dom svmap sub in
    let constrs0, ty =
      if positive then
        ( Set.Poly.empty,
          Rtype.mk_pred_poly ~config penv constrs
          @@ Rtype.pure_comp_of_val ~config ty )
      else
        (* ToDo: use existential quantification of pred. vars. instead*)
        let psub =
          Map.Poly.map penv ~f:(fun sorts ->
              (sort_env_list_of_sorts sorts, Formula.mk_true ()))
        in
        ( Set.Poly.map ~f:(Formula.subst_preds psub) constrs,
          subst_preds_val psub ty )
    in
    let ty, constrs, kind_map =
      instantiate_val ~print:Debug.print ~config dom kind_map (sub, svmap)
        (ty, sort)
    in
    let constrs = Set.union constrs constrs0 in
    Debug.print
    @@ lazy
         (sprintf "instantiated constructor type: %s\nconstraints: %s"
            (str_of_val ~config ty)
            (Formula.str_of @@ Formula.and_of @@ Set.to_list constrs));
    (ty, constrs, kind_map)

  let rec constr_of ~config ?(depth = 0 (*ToDo*)) (renv, phis) =
    let open Rtype in
    let css, phis' =
      Set.unzip
      @@ Set.Poly.filter_map (Map.to_set renv) ~f:(fun (x, ty) ->
             let x_term = Term.mk_var x @@ sort_of_val ty in
             match ty with
             | RGeneral (_, T_dt.SDT dt, pred) ->
                 let css, phis =
                   if depth <= 0 then ([], [])
                   else
                     let renv_wo_x = (Map.Poly.remove renv x, phis) in
                     let dom = Env.dep_args_of renv_wo_x in
                     (*let dt = Datatype.update_params dt @@ List.map params ~f:sort_of_val in*)
                     List.unzip
                     @@ List.map (Datatype.conses_of dt) ~f:(fun cons ->
                            (*print @@ lazy cons.name;*)
                            let cty, constrs, _kind_map (*ToDo*) =
                              let cty = Map.Poly.find_exn !dtrenv cons.name in
                              instantiate_val_con false ~config dom
                                Map.Poly.empty (*ToDo*) (cty, None, ty)
                            in
                            let args, _ret =
                              args_ret_of_val @@ aconv_val Map.Poly.empty cty
                            in
                            let t_cons =
                              T_dt.mk_cons dt cons.name
                              @@ List.map args ~f:(fun (x, t) ->
                                     Term.mk_var x @@ Rtype.sort_of_val t)
                            in
                            let renv_args =
                              ( Map.Poly.of_alist_exn args,
                                Set.Poly.singleton @@ Formula.eq x_term t_cons
                              )
                            in
                            let constrs_args, phi_args =
                              constr_of ~config ~depth:(depth - 1) renv_args
                            in
                            ( Set.Poly.union_list [ constrs; constrs_args ],
                              Formula.mk_imply (Formula.eq x_term t_cons)
                                phi_args ))
                 in
                 Option.return
                 @@ ( Set.Poly.union_list css,
                      Formula.and_of @@ (Formula.apply_pred pred x_term :: phis)
                    )
             | RTuple (elems, pred) ->
                 let args =
                   List.map elems ~f:(fun t -> (mk_fresh_tvar_with "v", t))
                 in
                 let constrs_elems, phi_elems =
                   constr_of ~config ~depth
                   @@ ( Map.Poly.of_alist_exn args,
                        Set.Poly.singleton @@ Formula.eq x_term
                        @@ T_tuple.mk_tuple_cons (List.map elems ~f:sort_of_val)
                        @@ List.map args ~f:(fun (x, t) ->
                               Term.mk_var x @@ sort_of_val t) )
                 in
                 Option.return
                 @@ ( constrs_elems,
                      Formula.and_of
                        [ Formula.apply_pred pred x_term; phi_elems ] )
             | RGeneral (_params, T_dt.SUS (_name, _), pred) ->
                 (* ToDo: SUS can be promoted to SDT? *)
                 Some (Set.Poly.empty, Formula.apply_pred pred x_term)
             | RGeneral (_params, _sort, pred) ->
                 Some (Set.Poly.empty, Formula.apply_pred pred x_term)
             | RRef (_, pred) ->
                 Some (Set.Poly.empty, Formula.apply_pred pred x_term)
             | RArrow (_y, _t, _c, pred) ->
                 Some (Set.Poly.empty, Formula.apply_pred pred x_term)
             | _ -> None)
    in
    (Set.concat css, Formula.and_of @@ Set.to_list @@ Set.union phis phis')

  let rec cgen_subeff_temp ?(first = true) ~config ?(depth = 0) renv
      ((x1, phi1), (y1, psi1)) ((x2, phi2), (y2, psi2)) =
    let open Rtype in
    if config.enable_temp_eff then (
      if first then
        Debug.print
        @@ lazy
             (sprintf "[cgen_subeff_temp]\n%s\n  |- (%s)  <:  (%s)"
                (Env.str_of ~config renv)
                (str_of_temp ((x1, phi1), (y1, psi1)))
                (str_of_temp ((x2, phi2), (y2, psi2))));
      let constrs =
        let constrs1, phi1_pre =
          constr_of ~config ~depth @@ Env.add_phi renv @@ snd
          @@ Formula.split_exists
          @@ Formula.rename (Map.Poly.singleton x1 x2) phi1
        in
        let constrs2, psi1_pre =
          constr_of ~config ~depth @@ Env.add_phi renv @@ snd
          @@ Formula.split_exists
          @@ Formula.rename (Map.Poly.singleton y1 y2) psi1
        in
        Set.union
          (Set.add constrs1
          @@ Formula.mk_imply
               (Evaluator.simplify phi1_pre)
               (Evaluator.simplify phi2))
          (Set.add constrs2
          @@ Formula.mk_imply
               (Evaluator.simplify psi1_pre)
               (Evaluator.simplify psi2))
      in
      if first then
        Debug.print
        @@ lazy
             (sprintf "[cgen_subeff_temp] constraints:\n  %s\n"
             @@ String.concat_set ~sep:"\n  "
             @@ Set.Poly.map constrs ~f:Formula.str_of);
      constrs)
    else Set.Poly.empty

  and cgen_subeff_cont ?(first = true) ~config ?(depth = 0) renv t es s1 s2 =
    let open Rtype in
    if first then
      if config.enable_temp_eff then
        Debug.print
        @@ lazy
             (sprintf "[cgen_subeff_cont]\n%s\n| %s & %s\n  |- %s  <:  %s"
                (Env.str_of ~config renv) (str_of_val ~config t)
                (str_of_temp @@ compose_temp_eff es)
                (str_of_cont ~config s1) (str_of_cont ~config s2))
      else
        Debug.print
        @@ lazy
             (sprintf "[cgen_subeff_cont]\n%s\n| %s \n  |- %s  <:  %s"
                (Env.str_of ~config renv) (str_of_val ~config t)
                (str_of_cont ~config s1) (str_of_cont ~config s2));
    let constrs =
      match (s1, s2) with
      | Pure, Pure -> Set.Poly.empty
      | Eff (x1, c11, c12), Eff (x2, c21, c22) ->
          let c11 = rename_comp ~config (Map.Poly.singleton x1 x2) c11 in
          let renv' = Env.disj_union renv @@ Env.singleton_ty x2 t in
          Set.union
            (cgen_subtype_comp ~first:false ~config ~depth renv' c21 c11)
          @@ cgen_subtype_comp ~first:false ~config ~depth renv c12 c22
      | Pure, Eff (x, c1, c2) ->
          let renv' = Env.disj_union renv @@ Env.singleton_ty x t in
          Set.union
            (cgen_subtype_comp ~first:false ~config ~depth renv'
               (compose_temp_comp es c1) c2)
          @@
          if config.Rtype.enable_temp_eff then
            let _, (y, phi) = compose_temp_eff es in
            let constrs, phi_pre =
              constr_of ~config ~depth @@ Env.add_phi renv @@ snd
              @@ Formula.split_exists (*ToDo*) phi
            in
            Set.add constrs
            @@ Formula.mk_imply
                 (Evaluator.simplify phi_pre)
                 (Evaluator.simplify @@ nu_of_comp y c2)
          else Set.Poly.empty
      | _ ->
          failwith
          @@ sprintf "[cgen_subeff_cont] %s and %s " (str_of_cont ~config s1)
               (str_of_cont ~config s2)
    in
    if first then
      Debug.print
      @@ lazy
           (sprintf "[cgen_subeff_cont] constraints:\n  %s\n"
              (String.concat_set ~sep:"\n  "
              @@ Set.Poly.map constrs ~f:Formula.str_of));
    constrs

  and cgen_subtype_opsig ?(first = true) ~config ?(depth = 0) renv
      (o1 : Rtype.o) (o2 : Rtype.o) =
    let open Rtype in
    if first then
      Debug.print
      @@ lazy
           (sprintf "[cgen_subtype_opsig]\n%s\n  |- %s  <:  %s"
              (Env.str_of ~config renv) (str_of_opsig ~config o1)
              (str_of_opsig ~config o2));
    let constrs =
      let _lefts, boths, rights =
        ALMap.split_lbr (fst (*ToDo*) o1) (fst (*ToDo*) o2)
      in
      if (* List.is_empty lefts && *) List.is_empty rights then
        Set.Poly.union_list
        @@ List.map boths
             ~f:
               (snd
               >> uncurry @@ cgen_subtype_val ~first:false ~config ~depth renv)
      else
        failwith
        @@ sprintf "[cgen_subtype_opsig] %s and %s" (str_of_opsig ~config o1)
             (str_of_opsig ~config o2)
    in
    if first then
      Debug.print
      @@ lazy
           (sprintf "[cgen_subtype_opsig] constraints:\n  %s\n"
              (String.concat_set ~sep:"\n  "
              @@ Set.Poly.map constrs ~f:Formula.str_of));
    constrs

  and cgen_subtype_comp ?(first = true) ~config ?(depth = 0) renv (c1 : Rtype.c)
      (c2 : Rtype.c) =
    let open Rtype in
    if first then
      Debug.print
      @@ lazy
           (sprintf "[cgen_subtype_comp]\n%s\n  |- %s  <:  %s"
              (Env.str_of ~config renv) (str_of_comp ~config c1)
              (str_of_comp ~config c2));
    let constrs =
      Set.Poly.union_list
        [
          cgen_subtype_val ~first:false ~config ~depth renv c1.val_type
            c2.val_type;
          cgen_subtype_opsig ~first:false ~config ~depth renv c2.op_sig
            c1.op_sig;
          cgen_subeff_temp ~first:false ~config ~depth renv c1.temp_eff
            c2.temp_eff;
          cgen_subeff_cont ~first:false ~config ~depth renv c1.val_type
            [ c1.temp_eff ] c1.cont_eff c2.cont_eff;
        ]
    in
    if first then
      Debug.print
      @@ lazy
           (sprintf "[cgen_subtype_comp] constraints:\n  %s\n"
              (String.concat_set ~sep:"\n  "
              @@ Set.Poly.map constrs ~f:Formula.str_of));
    constrs

  and cgen_subtype_val ?(first = true) ~config ?(depth = 0) renv (t1 : Rtype.t)
      (t2 : Rtype.t) =
    let open Rtype in
    if first then
      Debug.print
      @@ lazy
           (sprintf "[cgen_subtype_val]\n%s\n  |- %s  <:  %s"
              (Env.str_of ~config renv) (str_of_val ~config t1)
              (str_of_val ~config t2));
    let imply (v1, phi1) (v2, phi2) =
      let phi1 = Formula.rename (Map.Poly.singleton v1 v2) phi1 in
      let constrs, phi1_pre =
        constr_of ~config ~depth @@ Env.add_phi renv @@ snd
        @@ Formula.split_exists (*ToDo*) phi1
      in
      Set.add constrs
      @@ Formula.mk_imply
           (Evaluator.simplify phi1_pre)
           (Evaluator.simplify phi2)
    in
    let constrs =
      match (t1, t2) with
      | RGeneral (params1, _sort1, pred1), RGeneral (params2, _sort2, pred2)
        when List.length params1 = List.length params2 ->
          Set.Poly.union_list
          @@ imply pred1 pred2
             :: (* assume that all type parameters are covariant *)
                List.map2_exn params1 params2
                  ~f:(cgen_subtype_val ~first:false ~config ~depth renv)
      (*@ List.map2_exn params2 params1 ~f:(cgen_subtype_val ~config ~depth renv)*)
      | RTuple (elems1, pred1), RTuple (elems2, pred2) ->
          Set.Poly.union_list
          @@ imply pred1 pred2
             :: List.map2_exn elems1 elems2
                  ~f:(cgen_subtype_val ~first:false ~config ~depth renv)
      | RRef (t1, pred1), RRef (t2, pred2) ->
          Set.Poly.union_list
          @@ [
               imply pred1 pred2;
               cgen_subtype_val ~first:false ~config ~depth renv t1 t2;
               cgen_subtype_val ~first:false ~config ~depth renv t2 t1;
             ]
      | RArrow (v1, t1, c1, pred1), RArrow (v2, t2, c2, pred2) ->
          let renv' = Env.disj_union renv @@ Env.singleton_ty v2 t2 in
          let c1' =
            subst_comp
              (Map.Poly.singleton v1 (Term.mk_var v2 @@ sort_of_val t2))
              c1
          in
          Set.Poly.union_list
          @@ [
               imply pred1 pred2;
               cgen_subtype_val ~first:false ~config ~depth renv t2 t1;
               cgen_subtype_comp ~first:false ~config ~depth renv' c1' c2;
             ]
      (*| RForall (_penv1, _phis1, _c1), RForall (_penv2, _phis2, _c2) -> failwith "not supported"
        (* ToDo: forall penv2 exists penv1. phis2 => phis1 /\ cgen_subtype_comp renv c1 c2 *)*)
      | _ ->
          Debug.print
          @@ lazy ("[cgen_subtype_val] env:\n" ^ Env.str_of ~config renv);
          failwith
          @@ sprintf "[cgen_subtype_val] %s <: %s" (str_of_val ~config t1)
               (str_of_val ~config t2)
    in
    if first then
      Debug.print
      @@ lazy
           (sprintf "[cgen_subtype_val] constraints:\n  %s\n"
              (String.concat_set ~sep:"\n  "
              @@ Set.Poly.map constrs ~f:Formula.str_of));
    constrs

  let compose_temp_eff_inv ~config renv ((x1, phi1), (y1, psi1))
      ((x2, phi2), (y2, psi2)) =
    let open Rtype in
    let sub1 =
      Map.Poly.singleton x2
      @@ T_sequence.mk_concat ~fin:true
           (Term.mk_var x1 @@ T_sequence.SSequence true)
           (Term.mk_var x2 @@ T_sequence.SSequence true)
    in
    let sub2 =
      Map.Poly.singleton y2
      @@ T_sequence.mk_concat ~fin:false
           (Term.mk_var x1 @@ T_sequence.SSequence true)
           (Term.mk_var y2 @@ T_sequence.SSequence false)
    in
    let _, psi1 = Formula.split_exists (*ToDo*) psi1 in
    let _, phi1 = Formula.split_exists (*ToDo*) phi1 in
    ( (if config.enable_temp_eff then
         let constrs, psi1_pre = constr_of ~config @@ Env.add_phi renv psi1 in
         Set.add constrs
         @@ Formula.mk_imply
              (Evaluator.simplify psi1_pre)
              (Evaluator.simplify
              @@ Formula.rename (Map.Poly.singleton y2 y1) psi2)
       else Set.Poly.empty),
      ( ( x2,
          Formula.forall [ (x1, T_sequence.SSequence true) ]
          @@ Evaluator.simplify @@ Formula.mk_imply phi1
          @@ Formula.subst sub1 phi2 ),
        ( y2,
          Formula.forall [ (x1, T_sequence.SSequence true) ]
          @@ Evaluator.simplify @@ Formula.mk_imply phi1
          @@ Formula.subst sub2 psi2 ) ) )

  let rec compose_temp_cont_inv ~config renv e =
    let open Rtype in
    function
    | Pure -> (Set.Poly.empty, Pure)
    | Eff (x, c1, c2) ->
        let constrs, c2' = compose_temp_comp_inv ~config renv e c2 in
        (constrs, Eff (x, c1, c2'))
    | EVar _ -> assert false

  and compose_temp_comp_inv ~config renv e c =
    let constrs1, temp_eff = compose_temp_eff_inv ~config renv e c.temp_eff in
    let constrs2, cont_eff = compose_temp_cont_inv ~config renv e c.cont_eff in
    (Set.union constrs1 constrs2, { c with temp_eff; cont_eff })

  let rec compose_cont_eff ~config =
    let open Rtype in
    function
    | [] -> (*ToDo:reachable here?*) (Set.Poly.empty, Pure)
    | [ (_, _, _, First _) ] -> (Set.Poly.empty, Pure)
    | [ (_, _, _, Second s) ] -> (Set.Poly.empty, s)
    | [
        (pat1, _renv1, _t1, Second (Eff (x1, c1, c2)));
        (_pat2, renv2, t2, First es);
      ] ->
        (* renv2, x2 : t2 |- es c3 <: [pat1/x1]c1
           renv2 |- es^nu => [pat1/x1]c1^nu
           --------------------------------------------------
           renv2 | t2 & es |- Pure <: (x2. c3) => [pat1/x1]c1 *)
        let c1 =
          subst_comp (Map.Poly.singleton x1 @@ Pattern.term_of pat1) c1
        in
        let x2 = mk_fresh_tvar_with "x2_" in
        let renv2' = Env.set_ty renv2 x2 t2 (* [t2] can depend on x2 *) in
        let constrs, c3 =
          if true then
            let c3 =
              (*Debug.print @@ lazy ("renv: " ^ Env.str_of ~config renv');*)
              let refine, dom = (true, Env.dep_args_of renv2') in
              let c = triple_of_comp c1 in
              comp_of_sort ~config ~refine ~temp:true ~opsig:(`Sort c.op_sig)
                ~cont:c.cont_eff dom c.val_type
            in
            (cgen_subtype_comp ~config renv2' (compose_temp_comp es c3) c1, c3)
          else
            (* the following avoids introducing a fresh predicate variable but imcomplete *)
            compose_temp_comp_inv ~config renv2' (compose_temp_eff es) c1
        in
        Debug.print
        @@ lazy
             (sprintf "composed cont eff: %s\n"
             @@ str_of_cont ~config
             @@ Eff (x2, c3, c2));
        ( (Set.union constrs
          @@
          if config.enable_temp_eff then
            let _, (y, phi) = compose_temp_eff es in
            let constrs, phi_pre =
              constr_of ~config @@ Env.add_phi renv2 @@ snd
              @@ Formula.split_exists (*ToDo*) phi
            in
            Set.add constrs
            @@ Formula.mk_imply
                 (Evaluator.simplify phi_pre)
                 (Evaluator.simplify @@ nu_of_comp y c1)
          else Set.Poly.empty),
          (* we can omit existential quantification over x2 in c1
             because the type is only used by cgen_subeff negatively *)
          Eff (x2, c3, c2) )
    | (_, _, _, First es1) :: (pat2, renv2, t2, First es2) :: ss ->
        (*ToDo*)
        compose_cont_eff ~config @@ ((pat2, renv2, t2, First (es1 @ es2)) :: ss)
    | ((_, _, _, Second _) as s1)
      :: (_, _, _, First es1)
      :: (pat2, renv2, t2, First es2)
      :: ss ->
        (*ToDo*)
        compose_cont_eff ~config
        @@ (s1 :: (pat2, renv2, t2, First (es1 @ es2)) :: ss)
    | (_pat1, renv1, _t1, First es)
      :: (pat2, renv2, t2, Second (Eff (x, c1, c2)))
      :: ss ->
        (* renv1, pat1 : t1 |- es c2 <: c3    renv1 |- es^nu => c3^nu
           -------------------------------------------------------
                 renv1 | t1 & es |- Pure <: (pat1. c2) => c3 *)
        let c3 = compose_temp_comp es c2 in
        (* we can omit existential quantification over pat1 in c3
           because the type is only used by cgen_subeff negatively *)
        let s = Eff (x, c1, c3) in
        let constrs, s =
          compose_cont_eff ~config @@ ((pat2, renv2, t2, Second s) :: ss)
        in
        ( (Set.union constrs
          @@
          if config.enable_temp_eff then
            let _, (y, phi) = compose_temp_eff es in
            let constrs, phi_pre =
              constr_of ~config @@ Env.add_phi renv1 @@ snd
              @@ Formula.split_exists (*ToDo*) phi
            in
            Set.add constrs
            @@ Formula.mk_imply
                 (Evaluator.simplify phi_pre)
                 (Evaluator.simplify @@ nu_of_comp y c3)
          else Set.Poly.empty),
          s )
    | ((_, _, _, Second _) as s1)
      :: (_pat1, renv1, _t1, First es)
      :: (pat2, renv2, t2, Second (Eff (x, c1, c2)))
      :: ss ->
        let c3 = compose_temp_comp es c2 in
        (* we can omit existential quantification over pat1 in c3
           because the type is only used by cgen_subeff negatively *)
        let s = Eff (x, c1, c3) in
        let constrs, s =
          compose_cont_eff ~config @@ (s1 :: (pat2, renv2, t2, Second s) :: ss)
        in
        ( (Set.union constrs
          @@
          if config.enable_temp_eff then
            let _, (y, phi) = compose_temp_eff es in
            let constrs, phi_pre =
              constr_of ~config @@ Env.add_phi renv1 @@ snd
              @@ Formula.split_exists (*ToDo*) phi
            in
            Set.add constrs
            @@ Formula.mk_imply
                 (Evaluator.simplify phi_pre)
                 (Evaluator.simplify @@ nu_of_comp y c3)
          else Set.Poly.empty),
          s )
    | (pat1, _renv1, _t1, Second (Eff (x1, c11, c12)))
      :: (pat2, renv2, t2, Second (Eff (x2, c21, c22)))
      :: ss ->
        let c11 =
          subst_comp (Map.Poly.singleton x1 @@ Pattern.term_of pat1) c11
        in
        let constrs, s =
          compose_cont_eff ~config
            ((pat2, renv2, t2, Second (Eff (x2, c21, c12))) :: ss)
        in
        (Set.union constrs @@ cgen_subtype_comp ~config renv2 c22 c11, s)
    | _ -> failwith "compose_cont_eff"

  let cgen_compose_temp_eff ~config renv es e =
    let open Rtype in
    if config.enable_temp_eff then
      [ cgen_subeff_temp ~config renv (compose_temp_eff es) e ]
    else []

  let cgen_compose_cont_eff ~config renv ss (t, es) s =
    let constrs, s' = compose_cont_eff ~config ss in
    constrs :: [ cgen_subeff_cont ~config renv t es s' s ]

  let cgen_subeff ~config renv rev_tys t' c =
    let open Rtype in
    let tys = List.rev rev_tys in
    let init = str_of_comp ~config c in
    Debug.print
    @@ lazy
         (sprintf "[cgen_subeff]\n%s"
         @@ List.fold_right tys ~init ~f:(fun (pat, _renv, c) ->
                sprintf "let %s : %s in\n%s" (Pattern.str_of pat)
                  (str_of_comp ~config c)));
    let constrs =
      (* assume that all opsigs in [tys] are empty or the same as [o]
         (i.e. they are supertypes of [o]) *)
      let es = List.map tys ~f:(fun (_, _, c) -> c.temp_eff) in
      let ss =
        List.map tys ~f:(fun (pat, renv, c) ->
            ( pat,
              renv,
              c.val_type,
              match c.cont_eff with
              | Pure -> First [ c.temp_eff ]
              | Eff _ -> Second c.cont_eff
              | EVar _ -> assert false ))
      in
      Set.Poly.union_list
      @@ cgen_compose_temp_eff ~config renv es c.temp_eff
      @ cgen_compose_cont_eff ~config renv ss (t', es) c.cont_eff
    in
    Debug.print
    @@ lazy
         (sprintf "[cgen_subeff] constraints:\n  %s\n"
            (String.concat_set ~sep:"\n  "
            @@ Set.Poly.map constrs ~f:Formula.str_of));
    constrs

  let cgen_check_pure ~config renv c =
    Debug.print
    @@ lazy (sprintf "[cgen_check_pure] %s" @@ Rtype.str_of_comp ~config c);
    let e_val = Rtype.mk_temp_val () in
    (* o can be any opsig because empty opsig is a supertype of any opsig *)
    let constrs =
      Set.Poly.union_list
        [
          cgen_subeff_temp ~config renv e_val c.temp_eff;
          cgen_subeff_cont renv ~config c.val_type [ e_val ] Pure c.cont_eff;
        ]
    in
    Debug.print
    @@ lazy
         (sprintf "[cgen_check_pure] constraints:\n  %s\n"
            (String.concat_set ~sep:"\n  "
            @@ Set.Poly.map constrs ~f:Formula.str_of));
    constrs

  (** assume [pat] is instantiated to [sort_of_val rty] *)
  let rec pattern_match_with ~config renv (pat : Pattern.t)
      (term, (rty : Rtype.t)) =
    match (pat, rty) with
    | PAny _, _ ->
        ( Rtype.Env.mk_empty (),
          Set.Poly.empty,
          (* always match *) Formula.mk_false () )
    | PVar (x, _), _ ->
        (*assert Stdlib.(sort = Rtype.sort_of_val rty);*)
        ( Rtype.Env.add_phi (Rtype.Env.singleton_ty x rty)
          @@ Formula.eq term @@ Term.mk_var x @@ Rtype.sort_of_val rty,
          Set.Poly.empty,
          (* always match *) Formula.mk_false () )
    | PTuple pats, RTuple (elems, pred) ->
        let renvs, constrss, not_matched, args, sorts, targs =
          List.unzip6
          @@ List.map2_exn pats elems ~f:(fun pi ti ->
                 let arg = Ident.mk_fresh_tvar () in
                 let sort = Rtype.sort_of_val ti in
                 let targ = Term.mk_var arg sort in
                 let renv, constrs, not_matched =
                   pattern_match_with ~config renv pi (targ, ti)
                 in
                 (renv, constrs, not_matched, (arg, ti), sort, targ))
        in
        let renv_args =
          ( Map.Poly.of_alist_exn args,
            Set.Poly.singleton @@ Formula.eq term
            @@ T_tuple.mk_tuple_cons sorts targs )
        in
        ( Rtype.Env.add_phi
            (Rtype.Env.disj_union_list
           @@ (* assume distinct *)
           (renv_args :: renvs))
            (Formula.apply_pred pred term (*ToDo: redundant?*)),
          Set.Poly.union_list constrss,
          Formula.or_of
          @@ (Formula.mk_atom @@ T_tuple.mk_is_not_tuple sorts term)
             :: not_matched )
    | PCons (dt, cons_name, pats), RGeneral (_, T_dt.SDT dt', pred)
      when String.(Datatype.name_of dt = Datatype.name_of dt') ->
        (*Debug.print @@ lazy cons_name;*)
        let ( cty (* may contain a predicate variable *),
              constrs,
              _kind_map (*ToDo*) ) =
          let cty = Map.Poly.find_exn !dtrenv cons_name in
          instantiate_val_con false ~config
            (Rtype.Env.dep_args_of renv)
            Map.Poly.empty (*ToDo*)
            (cty, Some (List.map pats ~f:Pattern.sort_of), rty)
        in
        let args, _ret =
          Rtype.args_ret_of_val @@ Rtype.aconv_val Map.Poly.empty cty
        in
        let ts =
          List.map args ~f:(fun (x, t) -> Term.mk_var x @@ Rtype.sort_of_val t)
        in
        let renv_args =
          ( Map.Poly.of_alist_exn args,
            Set.Poly.singleton @@ Formula.eq term
            @@ T_dt.mk_cons dt cons_name ts )
        in
        let renvs, constrss_args, not_matched =
          List.unzip3
          @@ List.map3_exn pats ts args ~f:(fun pi ti argi ->
                 pattern_match_with renv ~config pi (ti, snd argi))
        in
        ( Rtype.Env.add_phi
            (Rtype.Env.disj_union_list
           @@ (* assume distinct *)
           (renv_args :: renvs))
            (Formula.apply_pred pred term (*ToDo: redundant?*)),
          Set.Poly.union_list @@ (constrs :: constrss_args),
          Formula.or_of
          @@ (Formula.mk_atom @@ T_dt.mk_is_not_cons dt cons_name term)
             :: not_matched )
    | _ -> failwith "[pattern_match_with] unsupported pattern"

  let cgen_pattern_match ~config (x, c_matched, is_bound) pats (nexts, conts) =
    let open Rtype in
    fun kind_map maps renv_matched c ->
      let opsig = `Refined c.op_sig in
      match (pats, nexts, conts) with
      | [ Pattern.PVar (x', sort) ], [ next ], [ cont ] ->
          let renv_branch, c_matched, sort_matched, c =
            let sort_matched = sort_of_comp c_matched in
            if true (*ToDo*) || Stdlib.(sort = sort_matched) then
              let renv_branch, map =
                Env.update_with ~config renv_matched
                  (Env.singleton_ty x' c_matched.val_type)
              in
              ( renv_branch,
                rename_comp ~config map c_matched,
                sort_matched,
                rename_comp ~config (Map.Poly.singleton x x')
                @@ rename_comp ~config map c )
            else
              failwith
              @@ sprintf "[cgen_pattern_match] %s and %s"
                   (Term.str_of_sort sort)
                   (Term.str_of_sort sort_matched)
          in
          let is_impure_pure =
            (Fn.non Sort.is_pure @@ cont_of c_matched.cont_eff)
            && Sort.is_pure cont
          in
          let c_branch =
            let dom = Env.dep_args_of renv_branch in
            comp_of_val ~config ~temp:true ~opsig ~cont dom
            @@
            if is_impure_pure then
              val_of_sort ~config ~refine:true dom @@ sort_of_comp c
            else c.val_type
          in
          let rev_comp_effs =
            [
              (Pattern.PAny (sort_of_comp c_branch), renv_branch, c_branch);
              (Pattern.PVar (x', sort_matched), renv_matched, c_matched);
            ]
          in
          let constrs, kind_map = next kind_map maps renv_branch c_branch in
          ( Set.Poly.union_list
            @@ [
                 (if is_impure_pure then
                    cgen_subtype_val ~config renv_branch c_branch.val_type
                      c.val_type
                  else Set.Poly.empty);
                 cgen_subeff ~config renv_matched rev_comp_effs
                   c_branch.val_type c;
                 constrs;
               ],
            kind_map )
      | _ ->
          let renv =
            if is_bound then (*x is bound in renv_matched*) renv_matched
            else
              (*x is not bound in renv_matched*)
              Env.disj_union renv_matched
              @@ Env.singleton_ty x c_matched.val_type
          in
          let sort_matched = sort_of_comp c_matched in
          let has_impure_branch = List.exists ~f:(Fn.non Sort.is_pure) conts in
          let renv_not_matched, (constrs, kind_map) =
            List.fold
              ~init:(renv, (Set.Poly.empty, kind_map))
              (List.zip3_exn pats nexts conts)
              ~f:(fun (renv, (constrs, kind_map)) (pat, next, cont) ->
                let is_impure_pure =
                  (Fn.non Sort.is_pure @@ cont_of c_matched.cont_eff)
                  && Sort.is_pure cont
                in
                let is_pure_in_impures =
                  Sort.is_pure cont && has_impure_branch
                in
                let shadow = Set.mem (Pattern.tvars_of pat) x in
                let x_tentative =
                  if shadow then Ident.mk_fresh_tvar () else x
                in
                let pat_renv, constrs_params, not_matched =
                  let sub = Map.Poly.singleton x x_tentative in
                  pattern_match_with ~config
                    (Env.rename_bound_vars ~config sub renv)
                    pat
                    ( Term.mk_var x_tentative sort_matched,
                      rename_val ~config sub c_matched.val_type )
                in
                Debug.print
                @@ lazy
                     (sprintf
                        "[cgen_pattern_match] pattern: %s\n\
                         renv:\n\
                         %s\n\
                         constraints: %s" (Pattern.str_of pat)
                        (Env.str_of ~config pat_renv)
                        (String.concat_set ~sep:"\n"
                        @@ Set.Poly.map ~f:Formula.str_of constrs_params));

                ( Env.add_phi renv
                  @@ Formula.rename
                       (Map.Poly.singleton x_tentative x)
                       not_matched,
                  let renv_branch, c_matched, c =
                    let renv_branch, map =
                      Env.update_with ~config renv
                        (*ToDo*) (fst pat_renv, Set.Poly.empty)
                    in
                    let renv_branch =
                      (*ToDo*) Env.add_phis renv_branch (snd pat_renv)
                    in
                    let x_final =
                      match Map.Poly.find map x with
                      | None ->
                          assert (not shadow);
                          x
                      | Some x_final ->
                          assert shadow;
                          x_final
                    in
                    let map_x = Map.Poly.singleton x_tentative x_final in
                    ( Env.rename ~config map_x renv_branch,
                      rename_comp ~config map c_matched,
                      rename_comp ~config map c )
                  in
                  let c_branch =
                    let dom = Env.dep_args_of renv_branch in
                    comp_of_val ~config ~temp:true ~opsig ~cont dom
                    @@
                    if is_impure_pure || is_pure_in_impures then
                      val_of_sort ~config ~refine:true dom @@ sort_of_comp c
                    else c.val_type
                  in
                  let rev_comp_effs =
                    [
                      ( Pattern.PAny (sort_of_comp c_branch),
                        renv_branch,
                        c_branch );
                      (Pattern.PVar (x, sort_matched), renv_matched, c_matched);
                    ]
                  in
                  let constrs', kind_map =
                    next kind_map maps renv_branch c_branch
                  in
                  ( Set.Poly.union_list
                    @@ [
                         (if is_impure_pure || is_pure_in_impures then
                            cgen_subtype_val ~config renv_branch
                              c_branch.val_type c.val_type
                          else Set.Poly.empty);
                         cgen_subeff ~config renv_matched rev_comp_effs
                           c_branch.val_type c;
                         constrs';
                         constrs_params;
                         constrs;
                       ],
                    kind_map ) ))
          in
          let constrs_matched, phi_matched =
            constr_of ~config renv_not_matched
          in
          ( Set.union constrs @@ Set.add constrs_matched
            @@ Formula.mk_imply
                 (Evaluator.simplify phi_matched)
                 (Formula.mk_false ()),
            kind_map )

  let rec env_and_rty_of_pat ~config mode ?(is_top_level = false) dom = function
    | Pattern.PAny _, is_fun, is_rec, sort ->
        let svmap =
          if
            config.Rtype.gen_ref_pred_for_type_vars
            && config.Rtype.share_ref_pred_with_same_type_vars
          then
            Map.of_set_exn
            @@ Set.Poly.map (Term.svs_of_sort sort) ~f:(fun sv ->
                   let pv = Ident.mk_fresh_pvar ~prefix:(Some "$sv") () in
                   ( sv,
                     let sort = Sort.SVar sv in
                     Rtype.mk_rbase sort
                     @@
                     let tv = Ident.mk_fresh_tvar () in
                     (tv, Rtype.mk_refpred ~config pv dom tv sort) ))
          else Map.Poly.empty
        in
        let rty =
          let refine = not is_fun (*ToDo*) in
          Rtype.val_of_sort ~config ~refine ~svmap dom sort
        in
        let adm_pvars =
          match mode with
          | HFL_Expectation with_cond ->
              let rett = Rtype.ret_of_val rty in
              if
                is_rec
                && not
                     ((Term.is_bool_sort @@ Rtype.sort_of_val rett)
                     || (Term.is_int_sort @@ Rtype.sort_of_val rett)
                     || (Term.is_dt_sort @@ Rtype.sort_of_val rett))
                (*ToDo*)
              then
                let _, phi = Rtype.pred_of_val rett in
                Set.Poly.map ~f:(fun (p, sorts) -> (p, with_cond, sorts))
                @@ (*ToDo:check if rett are props*) Formula.pred_sort_env_of phi
              else Set.Poly.empty
          | OCaml -> Set.Poly.empty
        in
        (Rtype.Env.mk_empty (), rty, adm_pvars)
    | Pattern.PVar (x, _sort), is_fun, is_rec, sort ->
        let svmap =
          if
            config.Rtype.gen_ref_pred_for_type_vars
            && config.Rtype.share_ref_pred_with_same_type_vars
          then
            Map.of_set_exn
            @@ Set.Poly.map (Term.svs_of_sort sort) ~f:(fun sv ->
                   let pv = Ident.mk_fresh_pvar () in
                   ( sv,
                     let sort = Sort.SVar sv in
                     Rtype.mk_rbase sort
                     @@
                     let tv = Ident.mk_fresh_tvar () in
                     (tv, Rtype.mk_refpred ~config pv dom tv sort) ))
          else Map.Poly.empty
        in
        let rty =
          let name =
            if is_top_level then Some (name_of_tvar x, "", 0) else None
          in
          let refine = not is_fun (*ToDo*) in
          Rtype.val_of_sort ~config ~refine ~svmap ~name dom sort
        in
        let adm_pvars =
          match mode with
          | HFL_Expectation with_cond ->
              let rett = Rtype.ret_of_val rty in
              if
                is_rec
                && not
                     ((Term.is_bool_sort @@ Rtype.sort_of_val rett)
                     || (Term.is_int_sort @@ Rtype.sort_of_val rett)
                     || (Term.is_dt_sort @@ Rtype.sort_of_val rett))
                (*ToDo*)
              then
                let _, phi = Rtype.pred_of_val rett in
                Set.Poly.map ~f:(fun (p, sorts) -> (p, with_cond, sorts))
                @@ (*ToDo:check if rett are props*) Formula.pred_sort_env_of phi
              else Set.Poly.empty
          | OCaml -> Set.Poly.empty
        in
        (Rtype.Env.singleton_ty x rty, rty, adm_pvars)
    | ( (Pattern.PTuple pats as pat),
        is_fun,
        is_rec,
        (T_tuple.STuple sorts as sort) ) ->
        let renvs, rtys, adm_pvarss =
          List.unzip3
          @@ List.map2_exn pats sorts ~f:(fun pat sort ->
                 env_and_rty_of_pat ~config mode dom (pat, is_fun, is_rec, sort))
        in
        let tup_ty, phi =
          let terms, sorts = List.unzip dom in
          let pvar = mk_fresh_pvar () in
          let phi =
            Formula.mk_atom
            @@ Atom.mk_pvar_app pvar (sorts @ [ sort ])
                 (* ToDo: dom can be masked by pat *)
                 (terms @ [ Pattern.term_of pat ])
          in
          let v = Rtype.mk_fresh_tvar_with "v" in
          ( Rtype.mk_rtuple rtys
            @@ ( v,
                 Formula.mk_atom
                 @@ Atom.mk_pvar_app pvar (sorts @ [ sort ])
                      (terms @ [ Term.mk_var v sort ]) ),
            phi )
        in
        ( Rtype.Env.add_phi
            (Rtype.Env.disj_union_list (* assume distinct *) renvs)
            phi,
          tup_ty,
          Set.Poly.union_list adm_pvarss )
    | Pattern.PCons _, _, _, _ ->
        failwith
          "[env_and_rty_of_pat] not reachable here because [let T x = ... in \
           ...] is parsed as [match ... with T x -> ...]"
    | _ -> failwith "[env_and_rty_of_pat] unsupported pattern"

  module Preprocessor = Preprocessor.Make (struct
    let config =
      Preprocessor.Config.make config.enable_pvar_elim false (*config.verbose*)
        Int.max_value
        (* [fixpoint] assumes that any intermediate predicate variables are eliminated for GFP predicate generation*)
        4 false
  end)

  type envs = {
    mode : mode;
    constrs : constr Set.Poly.t;
    exi_senv : sort_env_map;
    kind_map : (tvar, Kind.t) Map.Poly.t;
    fenv : FunEnv.t;
    dtenv : DTEnv.t;
    renv : Rtype.Env.t;
  }

  let pcsp_of ?(skolem_pred = false) ?(sol_space = Map.Poly.empty) envs constrs
      =
    (*Debug.print @@ lazy (sprintf "\n*** original:" );
      Debug.print @@ lazy (String.concat_map_set ~sep:"\n" constrs ~f:Formula.str_of);*)
    let phis =
      Set.Poly.map (Set.union envs.constrs constrs) ~f:(fun phi ->
          let phi = Evaluator.simplify phi in
          let tvs =
            Formula.term_sort_env_of (*ToDo: use sort_env_of instead?*) phi
          in
          Formula.mk_forall_if_bounded (Set.to_list tvs) phi)
    in
    (*Debug.print @@ lazy (sprintf "\n*** simplified:" );
      Debug.print @@ lazy (String.concat_map_set ~sep:"\n" phis ~f:Formula.str_of);*)
    let phis =
      Typeinf.typeinf ~print:(fun _ -> () (*Debug.print*)) ~to_sus:true
      @@ Set.to_list phis
    in
    (*Debug.print @@ lazy (sprintf "\n*** type inferred:" );
      Debug.print @@ lazy (String.concat_map_list ~sep:"\n" phis ~f:Formula.str_of);*)
    let pcsp =
      let exi_senv, kind_map =
        (*ToDo: given exi_senv and kind_map are incomplete? *)
        List.map phis ~f:Formula.pred_sort_env_of
        |> Set.Poly.union_list
        |> Set.fold ~init:(envs.exi_senv, envs.kind_map)
             ~f:(fun (exi_senv, kind_map) (pvar, sorts) ->
               let tvar = Ident.pvar_to_tvar pvar in
               if Map.Poly.mem exi_senv tvar then (
                 assert (Map.Poly.mem kind_map tvar);
                 (exi_senv, kind_map))
               else if Map.Poly.mem kind_map tvar then
                 let sort = Sort.mk_fun @@ sorts @ [ T_bool.SBool ] in
                 (Map.Poly.add_exn exi_senv ~key:tvar ~data:sort, kind_map)
               else
                 let sort = Sort.mk_fun @@ sorts @ [ T_bool.SBool ] in
                 ( Map.Poly.add_exn exi_senv ~key:tvar ~data:sort,
                   Map.Poly.add_exn kind_map ~key:tvar ~data:Kind.Ord (*ToDo*)
                 ))
      in
      PCSP.Problem.make ~skolem_pred phis
      @@ SMT.Problem.
           {
             uni_senv = Map.Poly.empty;
             exi_senv;
             kind_map;
             fenv =
               Map.Poly.filter envs.fenv ~f:(fun (_, _, _, is_rec, _) -> is_rec)
               (*ToDo*);
             dtenv = envs.dtenv;
           }
    in
    PCSP.Problem.set_params_sol_space pcsp sol_space

  let pren_of penv_dtrenv bpvs constrs =
    Map.of_set_exn
    @@ Set.Poly.filter_map ~f:(fun (Ident.Pvar n, sorts) ->
           if
             Set.exists penv_dtrenv ~f:(fun (pvar, sorts') ->
                 Stdlib.(pvar = Ident.Pvar n && sorts <> sorts'))
           then
             let name_inst =
               n ^ String.bracket
               @@ String.concat_map_list ~sep:"," sorts ~f:Term.str_of_sort
             in
             Some ((n, sorts), Ident.Pvar name_inst)
           else None)
    @@ Set.concat_map ~f:(Formula.pred_sort_env_of ~bpvs)
    @@ constrs

  let fixpoint ~config renv kind_map fenv dtenv penv_dtrenv pvs_preds bpvs pvmap
      constrs =
    Debug.print
    @@ lazy (sprintf "\n*** %d constraints generated:" @@ Set.length constrs);
    Debug.print
    @@ lazy (String.concat_map_set ~sep:"\n" constrs ~f:Formula.str_of);
    Debug.print
    @@ lazy
         ("kind: "
         ^ String.concat_map_list ~sep:", " (Map.Poly.to_alist kind_map)
             ~f:(fun (x, k) -> Ident.name_of_tvar x ^ " is " ^ Kind.str_of k));
    let constrs, bpvs =
      let pren =
        (* rename pvars in penv_dtrenv whose sort contains no sort variable*)
        Map.Poly.filter_keys ~f:(fun (_, sorts) ->
            Set.is_empty @@ Set.Poly.union_list
            @@ List.map sorts ~f:Term.svs_of_sort)
        @@ pren_of penv_dtrenv pvs_preds constrs
      in
      inst_pvs_dtrenv :=
        Set.union !inst_pvs_dtrenv (Set.Poly.of_list @@ Map.Poly.data pren);
      ( Set.Poly.map constrs ~f:(Formula.rename_sorted_pvars pren),
        Set.union bpvs !inst_pvs_dtrenv )
      (*Set.Poly.map constrs ~f:(Formula.map_atom ~f:(function
        | Atom.App (Predicate.Var (pvar, sorts), ts, _)
          when Set.mem pvs_dtrenv pvar &&
               Set.is_empty @@ Set.Poly.union_list @@
               List.map sorts ~f:Term.svs_of_sort ->
          let name = Ident.name_of_pvar pvar ^ String.bracket @@ String.concat_map_list ~sep:"\n" sorts ~f:Term.str_of_sort in
          Formula.mk_atom @@ Atom.mk_pvar_app (Ident.Pvar name) sorts ts
        | atom -> Formula.mk_atom atom))*)
    in
    let pcsp0 =
      (*ToDo*)
      pcsp_of
        {
          mode = OCaml (*dummy*);
          constrs = Set.Poly.empty;
          exi_senv = Map.Poly.empty;
          kind_map;
          fenv;
          dtenv;
          renv = Rtype.Env.mk_empty () (*dummy*);
        }
        constrs
    in
    let mu_pvmap =
      Map.Poly.filter_map pvmap ~f:(function `LFP pv -> Some pv | _ -> None)
    in
    let nu_pvmap =
      Map.Poly.filter_map pvmap ~f:(function `GFP pv -> Some pv | _ -> None)
    in
    let mu_pvs_dummy = Set.Poly.of_list @@ Map.Poly.data mu_pvmap in
    let nu_pvs_dummy = Set.Poly.of_list @@ Map.Poly.data nu_pvmap in
    let pvs_dummy = Set.Poly.union_list [ mu_pvs_dummy; nu_pvs_dummy ] in
    let _, pcsp =
      let bpvs =
        Set.Poly.map ~f:Ident.pvar_to_tvar
        @@ Set.Poly.union_list [ bpvs; pvs_dummy ]
      in
      (* the following is needed since Z3interface.sort_of invokes RtypeParser *)
      Rtype.cgen_config := config;
      Rtype.renv_ref := renv;
      set_dtenv dtenv;
      Preprocessor.preprocess pcsp0 ~bpvs
    in
    let clauses1, clauses2 =
      Set.partition_tf
        (PCSP.Problem.clauses_of pcsp)
        ~f:
          (Clause.pvs_of
          >> Set.Poly.map ~f:Ident.tvar_to_pvar
          >> Set.inter pvs_dummy >> Set.is_empty)
    in
    Debug.print @@ lazy "";
    let theta_mu =
      (*if Fn.non Map.Poly.is_empty mu_pvmap then*)
      Debug.print @@ lazy "*** inductive predicates extracted:";
      Debug.print @@ lazy "";
      Map.Poly.mapi mu_pvmap ~f:(fun ~key:pvar' ~data:pvar ->
          let env, t =
            ClauseSet.pred_of_pos (PCSP.Problem.senv_of pcsp0) clauses2
            @@ Ident.pvar_to_tvar pvar
          in
          let phi =
            Logic.ExtTerm.to_old_fml
              (PCSP.Problem.senv_of pcsp)
              (Map.Poly.of_alist_exn env, t)
          in
          assert (Set.is_empty @@ Set.inter (Formula.pvs_of phi) pvs_dummy);
          let env = Logic.to_old_sort_env_list env in
          Debug.print
          @@ lazy
               (sprintf "%s(%s) =mu\n  %s\n" (Ident.name_of_pvar pvar')
                  (str_of_sort_env_list Term.str_of_sort env)
                  (Formula.str_of phi));
          (env, phi))
    in
    mu_preds := Map.force_merge !mu_preds theta_mu;
    let theta_nu =
      (*if Fn.non Map.Poly.is_empty mu_pvmap then*)
      Debug.print @@ lazy "*** coinductive predicates extracted:";
      Debug.print @@ lazy "";
      Map.Poly.mapi nu_pvmap ~f:(fun ~key:pvar' ~data:pvar ->
          let env, t =
            ClauseSet.pred_of_pos (PCSP.Problem.senv_of pcsp0) clauses2
            @@ Ident.pvar_to_tvar pvar
          in
          let phi =
            Logic.ExtTerm.to_old_fml
              (PCSP.Problem.senv_of pcsp)
              (Map.Poly.of_alist_exn env, t)
          in
          assert (Set.is_empty @@ Set.inter (Formula.pvs_of phi) pvs_dummy);
          let env = Logic.to_old_sort_env_list env in
          Debug.print
          @@ lazy
               (sprintf "%s(%s) =nu\n  %s\n" (Ident.name_of_pvar pvar')
                  (str_of_sort_env_list Term.str_of_sort env)
                  (Formula.str_of phi));
          (env, phi))
    in
    nu_preds := Map.force_merge !nu_preds theta_nu;
    let constrs =
      Set.Poly.map clauses1
        ~f:
          (Clause.normalize_uni_senv >> Clause.to_senv_formula
          >> Logic.ExtTerm.to_old_fml (PCSP.Problem.senv_of pcsp))
    in
    Debug.print @@ lazy "*** predicate constraints extracted:";
    Debug.print @@ lazy "";
    Debug.print
    @@ lazy (String.concat_map_set ~sep:"\n" constrs ~f:Formula.str_of);
    Debug.print @@ lazy "";
    constrs

  let generalize ~config renv pat_renv constrs =
    (*ToDo: note that nu_preds and mu_preds can be type-polymorphic as well!*)
    let pvs_preds =
      Set.Poly.of_list @@ Map.Poly.(keys !mu_preds @ keys !nu_preds)
    in
    let pvs_renv = Set.diff (Rtype.Env.pvs_of renv) pvs_preds in
    let pvs_dtrenv = Set.union (get_pvs_dtrenv pvs_preds) !inst_pvs_dtrenv in
    let penv_constrs =
      Set.concat_map constrs ~f:(Formula.pred_sort_env_of ~bpvs:pvs_preds)
    in
    Map.Poly.map pat_renv ~f:(fun t ->
        let penv =
          let penv_val =
            let pvs_constrs = Set.Poly.map ~f:fst penv_constrs in
            Rtype.pred_sort_env_of_val ~bpvs:pvs_preds t
            (*ToDo*) |> Set.filter ~f:(fst >> Set.mem pvs_constrs >> not)
          in
          let penv_set =
            Set.filter (Set.union penv_val penv_constrs) ~f:(fun (pvar, _) ->
                (not (Set.mem pvs_renv pvar)) && not (Set.mem pvs_dtrenv pvar))
          in
          try Map.of_set_exn penv_set
          with _ ->
            failwith @@ sprintf "duplicate: %s"
            @@ str_of_pred_sort_env_set Term.str_of_sort penv_set
        in
        let svs =
          Set.diff
            (Term.svs_of_sort @@ Rtype.sort_of_val t)
            (Rtype.Env.svs_of renv)
        in
        Rtype.mk_type_poly ~config svs
        @@ Rtype.pure_comp_of_val ~config
        @@ Rtype.mk_pred_poly ~config penv constrs
        @@ Rtype.pure_comp_of_val ~config t)

  let cgen_let ~config mode ~is_top_level ?opsig fenv dtenv is_rec pats
      (is_pures, is_funs, next1s, c1s) kind_map maps renv =
    let open Rtype in
    let pat_renvs, cs, adm_pvarss =
      List.unzip3
      @@ List.map3_exn pats (List.zip_exn is_funs is_pures) c1s
           ~f:(fun pat (is_fun, is_pure) c1 ->
             let dom = Env.dep_args_of renv in
             let pat_renv, t, adm_pvars =
               env_and_rty_of_pat ~config mode ~is_top_level dom
                 (pat, is_fun, is_rec, c1.Sort.val_type)
             in
             let temp =
               if is_pure then (
                 assert (Sort.is_pure c1.cont_eff);
                 false)
               else true
             in
             let opsig =
               match opsig with Some opsig -> opsig | None -> `Sort c1.op_sig
             in
             ( pat_renv,
               comp_of_val ~config ~temp ~opsig ~cont:c1.cont_eff dom (*ToDo*) t,
               adm_pvars ))
    in
    let adm_pvars = Set.Poly.union_list adm_pvarss in
    let kind_map =
      Set.fold adm_pvars ~init:kind_map ~f:(fun acc (pv, with_cond, _) ->
          Map.Poly.add_exn acc ~key:(Ident.pvar_to_tvar pv)
            ~data:(Kind.Adm with_cond))
    in
    let renv_bound, (constrss, kind_maps) =
      let renv_bound, map =
        if is_rec then
          Env.update_with ~config renv
          @@ Env.disj_union_list (* assume distinct *) pat_renvs
        else (renv, Map.Poly.empty)
      in
      let cs', pvmap =
        let cs', pvmapss =
          List.unzip
          @@ List.map cs ~f:(fun c ->
                 let val_type, pvmap =
                   fresh_eff_pvars_val ~print:Debug.print c.val_type
                 in
                 (rename_comp ~config map { c with val_type }, pvmap))
        in
        (cs', Map.force_merge_list pvmapss)
      in
      let pvs_preds =
        Set.Poly.of_list @@ Map.Poly.(keys !mu_preds @ keys !nu_preds)
      in
      let pvs_renv = Set.diff (Env.pvs_of (*ToDo*) renv) pvs_preds in
      let penv_dtrenv = get_penv_dtrenv pvs_preds in
      let pvs_dtrenv = Set.Poly.map ~f:fst penv_dtrenv in
      let cs_pvs =
        Set.Poly.union_list
        @@ List.map cs ~f:(pvs_of_comp >> Fn.flip Set.diff pvs_preds)
      in
      ( renv_bound,
        List.unzip
        @@ List.map3_exn (*ToDo*) pats next1s (List.zip_exn cs' cs)
             ~f:(fun pat next (c', c) ->
               (*if is_top_level then*)
               Debug.print
               @@ lazy
                    (sprintf
                       ">>>>>>>>> predicate constraint generation for %s with\n\
                       \  %s\n"
                       (Pattern.str_of pat)
                       (Rtype.str_of_comp ~config c'));
               let constrs, kind_map =
                 let bpvs =
                   Set.Poly.union_list
                   @@ [
                        pvs_preds;
                        pvs_renv;
                        pvs_dtrenv;
                        (if is_rec then cs_pvs
                         else
                           Set.Poly.map ~f:fst
                           @@ pred_sort_env_of_comp (*ToDo*) ~bpvs:pvs_preds c);
                      ]
                 in
                 let constrs, kind_map = next kind_map maps renv_bound c' in
                 ( fixpoint ~config renv kind_map fenv dtenv penv_dtrenv
                     pvs_preds bpvs pvmap constrs,
                   kind_map )
               in
               (*if is_top_level then*)
               Debug.print
               @@ lazy "<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<\n";
               (constrs, kind_map)) )
    in
    let generalizable =
      List.for_all is_pures ~f:Fn.id
      && List.for_all pats ~f:(Pattern.sort_of >> Sort.is_arrow)
    in
    let renv_body, map =
      (*shadowing*)
      Env.update_with ~config renv
      @@ Env.disj_union_list
      (* assume the following are distinct *)
      @@
      if generalizable then
        let constrs_merged = Set.Poly.union_list constrss in
        List.map2_exn pat_renvs constrss
          ~f:(fun (pat_renv, phis (* must be empty *)) constrs ->
            ( generalize ~config renv pat_renv
                (if is_rec then constrs_merged else constrs),
              phis ))
      else pat_renvs
    in
    ( List.map cs ~f:(rename_comp ~config map),
      renv_bound,
      adm_pvars,
      (if generalizable then Set.Poly.empty else Set.Poly.union_list constrss),
      Map.force_merge_list kind_maps,
      renv_body,
      map )

  let sort_of_either = function
    | First (_, _, c) -> c.Sort.val_type
    | Second (_, sort) -> sort

  let subst_all_either maps = function
    | First (pure, next, c) -> First (pure, next, Term.subst_triple maps c)
    | Second (x, sort) -> Second (x, Term.subst_sort maps sort)

  let subst_all_opt maps = function
    | Some (next, cont) -> Some (next, Term.subst_cont maps cont)
    | None -> None

  let cgen_either ~config kind_map renv maps opsig =
    let open Rtype in
    function
    | First (pure, next, c (*c.op_sig*)) ->
        let x = mk_fresh_tvar_with "dummy_" in
        let c =
          let refine, dom = (true, Env.dep_args_of renv) in
          let temp =
            if pure then (
              assert (Sort.is_pure c.Sort.cont_eff);
              false)
            else true
          in
          comp_of_sort ~config ~refine ~temp ~opsig ~cont:c.cont_eff dom
            c.val_type
        in
        ((x, c, false), next kind_map maps renv c)
    | Second (x, sort) ->
        let c, constrs =
          match Env.look_up renv x with
          | Some xty ->
              let xty, constrs, _kind_map (*ToDo*) =
                instantiate_val ~print:Debug.print ~config
                  (Env.dep_args_of renv) Map.Poly.empty (*ToDo*)
                  (Map.Poly.empty, Map.Poly.empty)
                  (xty, sort)
              in
              (comp_of_term ~config (Term.mk_var x sort) xty, constrs)
          | None ->
              failwith
              @@ sprintf "[cgen_either] unbound variable: %s : %s\nrenv = %s"
                   (name_of_tvar x) (Term.str_of_sort sort)
                   (Env.str_of ~config renv)
        in
        ((x, c, true), (constrs, kind_map))

  let cgen_expr ~config mode fenv dtenv senv (expr : expression) =
    let open Rtype in
    MBcgen.fold_expr dtenv senv expr
      ~f:
        (object
           method f_annot (attrs, next) kind_map maps renv ty =
             let c =
               let c_annot_rty_opt =
                 MBcgen.find_comp_attrs ~config ~renv ~dtenv
                   ~attr_name:"annot_rty" attrs
               in
               let c_annot_opt =
                 MBcgen.find_comp_attrs ~config ~renv ~dtenv ~attr_name:"annot"
                   attrs
               in
               match (c_annot_rty_opt, c_annot_opt) with
               | Some c, _ | None, Some c -> c
               | None, None -> assert false
             in
             Debug.print
             @@ lazy
                  (sprintf "[rcaml:annot] %s <: %s\n" (str_of_comp ~config c)
                     (str_of_comp ~config ty));
             let constrs, kind_map = next kind_map maps renv c in
             ( Set.Poly.union_list
                 [ cgen_subtype_comp ~config renv c ty; constrs ],
               kind_map )

           method f_unif (next, sort) kind_map maps renv ty =
             let sort = Term.subst_sort maps sort in
             (* *)
             let use_adm_pred = true in
             let enable_lhs_param = true (*ToDo*) in
             Debug.print
             @@ lazy (sprintf "[rcaml:unif] %s\n" @@ str_of_comp ~config ty);
             let y = Ident.mk_fresh_tvar () in
             let yt = Term.mk_var y T_real.SReal in
             let num =
               match sort with
               | Sort.SArrow (T_real.SReal, c) -> (
                   match c.val_type with
                   | T_real.SReal -> 1
                   | T_tuple.STuple sorts
                     when List.for_all sorts ~f:Term.is_real_sort ->
                       List.length sorts
                   | _ -> failwith "[f_unif] unsupported sort")
               | _ -> failwith "[f_unif] unsupported sort"
             in
             let dom = Env.dep_args_of renv in
             let renv', (c, c'), constrs', kind_map' =
               let v = Ident.mk_fresh_tvar () in
               let vt = Term.mk_var v T_real.SReal in
               if use_adm_pred then
                 let ts, ts', pvars =
                   let dom =
                     List.filter dom ~f:(fun (_, s) ->
                         Term.is_int_sort s || Term.is_real_sort s)
                   in
                   List.unzip3
                   @@ List.init num ~f:(fun _ ->
                          let pvar =
                            Ident.mk_fresh_pvar ~prefix:(Some "PARAM_") ()
                          in
                          let phi =
                            let args =
                              dom @ [ (yt, T_real.SReal); (vt, T_real.SReal) ]
                            in
                            Formula.mk_atom
                            @@ Atom.mk_pvar_app pvar (List.map ~f:snd args)
                                 (List.map ~f:fst args)
                          in
                          let phi' =
                            let args =
                              dom
                              @ [
                                  ( T_real.mk_real Q.(one / of_int 2),
                                    T_real.SReal );
                                  (vt, T_real.SReal);
                                ]
                            in
                            Formula.mk_atom
                            @@ Atom.mk_pvar_app pvar (List.map ~f:snd args)
                                 (List.map ~f:fst args)
                          in
                          ( Rtype.mk_rbase T_real.SReal (v, phi),
                            Rtype.mk_rbase T_real.SReal (v, phi'),
                            pvar ))
                 in
                 ( renv,
                   (match (ts, ts') with
                   | [ t ], [ t' ] ->
                       ( Rtype.pure_comp_of_val ~config t,
                         Rtype.pure_comp_of_val ~config t' )
                   | _, _ ->
                       ( Rtype.pure_comp_of_val ~config
                         @@ Rtype.mk_rtuple ts (mk_fresh_trivial_pred ()),
                         Rtype.pure_comp_of_val ~config
                         @@ Rtype.mk_rtuple ts' (mk_fresh_trivial_pred ()) )),
                   Set.Poly.empty,
                   List.fold pvars ~init:kind_map ~f:(fun kind_map x ->
                       Map.Poly.add_exn kind_map ~key:(Ident.pvar_to_tvar x)
                         ~data:Kind.Integ) )
               else
                 let ts, ts', lhs_paramss, rhs_paramss =
                   let args =
                     (if true (*ToDo*) then List.map ~f:T_real.mk_rabs
                      else Fn.id)
                     @@ List.filter_map dom ~f:(fun (t, s) ->
                            if Term.is_real_sort s then Some t
                            else if Term.is_int_sort s then
                              Some (T_irb.mk_int_to_real t)
                            else None)
                   in
                   List.unzip4
                   @@ List.init num ~f:(fun _ ->
                          let lhs_coeff = Ident.mk_fresh_parameter () in
                          let lhs_coeff_t =
                            T_irb.mk_int_to_real
                            @@ Term.mk_var lhs_coeff T_int.SInt
                          in
                          let coeff = Ident.mk_fresh_parameter () in
                          let coeff_t =
                            T_irb.mk_int_to_real @@ Term.mk_var coeff T_int.SInt
                          in
                          let const = Ident.mk_fresh_parameter () in
                          let const_t =
                            T_irb.mk_int_to_real @@ Term.mk_var const T_int.SInt
                          in
                          let coeffs =
                            List.init (List.length args) ~f:(fun _ ->
                                Ident.mk_fresh_parameter ())
                          in
                          let coeffs_t =
                            List.map coeffs ~f:(fun c ->
                                T_irb.mk_int_to_real @@ Term.mk_var c T_int.SInt)
                          in
                          let cx =
                            List.fold ~init:const_t
                              (List.map2_exn coeffs_t args ~f:T_real.mk_rmult)
                              ~f:T_real.mk_radd
                          in
                          let phi =
                            Formula.mk_and
                              (Formula.mk_atom
                              @@ T_real.mk_rleq (T_real.rzero ()) vt)
                              (Formula.mk_atom
                              @@ T_real.mk_rleq
                                   (if enable_lhs_param then
                                      T_real.mk_rmult lhs_coeff_t vt
                                    else vt)
                              @@ T_real.mk_radd cx (T_real.mk_rmult coeff_t yt)
                              )
                          in
                          let phi' =
                            Formula.mk_and
                              (Formula.mk_atom
                              @@ T_real.mk_rleq (T_real.rzero ()) vt)
                              (Formula.mk_atom
                              @@ T_real.mk_rleq
                                   (if enable_lhs_param then
                                      T_real.mk_rmult lhs_coeff_t vt
                                    else vt)
                              @@ T_real.mk_radd cx
                                   (T_real.mk_rmult coeff_t
                                      (T_real.mk_real Q.(one / of_int 2))))
                          in
                          Debug.print
                          @@ lazy
                               (sprintf "%s is integrated to %s"
                                  (Formula.str_of phi) (Formula.str_of phi'));
                          ( Rtype.mk_rbase T_real.SReal (v, phi),
                            Rtype.mk_rbase T_real.SReal (v, phi'),
                            (if enable_lhs_param then [ lhs_coeff ] else []),
                            coeff :: const :: coeffs ))
                 in
                 let lhs_params = List.concat lhs_paramss in
                 let rhs_params = List.concat rhs_paramss in
                 let lhs_pvars =
                   List.map lhs_params ~f:(fun _ ->
                       Ident.mk_fresh_pvar ~prefix:(Some "PARAM_") ())
                 in
                 let rhs_pvars =
                   List.map rhs_params ~f:(fun _ ->
                       Ident.mk_fresh_pvar ~prefix:(Some "PARAM_") ())
                 in
                 let constrs_lhs_pvars =
                   Set.Poly.of_list
                   @@ List.map2_exn lhs_pvars lhs_params ~f:(fun p x ->
                          let xt = Term.mk_var x T_int.SInt in
                          Formula.mk_imply
                            (Formula.mk_atom
                            @@ Atom.mk_pvar_app p [ T_int.SInt ] [ xt ])
                          @@ Formula.mk_atom
                          @@ T_int.mk_leq (T_int.one ()) xt)
                 in
                 let constrs_rhs_pvars =
                   if true (*ToDo*) then
                     Set.Poly.of_list
                     @@ List.map2_exn rhs_pvars rhs_params ~f:(fun p x ->
                            let xt = Term.mk_var x T_int.SInt in
                            Formula.mk_imply
                              (Formula.mk_atom
                              @@ Atom.mk_pvar_app p [ T_int.SInt ] [ xt ])
                            @@ Formula.mk_atom
                            @@ T_int.mk_leq (T_int.zero ()) xt)
                   else Set.Poly.empty
                 in
                 ( Rtype.Env.add_phis renv
                     (Set.Poly.of_list
                     @@ List.map2_exn (lhs_pvars @ rhs_pvars)
                          (lhs_params @ rhs_params) ~f:(fun p x ->
                            Formula.mk_atom
                            @@ Atom.mk_pvar_app p [ T_int.SInt ]
                                 [ Term.mk_var x T_int.SInt ])),
                   (match (ts, ts') with
                   | [ t ], [ t' ] ->
                       ( Rtype.pure_comp_of_val ~config t,
                         Rtype.pure_comp_of_val ~config t' )
                   | _, _ ->
                       ( Rtype.pure_comp_of_val ~config
                         @@ Rtype.mk_rtuple ts (mk_fresh_trivial_pred ()),
                         Rtype.pure_comp_of_val ~config
                         @@ Rtype.mk_rtuple ts' (mk_fresh_trivial_pred ()) )),
                   Set.union constrs_lhs_pvars constrs_rhs_pvars,
                   List.fold (lhs_pvars @ rhs_pvars) ~init:kind_map
                     ~f:(fun kind_map x ->
                       Map.Poly.add_exn kind_map ~key:(Ident.pvar_to_tvar x)
                         ~data:Kind.FN) )
             in
             let cty =
               let t =
                 let x = Ident.mk_fresh_tvar () in
                 Rtype.mk_rbase T_real.SReal
                   ( x,
                     Formula.and_of
                     @@ Formula.mk_range_real
                          (Term.mk_var x T_real.SReal)
                          Q.zero Q.one )
               in
               pure_comp_of_val ~config
               @@ mk_rarrow y t c (mk_fresh_trivial_pred ())
             in
             let constrs, kind_map = next kind_map' maps renv' cty in
             ( Set.Poly.union_list
                 [ cgen_subtype_comp ~config renv' c' ty; constrs; constrs' ],
               kind_map )

           method f_var (x, sort) kind_map maps renv ty =
             let sort = Term.subst_sort maps sort in
             (* *)
             (*print_endline @@ Ident.name_of_tvar x ^ ": " ^ Term.str_of_sort sort;*)
             let xty, constrs, kind_map =
               match Env.look_up renv x with
               | Some xty ->
                   let xty, constrs, kind_map =
                     instantiate_val ~print:Debug.print ~config
                       (Env.dep_args_of renv) kind_map
                       (Map.Poly.empty, Map.Poly.empty)
                       (xty, sort)
                   in
                   ( comp_of_term ~config (Term.mk_var x sort) xty,
                     constrs,
                     kind_map )
               | None ->
                   failwith
                   @@ sprintf "[rcaml:var] unbound variable: %s : %s\nrenv = %s"
                        (name_of_tvar x) (str_of_comp ~config ty)
                        (Env.str_of ~config renv)
             in
             Debug.print
             @@ lazy
                  (sprintf "[rcaml:var] %s : %s <: %s\n" (name_of_tvar x)
                     (str_of_comp ~config xty) (str_of_comp ~config ty));
             ( Set.Poly.union_list
                 [ constrs; cgen_subtype_comp ~config renv xty ty ],
               kind_map )

           method f_const term kind_map maps renv ty =
             let term = Term.subst_all maps term in
             (* *)
             let cty, constrs, kind_map =
               let cty =
                 try
                   let (x, _), _ = Term.let_var term in
                   if
                     String.(
                       Ident.name_of_tvar x = "Stdlib.ref"
                       || Ident.name_of_tvar x = "Stdlib.!"
                       || Ident.name_of_tvar x = "Stdlib.:=")
                   then
                     let sv = Ident.mk_fresh_svar () in
                     let pv = Ident.mk_fresh_pvar () in
                     let sort = Sort.SVar sv in
                     let rty =
                       mk_rbase sort
                       @@
                       let tv = Ident.mk_fresh_tvar () in
                       ( tv,
                         if config.enable_pred_poly_for_ref_types then
                           mk_refpred ~config pv (Env.dep_args_of renv) tv sort
                         else Formula.mk_true () )
                     in
                     let penv = Map.Poly.singleton pv [ sort ] in
                     let x_arg = mk_fresh_tvar_with "x" in
                     mk_type_poly ~config (Set.Poly.singleton sv)
                     @@ pure_comp_of_val ~config
                     @@ (if config.enable_pred_poly_for_ref_types then fun ty ->
                           mk_pred_poly ~config penv Set.Poly.empty
                           @@ pure_comp_of_val ~config ty
                         else Fn.id)
                     @@
                     if String.(Ident.name_of_tvar x = "Stdlib.ref") then
                       mk_rarrow x_arg rty
                         (pure_comp_of_val ~config
                         @@ mk_rref rty (mk_fresh_trivial_pred ()))
                         (mk_fresh_trivial_pred ())
                     else if String.(Ident.name_of_tvar x = "Stdlib.!") then
                       mk_rarrow x_arg
                         (mk_rref rty (mk_fresh_trivial_pred ()))
                         (pure_comp_of_val ~config rty)
                         (mk_fresh_trivial_pred ())
                     else if String.(Ident.name_of_tvar x = "Stdlib.:=") then
                       mk_rarrow x_arg
                         (mk_rref rty (mk_fresh_trivial_pred ()))
                         (pure_comp_of_val ~config
                         @@ mk_rarrow (mk_fresh_tvar_with "x") rty
                              (pure_comp_of_val ~config
                             @@ simple_val_of_sort ~config @@ Datatype.sort_of
                             @@ Datatype.mk_unit_dt ())
                              (mk_fresh_trivial_pred ()))
                         (mk_fresh_trivial_pred ())
                     else assert false
                   else of_term ~print:Debug.print ~config term
                 with _ -> of_term ~print:Debug.print ~config term
               in
               instantiate_val ~print:Debug.print ~config (Env.dep_args_of renv)
                 kind_map
                 (Map.Poly.empty, Map.Poly.empty)
                 (cty, sort_of_comp ty)
             in
             Debug.print
             @@ lazy
                  (sprintf "[rcaml:const] %s : %s <: %s\n" (Term.str_of term)
                     (str_of_val ~config cty) (str_of_comp ~config ty));
             ( Set.Poly.union_list
               @@ [
                    constrs;
                    cgen_subtype_comp ~config renv
                      (pure_comp_of_val ~config cty)
                      ty;
                  ],
               kind_map )

           method f_construct _dt cons_name nexts_either kind_map maps renv ty =
             (*let dt = Datatype.subst maps dt in*)
             let nexts_either =
               List.map nexts_either ~f:(subst_all_either maps)
             in
             (* *)
             let cty, constrs, kind_map' =
               let cty = Map.Poly.find_exn !dtrenv cons_name in
               Debug.print
               @@ lazy
                    (sprintf "[rcaml:constructor] (%s : %s) (...) <: %s\n"
                       cons_name (str_of_val ~config cty)
                       (str_of_comp ~config ty));
               let sorts = List.map nexts_either ~f:sort_of_either in
               if true then
                 instantiate_val ~print:Debug.print ~config
                   (Env.dep_args_of renv) kind_map
                   (Map.Poly.empty, Map.Poly.empty)
                   (cty, LogicOld.Sort.mk_fun @@ sorts @ [ sort_of_comp ty ])
               else
                 (* can the following lose precision? *)
                 instantiate_val_con true ~config (Env.dep_args_of renv)
                   kind_map
                   (cty, Some sorts, ty.val_type)
             in
             let kind_map = Map.force_merge kind_map kind_map' in
             let res, constrs', kind_map =
               let opsig = `Refined ty.op_sig in
               List.fold_right nexts_either ~init:([], Set.Poly.empty, kind_map)
                 ~f:(fun next (res, constrs1, kind_map) ->
                   let r, (constrs2, kind_map) =
                     cgen_either ~config kind_map renv maps opsig next
                   in
                   (r :: res, Set.union constrs1 constrs2, kind_map))
             in
             let cs = List.map res ~f:snd3 in
             let cs', _, fun_ty =
               let ts = List.map cs ~f:(fun c -> c.val_type) in
               let xs =
                 List.map cs ~f:(fun _ -> mk_fresh_tvar_with "x" (* dummy *))
               in
               let temp, opsig, cont =
                 (false, `Refined (ALMap.empty, None), None)
               in
               (* pure *)
               of_args_ret ~config ~temp ~opsig ~cont [] xs ts ty.val_type
             in
             let rev_comp_effs =
               List.map ~f:(fun c -> (Pattern.PAny (sort_of_comp c), renv, c))
               @@ List.rev cs'
               @ (pure_comp_of_val ~config fun_ty :: cs)
             in
             ( Set.Poly.union_list
               @@ [
                    constrs;
                    cgen_subeff ~config renv rev_comp_effs ty.val_type ty;
                    cgen_subtype_val renv ~config cty fun_ty;
                    constrs';
                  ],
               kind_map )

           method f_apply (pure1, next1, opsig1s, opsig1, cont1s, cont1)
               next2s_either kind_map maps renv ty =
             let _opsig1s = List.map opsig1s ~f:(Term.subst_opsig maps) in
             let _opsig1 = Term.subst_opsig maps opsig1 in
             let cont1s = List.map cont1s ~f:(Term.subst_cont maps) in
             let cont1 = Term.subst_cont maps cont1 in
             let next2s_either =
               List.map next2s_either ~f:(subst_all_either maps)
             in
             (* *)
             Debug.print
             @@ lazy (sprintf "[rcaml:apply] %s\n" @@ str_of_comp ~config ty);
             let opsig =
               `Refined ty.op_sig
               (* ToDo: use opsig1s and opsig1 instead *)
             in
             let res, constrs, kind_map =
               List.fold_right next2s_either
                 ~init:([], Set.Poly.empty, kind_map)
                 ~f:(fun next (res, constrs1, kind_map) ->
                   let r, (constrs2, kind_map) =
                     cgen_either ~config kind_map renv maps opsig next
                   in
                   (r :: res, Set.union constrs1 constrs2, kind_map))
             in
             let cs = List.map res ~f:snd3 in
             let cs', dom', fun_ty =
               let ts = List.map cs ~f:(fun c -> c.val_type) in
               let xs =
                 List.map cs ~f:(fun _ -> mk_fresh_tvar_with "x" (* dummy *))
               in
               let dom = Env.dep_args_of renv in
               let temp, cont = (true, Some cont1s) in
               of_args_ret ~config ~temp ~opsig ~cont dom xs ts ty.val_type
             in
             let fun_ty =
               let temp =
                 if pure1 then (
                   assert (Sort.is_pure cont1);
                   false)
                 else true
               in
               let cont = cont1 in
               comp_of_val ~config ~temp ~opsig ~cont dom' fun_ty
             in
             (*assert Stdlib.(sort1 = sort_of_val fun_ty);*)
             let rev_comp_effs =
               List.map ~f:(fun c -> (Pattern.PAny (sort_of_comp c), renv, c))
               @@ List.rev cs'
               @ (fun_ty :: (*ToDo:List.rev*) cs)
             in
             let constrs', kind_map = next1 kind_map maps renv fun_ty in
             ( Set.Poly.union_list
               @@ [
                    cgen_subeff ~config renv rev_comp_effs ty.val_type ty;
                    constrs';
                    constrs;
                  ],
               kind_map )

           method f_tuple nexts_either kind_map maps renv ty =
             let nexts_either =
               List.map nexts_either ~f:(subst_all_either maps)
             in
             (* *)
             Debug.print
             @@ lazy (sprintf "[rcaml:tuple] %s\n" @@ str_of_comp ~config ty);
             let res, constrs, kind_map =
               let opsig = `Refined ty.op_sig in
               List.fold_right nexts_either ~init:([], Set.Poly.empty, kind_map)
                 ~f:(fun next (res, constrs1, kind_map) ->
                   let r, (constrs2, kind_map) =
                     cgen_either ~config kind_map renv maps opsig next
                   in
                   (r :: res, Set.union constrs1 constrs2, kind_map))
             in
             let cs = List.map res ~f:snd3 in
             let renv', tup_ty =
               let ts = List.map cs ~f:(fun c -> c.val_type) in
               let xs =
                 List.map cs ~f:(fun _ -> mk_fresh_tvar_with "x" (* dummy *))
               in
               let pred =
                 let sorts = List.map nexts_either ~f:sort_of_either in
                 let v = mk_fresh_tvar_with "v" in
                 ( v,
                   Formula.eq (Term.mk_var v @@ T_tuple.STuple sorts)
                   @@ T_tuple.mk_tuple_cons sorts
                   @@ List.map2_exn xs sorts ~f:Term.mk_var )
               in
               ( Env.disj_union renv @@ Env.of_list @@ List.zip_exn xs ts,
                 mk_rtuple ts pred )
             in
             let rev_comp_effs =
               List.map cs ~f:(fun c ->
                   (Pattern.PAny (sort_of_comp c), renv, c))
             in
             ( Set.Poly.union_list
               @@ [
                    cgen_subeff ~config renv rev_comp_effs tup_ty ty;
                    cgen_subtype_val ~config renv' tup_ty ty.val_type;
                    constrs;
                  ],
               kind_map )

           method f_function pats t_annot_rty_opt (nexts, conts) kind_map maps
               renv ty =
             let pats = List.map pats ~f:(Pattern.subst_sort maps) in
             let conts = List.map conts ~f:(Term.subst_cont maps) in
             (* *)
             Debug.print
             @@ lazy (sprintf "[rcaml:function] %s\n" @@ str_of_comp ~config ty);
             match ty.val_type with
             | RArrow (x, t, c, pred) ->
                 let x' = mk_fresh_tvar_with "matched_" in
                 let t' = rename_val ~config (Map.Poly.singleton x x') t in
                 let c' = rename_comp ~config (Map.Poly.singleton x x') c in
                 let t', constr_annot =
                   (* constr on refinement type annotations on arguments *)
                   match t_annot_rty_opt with
                   | Some t_annot ->
                       (* print_endline @@ "annotated: " ^ str_of_val ~config t_annot; *)
                       (t_annot, cgen_subtype_val ~config renv t' t_annot)
                   | None -> (t', Set.Poly.empty)
                 in
                 let constrs_renv, phi_renv = constr_of ~config renv in
                 let constrs, kind_map =
                   cgen_pattern_match ~config
                     (x', pure_comp_of_val ~config t', false)
                     pats (nexts, conts) kind_map maps renv c'
                 in
                 ( Set.Poly.union_list
                     [
                       cgen_check_pure ~config renv ty;
                       Set.add constrs_renv
                       @@ Formula.mk_imply
                            (Evaluator.simplify phi_renv)
                            (snd pred (*ToDo: the first element is ignored*));
                       constr_annot;
                       constrs;
                     ],
                   kind_map )
             | _ -> failwith "f_function"

           method f_ite (next1, cont1) (next2, cont2) next3_opt kind_map maps
               renv ty =
             let cont1 = Term.subst_cont maps cont1 in
             let cont2 = Term.subst_cont maps cont2 in
             let next3_opt = subst_all_opt maps next3_opt in
             (* *)
             Debug.print
             @@ lazy (sprintf "[rcaml:ite] %s\n" @@ str_of_comp ~config ty);
             let opsig = `Refined ty.op_sig in
             let c_cond =
               let refine, dom = (true, Env.dep_args_of renv) in
               let temp, cont = (true, cont1) in
               let name =
                 Some (name_of_tvar @@ mk_fresh_tvar_with "cond", "", 0)
               in
               comp_of_sort ~config ~refine ~temp ~opsig ~cont ~name dom
                 T_bool.SBool
             in
             let x_cond = Ident.mk_fresh_tvar () in
             let renv_then, renv_else =
               let renv = Env.set_ty renv x_cond c_cond.val_type in
               let t = Term.mk_var x_cond T_bool.SBool in
               ( Env.add_phi renv @@ Formula.eq t (T_bool.mk_true ()),
                 Env.add_phi renv @@ Formula.eq t (T_bool.mk_false ()) )
             in
             let is_impure_pure_then =
               Fn.non Sort.is_pure cont1 && Sort.is_pure cont2
             in
             let is_then_pure_else_impure =
               Sort.is_pure cont2
               &&
               match next3_opt with
               | Some (_, cont3) -> Fn.non Sort.is_pure cont3
               | _ -> false
             in
             let c_then =
               let dom_then = Env.dep_args_of renv_then in
               let temp, cont = (true, cont2) in
               comp_of_val ~config ~temp ~opsig ~cont dom_then
               @@
               if is_impure_pure_then || is_then_pure_else_impure then
                 val_of_sort ~config ~refine:true dom_then @@ sort_of_comp ty
               else ty.val_type
             in
             let rev_comp_effs_then =
               [
                 (Pattern.PAny (sort_of_comp c_then), renv_then, c_then);
                 (Pattern.PVar (x_cond, sort_of_comp c_cond), renv, c_cond);
               ]
             in
             let constrs1, kind_map = next1 kind_map maps renv c_cond in
             let constrs2, kind_map = next2 kind_map maps renv_then c_then in
             let constrss3, kind_map =
               match next3_opt with
               | None -> ([], kind_map)
               | Some (next3, cont3) ->
                   let is_impure_pure_else =
                     Fn.non Sort.is_pure cont1 && Sort.is_pure cont3
                   in
                   let is_then_impure_else_pure =
                     Fn.non Sort.is_pure cont2 && Sort.is_pure cont3
                   in
                   let c_else =
                     let dom_else = Env.dep_args_of renv_else in
                     let temp, cont = (true, cont3) in
                     comp_of_val ~config ~temp ~opsig ~cont dom_else
                     @@
                     if is_impure_pure_else || is_then_impure_else_pure then
                       val_of_sort ~config ~refine:true dom_else
                       @@ sort_of_comp ty
                     else ty.val_type
                   in
                   let rev_comp_effs_else =
                     [
                       (Pattern.PAny (sort_of_comp c_else), renv_else, c_else);
                       (Pattern.PVar (x_cond, sort_of_comp c_cond), renv, c_cond);
                     ]
                   in
                   let constrs3, kind_map =
                     next3 kind_map maps renv_else c_else
                   in
                   ( [
                       (if is_impure_pure_else || is_then_impure_else_pure then
                          cgen_subtype_val ~config renv_else c_else.val_type
                            ty.val_type
                        else Set.Poly.empty);
                       cgen_subeff ~config renv rev_comp_effs_else
                         c_else.val_type ty;
                       constrs3;
                     ],
                     kind_map )
             in
             ( Set.Poly.union_list
               @@ constrs1
                  :: (if is_impure_pure_then || is_then_pure_else_impure then
                        cgen_subtype_val ~config renv_then c_then.val_type
                          ty.val_type
                      else Set.Poly.empty)
                  :: cgen_subeff ~config renv rev_comp_effs_then c_then.val_type
                       ty
                  :: constrs2 :: constrss3,
               kind_map )

           method f_match next1_either pats (nexts, effs) kind_map maps renv ty
               =
             let pats = List.map pats ~f:(Pattern.subst_sort maps) in
             let effs = List.map effs ~f:(Term.subst_cont maps) in
             let next1_either = subst_all_either maps next1_either in
             (* *)
             let opsig = `Refined ty.op_sig in
             let matched, (constrs1, kind_map) =
               cgen_either ~config kind_map renv maps opsig next1_either
             in
             Debug.print
             @@ lazy
                  (sprintf "[rcaml:match] match %s : %s with ... : %s\n"
                     (name_of_tvar @@ fst3 matched)
                     (str_of_comp ~config @@ snd3 matched)
                     (str_of_comp ~config ty));
             let constrs, kind_map =
               cgen_pattern_match ~config matched pats (nexts, effs) kind_map
                 maps renv ty
             in
             (Set.Poly.union_list [ constrs1; constrs ], kind_map)

           method f_assert (next_opt, cont) kind_map maps renv ty =
             let cont = Term.subst_cont maps cont in
             (* *)
             Debug.print
             @@ lazy (sprintf "[rcaml:assert] %s\n" @@ str_of_comp ~config ty);
             match next_opt with
             | None ->
                 let constrs_renv, phi_renv = constr_of ~config renv in
                 ( Set.add constrs_renv
                   @@ Formula.mk_imply
                        (Evaluator.simplify phi_renv)
                        (Formula.mk_false ()),
                   kind_map )
             | Some next ->
                 let c_cond, renv_then, renv_else =
                   let c_cond =
                     let refine, dom = (true, Env.dep_args_of renv) in
                     let temp, opsig = (true, `Refined ty.op_sig) in
                     let name =
                       Some (name_of_tvar @@ mk_fresh_tvar_with "cond", "", 0)
                     in
                     comp_of_sort ~config ~refine ~temp ~opsig ~cont ~name dom
                       T_bool.SBool
                   in
                   let params, _, pred = let_rgeneral c_cond.val_type in
                   assert (List.is_empty params);
                   ( c_cond,
                     Env.add_phi renv @@ Formula.apply_pred pred
                     @@ T_bool.mk_true (),
                     Env.add_phi renv @@ Formula.apply_pred pred
                     @@ T_bool.mk_false () )
                 in
                 let rev_comp_effs =
                   [ (Pattern.PAny (sort_of_comp c_cond), renv, c_cond) ]
                 in
                 let ty_then =
                   simple_val_of_sort ~config @@ Datatype.sort_of
                   @@ Datatype.mk_unit_dt ()
                 in
                 let constrs_else, phi_else = constr_of ~config renv_else in
                 let constrs, kind_map = next kind_map maps renv c_cond in
                 ( Set.Poly.union_list
                   @@ [
                        constrs;
                        cgen_subeff ~config renv_then rev_comp_effs ty_then ty;
                        cgen_subtype_val ~config renv_then ty_then
                        @@ ty.val_type;
                        Set.add constrs_else
                        @@ Formula.mk_imply
                             (Evaluator.simplify phi_else)
                             (Formula.mk_false ());
                      ],
                   kind_map )

           method f_let_and is_rec pats defs (next2, cont2) kind_map maps renv
               ty =
             let pats = List.map pats ~f:(Pattern.subst_sort maps) in
             let defs =
               let is_pure1s, is_fun1s, next1s, sort1s, cont1s = defs in
               let sort1s = List.map sort1s ~f:(Term.subst_sort maps) in
               let cont1s = List.map cont1s ~f:(Term.subst_cont maps) in
               let c1s =
                 List.map2_exn sort1s cont1s ~f:(fun val_type cont_eff ->
                     Sort.
                       {
                         op_sig = Sort.empty_closed_opsig (*dummy*);
                         val_type;
                         cont_eff;
                       })
               in
               (is_pure1s, is_fun1s, next1s, c1s)
             in
             let cont2 = Term.subst_cont maps cont2 in
             (* *)
             Debug.print
             @@ lazy (sprintf "[rcaml:let_and] %s\n" @@ str_of_comp ~config ty);
             let opsig = `Refined ty.op_sig in
             let ( cs,
                   renv_bound,
                   _adm_pvars (*ToDo*),
                   constrs,
                   kind_map,
                   renv_body,
                   map ) =
               let is_top_level = false in
               cgen_let ~config mode ~is_top_level ~opsig fenv dtenv is_rec pats
                 defs kind_map maps renv
             in
             let ty = rename_comp ~config map ty in
             let is_impure_pure =
               List.exists (Quadruple.fth defs) ~f:(fun c ->
                   Fn.non Sort.is_pure c.cont_eff)
               && Sort.is_pure cont2
             in
             let c_body =
               let dom = Env.dep_args_of renv_body in
               comp_of_val ~config ~temp:true ~opsig ~cont:cont2 dom
               @@
               if is_impure_pure then
                 val_of_sort ~config ~refine:true dom @@ sort_of_comp ty
               else ty.val_type
             in
             let rev_comp_effs =
               (Pattern.PAny (sort_of_comp c_body), renv_body, c_body)
               :: (List.rev
                  @@ List.map2_exn pats cs ~f:(fun pat c ->
                         (pat, renv_bound, c)))
             in
             let constrs2, kind_map = next2 kind_map maps renv_body c_body in
             ( Set.Poly.union_list
               @@ [
                    (if is_impure_pure then
                       cgen_subtype_val ~config renv_body c_body.val_type
                         ty.val_type
                     else Set.Poly.empty);
                    constrs;
                    cgen_subeff ~config renv rev_comp_effs ty.val_type ty;
                    constrs2;
                  ],
               kind_map )

           method f_sequence (next1, sort1, cont1) (next2, cont2) kind_map maps
               renv ty =
             let sort1 = Term.subst_sort maps sort1 in
             let cont1 = Term.subst_cont maps cont1 in
             let cont2 = Term.subst_cont maps cont2 in
             (* *)
             Debug.print
             @@ lazy (sprintf "[rcaml:sequence] %s\n" @@ str_of_comp ~config ty);
             let dom = Env.dep_args_of renv in
             let temp = true in
             let opsig = `Refined ty.op_sig in
             let c1 =
               comp_of_val ~config ~temp ~opsig ~cont:cont1 dom
               @@ simple_val_of_sort ~config sort1
             in
             let c2 =
               comp_of_val ~config ~temp ~opsig ~cont:cont2 dom ty.val_type
             in
             let rev_comp_effs =
               [
                 (Pattern.PAny (sort_of_comp c2), renv, c2);
                 (Pattern.PAny sort1, renv, c1);
               ]
             in
             let constrs1, kind_map = next1 kind_map maps renv c1 in
             let constrs2, kind_map = next2 kind_map maps renv c2 in
             ( Set.Poly.union_list
               @@ [
                    cgen_subeff ~config renv rev_comp_effs ty.val_type ty;
                    constrs1;
                    constrs2;
                  ],
               kind_map )

           method f_shift0 (x_opt, sort) (next2, c2) kind_map maps renv ty =
             let sort = Term.subst_sort maps sort in
             let c2 = Term.subst_triple maps c2 in
             (* *)
             Debug.print
             @@ lazy (sprintf "[rcaml:shift0] %s\n" @@ str_of_comp ~config ty);
             match sort with
             | Sort.SArrow (sort_t, c1) ->
                 let t =
                   val_of_sort ~config (Env.dep_args_of renv) ~refine:true
                     sort_t
                 in
                 let y = mk_fresh_tvar_with "y" in
                 let c1 =
                   let renv1 =
                     Env.set_ty (*assume y is not bound by renv*) renv y t
                   in
                   let refine, dom = (true, Env.dep_args_of renv1) in
                   let temp, opsig, cont =
                     (true, `Sort c1.op_sig, c1.cont_eff)
                   in
                   comp_of_sort ~config ~refine ~temp ~opsig ~cont dom
                     c1.val_type
                 in
                 let c2 =
                   let refine, dom = (true, Env.dep_args_of renv) in
                   let temp, opsig, cont =
                     (true, `Sort c2.op_sig, c2.cont_eff)
                   in
                   comp_of_sort ~config ~refine ~temp ~opsig ~cont dom
                     c2.val_type
                 in
                 let rty =
                   {
                     op_sig = (ALMap.empty, None);
                     val_type = t;
                     temp_eff = mk_temp_val ();
                     cont_eff = Eff (y, c1, c2);
                   }
                 in
                 let renv2 =
                   match x_opt with
                   | None -> renv
                   | Some x ->
                       Env.set_ty (*assume x is not bound by renv*) renv x
                         (mk_rarrow y t c1 @@ mk_fresh_trivial_pred ())
                 in
                 let constrs2, kind_map = next2 kind_map maps renv2 c2 in
                 ( Set.Poly.union_list
                     [ cgen_subtype_comp ~config renv rty ty; constrs2 ],
                   kind_map )
             | _ -> failwith "f_shift0"

           method f_reset (next1, sort1) kind_map maps renv ty =
             let sort1 = Term.subst_sort maps sort1 in
             (* *)
             Debug.print
             @@ lazy (sprintf "[rcaml:reset] %s\n" @@ str_of_comp ~config ty);
             let c1 =
               (*ToDo:refactor*)
               let refine, dom = (true, Env.dep_args_of renv) in
               let t1 = val_of_sort ~config ~refine dom sort1 in
               {
                 op_sig = (ALMap.empty, None);
                 val_type = t1;
                 temp_eff =
                   (if (*ToDo*) config.Rtype.enable_temp_eff then
                      mk_temp_fresh ~config dom
                    else mk_temp_val ());
                 cont_eff =
                   (let x = mk_fresh_tvar_with "x" in
                    Eff
                      ( x,
                        comp_of_term ~config
                          (Term.mk_var x @@ sort_of_val t1)
                          t1,
                        ty ));
               }
             in
             next1 kind_map maps renv c1

           method f_perform attrs name sort_op_applied nexts_either kind_map
               maps renv ty =
             let sort_op_applied = Term.subst_sort maps sort_op_applied in
             let nexts_either =
               List.map nexts_either ~f:(subst_all_either maps)
             in
             (* *)
             Debug.print
             @@ lazy (sprintf "[rcaml:perform] %s\n" @@ str_of_comp ~config ty);
             let res, constrs, kind_map =
               let opsig = `Refined ty.op_sig in
               List.fold_right nexts_either ~init:([], Set.Poly.empty, kind_map)
                 ~f:(fun next (res, constrs1, kind_map) ->
                   let r, (constrs2, kind_map) =
                     cgen_either ~config kind_map renv maps opsig next
                   in
                   (r :: res, Set.union constrs1 constrs2, kind_map))
             in
             let c_args = List.map res ~f:snd3 in
             (*Debug.print @@ lazy ("c_args: " ^ String.concat_map_list ~sep:", " ~f:(Rtype.str_of_comp ~config) c_args);*)
             let t_args = List.map c_args ~f:(fun c -> c.val_type) in
             let x_args =
               List.map c_args ~f:(fun _ -> mk_fresh_tvar_with "x" (* dummy *))
             in

             let dom = Env.dep_args_of renv in
             let dom' =
               dom
               @ List.map2_exn x_args t_args ~f:(fun x t ->
                     (Term.mk_var x (sort_of_val t), sort_of_val t))
             in
             let ren =
               Map.Poly.of_alist_exn
               @@ List.zip_exn x_args (List.map ~f:fst3 res)
             in
             let t_op_applied, c_pfm, t_pfm =
               match sort_op_applied with
               | Sort.SArrow (Sort.SArrow (sort, cret1), cret2) ->
                   let x = Ident.mk_fresh_tvar () in
                   let y = Ident.mk_fresh_tvar () in
                   let t_y = val_of_sort ~config ~refine:true dom' sort in
                   let c1 =
                     let refine, dom =
                       (true, dom' @ [ (Term.mk_var y sort, sort) ])
                     in
                     let temp, opsig, cont =
                       (true (*ToDo*), `Sort cret1.op_sig, cret1.cont_eff)
                     in
                     comp_of_sort ~config ~refine ~temp ~opsig ~cont dom
                       cret1.val_type
                   in
                   let c2 =
                     let sort = Sort.mk_arrow sort cret1.val_type in
                     let refine, dom =
                       (true, dom' @ [ (Term.mk_var x sort, sort) ])
                     in
                     let temp, opsig, cont =
                       (true (*ToDo*), `Sort cret2.op_sig, cret2.cont_eff)
                     in
                     comp_of_sort ~config ~refine ~temp ~opsig ~cont dom
                       cret2.val_type
                   in
                   ( mk_rarrow x
                       (mk_rarrow y t_y c1 (mk_fresh_trivial_pred ()))
                       c2 (mk_fresh_trivial_pred ()),
                     {
                       op_sig = ty.op_sig;
                       val_type = rename_val ~config ren t_y;
                       temp_eff = mk_temp_val ();
                       cont_eff = rename_cont ~config ren @@ Eff (y, c1, c2);
                     },
                     rename_val ~config ren t_y )
               | _ -> assert false
             in
             (*Debug.print @@ lazy ("t_op_applied: " ^ Rtype.str_of_val ~config t_op_applied);
               Debug.print @@ lazy ("c_pfm: " ^ Rtype.str_of_comp ~config c_pfm);*)
             let _ (*ToDo*), _ (*ToDo*), t_op =
               let temp, opsig, cont =
                 ( true,
                   `Refined (ALMap.empty (*ToDo*), None (*ToDo*)),
                   None (*ToDo*) )
               in
               of_args_ret ~config ~temp ~opsig ~cont dom x_args t_args
                 t_op_applied
             in

             let t_op_o = ALMap.find_exn name (fst ty.op_sig) in

             (*Debug.print @@ lazy ("t_op: " ^ Rtype.str_of_val ~config t_op);
               Debug.print @@ lazy ("t_op_o: " ^ Rtype.str_of_val ~config t_op_o);*)
             let t_op_annot_opt =
               match
                 MBcgen.find_val_attrs ~config ~renv ~dtenv
                   ~attr_name:"annot_arm" attrs
               with
               | Some ty ->
                   Debug.print
                   @@ lazy
                        (sprintf "[rcaml:perform] annot local: %s\n"
                        @@ str_of_val ~config ty);
                   Some ty
               | None -> (
                   match Env.look_up renv @@ Tvar (name ^ "_arm") with
                   | Some ty ->
                       Debug.print
                       @@ lazy
                            (sprintf "[rcaml:perform] annot global: %s\n"
                            @@ str_of_val ~config ty);
                       Some ty
                   | None -> None)
             in
             let constr_o =
               match t_op_annot_opt with
               | Some t_op_annot ->
                   Set.Poly.union_list
                     [
                       (* ? *)
                       cgen_subtype_val ~config renv t_op_o t_op_annot;
                       cgen_subtype_val ~config renv t_op_annot t_op;
                     ]
               | None -> cgen_subtype_val ~config renv t_op_o t_op
             in

             let renv' =
               List.fold res ~init:renv ~f:(fun renv (x, c, is_bound) ->
                   if is_bound then renv else Env.set_ty renv x c.val_type)
             in
             let rev_comp_effs =
               List.map ~f:(fun c -> (Pattern.PAny (sort_of_comp c), renv', c))
               @@ (c_pfm :: (*ToDo:List.rev*) c_args)
             in
             ( Set.Poly.union_list
               @@ [
                    constr_o;
                    cgen_subtype_val ~config renv' t_pfm ty.val_type;
                    cgen_subeff ~config renv' rev_comp_effs t_pfm ty;
                    constrs;
                  ],
               kind_map )

           method f_handling (next_b, c_b) (next_r, xr, c_r) op_names nexts
               clauses kind_map maps renv ty =
             let c_b = Term.subst_triple maps c_b in
             let c_r = Term.subst_triple maps c_r in
             let clauses =
               List.map clauses ~f:(fun (x_args, sort_args, k_opt, sort_k, c) ->
                   let sort_args =
                     List.map ~f:(Term.subst_sort maps) sort_args
                   in
                   let sort_k = Term.subst_sort maps sort_k in
                   (x_args, sort_args, k_opt, sort_k, Term.subst_triple maps c))
             in
             (* *)
             Debug.print
             @@ lazy (sprintf "[rcaml:handling] %s\n" @@ str_of_comp ~config ty);
             let dom = Env.dep_args_of renv in

             let t_b = val_of_sort ~config ~refine:true dom c_b.val_type in

             let renv_r = Env.set_ty renv xr t_b in
             let c_r =
               let refine, dom_r = (true, Env.dep_args_of renv_r) in
               let temp, opsig, cont = (true, `Sort c_r.op_sig, c_r.cont_eff) in
               comp_of_sort ~config ~refine ~temp ~opsig ~cont dom_r
                 c_r.val_type
             in
             let constr_r, kind_map = next_r kind_map maps renv_r c_r in

             let (constrs, kind_map), t_ops =
               List.fold_right2_exn nexts clauses
                 ~init:((Set.Poly.empty, kind_map), [])
                 ~f:(fun
                     next
                     (x_args, sort_args, k_opt, sort_k, c0)
                     ((constrs, kind_map), t_ops)
                   ->
                   let t_args =
                     List.map sort_args
                       ~f:(val_of_sort ~config ~refine:true dom)
                   in
                   let renv' =
                     List.fold2_exn x_args t_args ~init:renv ~f:Env.set_ty
                   in

                   let t_k =
                     val_of_sort ~config ~refine:true (Env.dep_args_of renv')
                       sort_k
                   in
                   let renv'', k =
                     match k_opt with
                     | Some k -> (Env.set_ty renv' k t_k, k)
                     | None ->
                         (renv', mk_fresh_tvar ~prefix:(Some "k") () (*dummy*))
                   in

                   let c =
                     let refine, dom = (true, Env.dep_args_of renv'') in
                     let temp, opsig = (true, `Sort c0.op_sig) in
                     comp_of_sort ~config ~refine ~temp ~opsig ~cont:c0.cont_eff
                       dom c0.val_type
                   in

                   let constrs', kind_map = next kind_map maps renv'' c in
                   ( (Set.union constrs constrs', kind_map),
                     let temp, opsig, cont =
                       (false, `Refined (ALMap.empty, None), None)
                     in
                     (* ToDo *)
                     (trd3
                     @@ of_args_ret ~config ~temp ~opsig ~cont [] x_args t_args
                     @@ mk_rarrow k t_k c @@ mk_fresh_trivial_pred ())
                     :: t_ops ))
             in

             let constr_b, kind_map =
               let c_b =
                 {
                   op_sig =
                     (ALMap.of_alist_exn @@ List.zip_exn op_names t_ops, None);
                   val_type = t_b;
                   temp_eff =
                     (if config.Rtype.enable_temp_eff then
                        mk_temp_fresh ~config dom
                      else mk_temp_val ());
                   cont_eff = Eff (xr, c_r, ty);
                 }
               in
               next_b kind_map maps renv c_b
             in

             (Set.Poly.union_list [ constr_b; constr_r; constrs ], kind_map)
        end)

  (** Refinement Type Optimization *)

  let cgen_dir_map ~is_up t =
    let open Rtype in
    let rec inner (d : Assertion.direction) = function
      | (RTuple (_, (_, phi)) | RGeneral (_, _, (_, phi)))
        when Formula.is_atom phi ->
          let atm, _ = Formula.let_atom phi in
          if Atom.is_pvar_app atm then
            let pvar, _, _, _ = Atom.let_pvar_app atm in
            Map.Poly.singleton (pvar_to_tvar pvar) d
          else Map.Poly.empty
      | RArrow (_, t, c, _ (*ToDo*)) ->
          Map.force_merge
            (inner (CHCOpt.Problem.reverse_direction d) t)
            (inner d c.val_type (*ToDo*))
      | _ -> Map.Poly.empty
    in
    if is_up then inner Assertion.DUp t else inner Assertion.DDown t

  let cgen_fronts ~config ~is_up ?(renv = Rtype.Env.mk_empty ()) t :
      Assertion.fronts =
    let open Rtype in
    let rec inner d (constrs, phi) = function
      | RTuple (_, (_, phi1)) | RRef (_, (_, phi1)) | RGeneral (_, _, (_, phi1))
        ->
          if Formula.is_atom phi then
            let atm, _ = Formula.let_atom phi1 in
            if Atom.is_pvar_app atm then
              let pvar, _, ts, _ = Atom.let_pvar_app atm in
              let phi = Logic.ExtTerm.of_old_formula phi in
              let args =
                List.map ts ~f:(fun t ->
                    let (v, sort), _ = Term.let_var t in
                    (v, Logic.ExtTerm.of_old_sort sort))
              in
              Map.Poly.singleton (pvar_to_tvar pvar)
                (Logic.ExtTerm.mk_lambda args phi)
            else Map.Poly.empty
          else Map.Poly.empty
      | RArrow (x, t, c, _ (*ToDo*)) -> (
          match t with
          | RGeneral (_, _, (_, phi1)) when Formula.is_atom phi1 ->
              let atm, _ = Formula.let_atom phi1 in
              if Atom.is_pvar_app atm then
                let pvar, sorts, ts, _ = Atom.let_pvar_app atm in
                let pvar' =
                  tvar_to_pvar
                  @@ CHCOpt.Problem.direction_tvar d
                  @@ pvar_to_tvar pvar
                in
                let ts =
                  match List.rev ts with
                  | _ :: tl -> List.rev @@ (Term.mk_var x (sort_of_val t) :: tl)
                  | [] -> assert false
                in
                Map.force_merge
                  (inner d (constrs, phi) t)
                  (inner d
                     ( constrs,
                       Formula.mk_and phi @@ Formula.mk_atom
                       @@ Atom.mk_pvar_app pvar' sorts ts )
                     c.val_type (*ToDo*))
              else Map.Poly.empty
          | _ ->
              Map.force_merge
                (inner (CHCOpt.Problem.reverse_direction d) (constrs, phi) t)
                (inner d (constrs, phi) c.val_type (*ToDo*)))
      | RForall _ | RPoly _ -> assert false
    in
    inner
      (if is_up then Assertion.DUp else Assertion.DDown)
      (constr_of ~config renv) t

  (** Constraint Generation *)

  let sel_of dtenv datatypes cons i (ct : core_type) =
    let sel_name = Datatype.mk_name_of_sel cons.cd_name.txt i in
    match ct.ctyp_desc with
    | Ttyp_constr (ret_name, _, arg_cts) -> (
        List.find datatypes
          ~f:(Datatype.name_of_dt >> String.( = ) @@ Path.name ret_name)
        |> function
        | Some dt ->
            Datatype.mk_insel sel_name (Datatype.name_of_dt dt)
            @@ List.map arg_cts ~f:(MBcgen.sort_of_core_type dtenv)
        | None ->
            Datatype.mk_sel sel_name
            @@ MBcgen.sort_of_core_type ~rectyps:(Some datatypes) dtenv ct)
    | _ ->
        Datatype.mk_sel sel_name
        @@ MBcgen.sort_of_core_type ~rectyps:(Some datatypes) dtenv ct

  let cons_of dtenv datatypes (cons : Typedtree.constructor_declaration) =
    match cons.cd_args with
    | Cstr_tuple cts ->
        let sels = List.mapi cts ~f:(sel_of dtenv datatypes cons) in
        let cons = Datatype.mk_cons cons.cd_name.txt ~sels in
        Debug.print @@ lazy ("[cons_of] " ^ Datatype.str_of_cons cons);
        cons
    | Cstr_record _ ->
        failwith
          "[cons_of] Cstr_record is not supported as an argument of a \
           constructor"

  let _ = Compmisc.init_path ()

  let print_load_info str =
    Debug.print
    @@ lazy
         (sprintf "==================== processing %s ====================" str)

  let of_struct_item ~config (envs : envs) item =
    match item.str_desc with
    | Tstr_eval (_expr, _) -> failwith "expression not supported"
    | Tstr_value (is_rec, vbs) -> (
        let is_rec =
          let defs =
            String.concat_map_list ~sep:" and " vbs ~f:(fun vb ->
                Pattern.str_of @@ MBcgen.pattern_of envs.dtenv vb.vb_pat)
          in
          match is_rec with
          | Recursive ->
              print_load_info @@ "let rec " ^ defs;
              true
          | Nonrecursive ->
              print_load_info @@ "let " ^ defs;
              false
        in
        let is_pures, is_funs, pats, defs =
          List.unzip4
          @@ List.map vbs ~f:(fun vb ->
                 let pat = MBcgen.pattern_of envs.dtenv vb.vb_pat in
                 let t_annot_MB_opt =
                   MBcgen.find_val_attrs ~config ~renv:envs.renv
                     ~dtenv:envs.dtenv ~attr_name:"annot_MB" vb.vb_attributes
                 in
                 let t_annot_opt =
                   MBcgen.find_val_attrs ~config ~renv:envs.renv
                     ~dtenv:envs.dtenv ~attr_name:"annot" vb.vb_attributes
                 in
                 if
                   List.exists vb.vb_attributes ~f:(fun at ->
                       String.(at.attr_name.txt = "annot_rty"))
                   || Option.is_some t_annot_opt
                 then
                   failwith
                     "rtype annotations on let-bindings are not supported";
                 (*ToDo*)
                 let sort =
                   match (t_annot_MB_opt, t_annot_opt) with
                   | Some t, _ | None, Some t -> Rtype.sort_of_val t
                   | None, None ->
                       MBcgen.sort_of_expr ~lift:true envs.dtenv vb.vb_expr
                 in
                 ( MBcgen.is_pure vb.vb_expr.exp_desc,
                   MBcgen.is_fun vb.vb_expr.exp_desc,
                   pat,
                   ( Pattern.senv_of pat sort,
                     vb.vb_expr,
                     Sort.
                       {
                         op_sig = Sort.mk_fresh_empty_open_opsig ();
                         val_type = sort;
                         cont_eff = Sort.mk_fresh_evar ();
                       } ) ))
        in
        let maps, next1s =
          let senv = Rtype.Env.to_sort_env envs.renv in
          let senv_bounds =
            if is_rec then
              let pat_senvs = List.map defs (* assume distinct *) ~f:fst3 in
              Map.update_with_list (*shadowing*) @@ (senv :: pat_senvs)
            else senv
          in
          let eff_constrss, opsig_constrss, next1s =
            List.unzip3
            @@ List.map defs ~f:(fun (_, expr, c) ->
                   cgen_expr ~config envs.mode envs.fenv envs.dtenv senv_bounds
                     expr c)
          in
          let omap, smap, emap =
            let eff_constrs = Set.Poly.union_list eff_constrss in
            let opsig_constrs = Set.Poly.union_list opsig_constrss in
            Debug.print (lazy "==== MB type template:");
            List.iter2_exn pats defs ~f:(fun pat (_, _, c) ->
                Debug.print
                @@ lazy (Pattern.str_of pat ^ ": " ^ Term.str_of_triple c));
            Map.Poly.iteri senv_bounds ~f:(fun ~key ~data ->
                Debug.print
                @@ lazy (Ident.name_of_tvar key ^ ": " ^ Term.str_of_sort data));
            Debug.print (lazy "==== constraints on control effects:");
            Set.iter eff_constrs ~f:(fun (effs, eff) ->
                Debug.print
                @@ lazy
                     (sprintf "%s <: %s"
                        (String.concat_map_list ~sep:" " effs
                           ~f:Term.str_of_cont)
                        (Term.str_of_cont eff)));
            Debug.print (lazy "==== constraints on operation signatures:");
            Set.iter opsig_constrs ~f:(fun (o1, o2) ->
                Debug.print
                @@ lazy (Term.str_of_opsig o1 ^ " <: " ^ Term.str_of_opsig o2));
            let sol = MBcsol.solve eff_constrs opsig_constrs in
            (sol.otheta, Map.force_merge !MBcgen.ref_id sol.stheta, sol.etheta)
          in
          let emap' =
            Map.Poly.map ~f:(Term.subst_conts_cont emap)
            @@ Map.Poly.map ~f:(Term.subst_sorts_cont smap)
            @@ Map.Poly.map ~f:(Term.subst_opsigs_cont omap) emap
          in
          let omap' =
            Map.Poly.map ~f:(Term.subst_conts_opsig emap')
            @@ Map.Poly.map ~f:(Term.subst_sorts_opsig smap)
            @@ Map.Poly.map ~f:(Term.subst_opsigs_opsig omap) omap
          in
          let smap' =
            Map.Poly.map ~f:(Term.subst_conts_sort emap')
            @@ Map.Poly.map ~f:(Term.subst_sorts_sort smap)
            @@ Map.Poly.map ~f:(Term.subst_opsigs_sort omap') smap
          in
          ((omap', smap', emap'), next1s)
        in
        let cs = List.map defs ~f:(trd3 >> Term.subst_triple maps) in
        (* *)
        Debug.print @@ lazy "";
        let ( cs,
              _renv_bound (*ToDo*),
              adm_pvars,
              constrs',
              kind_map,
              renv_body,
              _map (*ToDo*) ) =
          cgen_let ~config envs.mode ~is_top_level:true envs.fenv envs.dtenv
            is_rec pats
            (is_pures, is_funs, next1s, cs)
            envs.kind_map maps envs.renv
        in
        match List.find cs ~f:(Fn.non @@ Rtype.is_pure_comp ~config) with
        | None ->
            Debug.print
            @@ lazy
                 (sprintf "updated renv:\n%s"
                 @@ Rtype.Env.str_of ~config renv_body);
            let exi_senv =
              Set.fold adm_pvars ~init:envs.exi_senv
                ~f:(fun acc (pv, _, arg_sorts) ->
                  let sort = Sort.mk_fun @@ arg_sorts @ [ T_bool.SBool ] in
                  Map.Poly.add_exn acc ~key:(Ident.pvar_to_tvar pv) ~data:sort)
            in
            ( {
                envs with
                constrs = Set.union envs.constrs constrs';
                exi_senv;
                kind_map;
                renv = renv_body;
              },
              Skip )
        | Some c ->
            failwith
            @@ "[of_struct_item] impure top-level computation not supported: "
            ^ Rtype.str_of_comp ~config c)
    | Tstr_primitive vd ->
        print_load_info "external";
        let renv', _ =
          Rtype.Env.update_with ~config envs.renv
          @@ Rtype.Env.singleton_ty (Tvar vd.val_name.txt)
          @@ (if true then fun sort -> Rtype.simple_val_of_sort ~config sort
              else
                Rtype.val_of_sort ~config ~refine:true
                  ~name:(Some (vd.val_name.txt, "", 0))
                  [])
          @@
          let sort =
            MBcgen.sort_of_type_expr envs.dtenv vd.val_desc.ctyp_type
          in
          Sort.mk_poly (Term.svs_of_sort sort) sort
        in
        Debug.print
        @@ lazy (sprintf "updated renv:\n%s" @@ Rtype.Env.str_of ~config renv');
        ({ envs with renv = renv' }, Skip)
    | Tstr_type (_rec_flag (*ToDo*), types) ->
        print_load_info "type";
        let dttypes, ustypes =
          List.partition_tf types ~f:(fun ty ->
              Debug.print
              @@ lazy
                   (sprintf "[of_struct_item] processing a type declaration: %s"
                      ty.typ_name.txt);
              match ty.typ_kind with
              | Ttype_variant _ ->
                  Debug.print @@ lazy "\t is a variant type";
                  true
              | Ttype_abstract ->
                  Debug.print @@ lazy "\t is an abstract type";
                  false
              | Ttype_open ->
                  failwith "unsupported type_declaration kind: Ttype_open"
              | Ttype_record _ -> (
                  match ty.typ_name.txt with
                  | "effect_handler" | "handler" ->
                      Debug.print @@ lazy "\t is a handler type";
                      true
                  | _ ->
                      failwith "unsupported type_declaration kind: Ttype_record"
                  ))
        in
        let dtenv =
          List.fold_left ustypes ~init:envs.dtenv ~f:(fun dtenv ty ->
              DTEnv.update_dt dtenv
              @@
              match ty.typ_manifest with
              | Some core_type ->
                  Datatype.mk_alias ty.typ_name.txt
                  @@ MBcgen.sort_of_core_type dtenv core_type
              | None -> Datatype.mk_uninterpreted_datatype ty.typ_name.txt)
        in
        let dts =
          let datatypes =
            List.map dttypes ~f:(fun t ->
                Datatype.mk_dt t.typ_name.txt
                @@ List.map t.typ_params
                     ~f:(fst >> MBcgen.sort_of_core_type dtenv))
          in
          let datatypes =
            List.map2_exn datatypes dttypes ~f:(fun dt ty ->
                match ty.typ_kind with
                | Ttype_variant tds ->
                    {
                      dt with
                      conses = List.map tds ~f:(cons_of dtenv datatypes);
                    }
                | Ttype_abstract ->
                    failwith "unsupported type_declaration kind: Ttype_abstract"
                | Ttype_open ->
                    failwith "unsupported type_declaration kind: Ttype_open"
                | Ttype_record _ -> dt
                (*ToDo: empty definition*)
                (*failwith "unsupported type_declaration kind: Ttype_record"*))
          in
          List.map datatypes ~f:(fun dt ->
              Datatype.make (Datatype.name_of_dt dt) datatypes Datatype.FDt)
        in
        let dtenv' = List.fold_left dts ~init:dtenv ~f:DTEnv.update_dt in
        Debug.print
        @@ lazy
             (sprintf "[of_struct_item] datatype env:\n%s"
             @@ DTEnv.str_of dtenv');
        update_dtenv dtenv';
        update_dtrenv_with_dts ~config dts;
        ({ envs with dtenv = dtenv' }, Skip)
    | Tstr_typext _ -> failwith "type extension not supported"
    | Tstr_exception _ -> failwith "exception not supported"
    | Tstr_module _ -> failwith "module not supported"
    | Tstr_recmodule _ -> failwith "recursive module not supported"
    | Tstr_modtype _ -> failwith "module type not supported"
    | Tstr_open _ -> failwith "open not supported"
    | Tstr_class _ -> failwith "class not supported"
    | Tstr_class_type _ -> failwith "class type not supported"
    | Tstr_include _ -> failwith "include not supported"
    | Tstr_attribute attr -> (
        print_load_info "attribute";
        let content =
          match attr.Parsetree.attr_payload with
          | Parsetree.PStr ps -> (
              (*Debug.print @@ lazy
                 (sprintf "parse structure:\n%s" (str_of_parse_structure ps));*)
              let ts, _, _, _, _ =
                Typemod.type_structure (Compmisc.initial_env ()) ps
              in
              (*Debug.print @@ lazy
                 (sprintf "attr typedtree:%s" (MBcgen.str_of_typedtree_structure ts));*)
              match (List.hd_exn @@ List.rev ts.str_items).str_desc with
              | Tstr_eval (expr, _) -> (
                  match expr.exp_desc with
                  | Texp_constant (Const_string (str, _, _)) -> str
                  | Texp_constant (Const_int _) -> failwith "Const_int"
                  | Texp_constant (Const_char _) -> failwith "Const_char"
                  | Texp_constant (Const_float _) -> failwith "Const_float"
                  | Texp_constant (Const_int32 _) -> failwith "Const_int32"
                  | Texp_constant (Const_int64 _) -> failwith "Const_int64"
                  | Texp_constant (Const_nativeint _) ->
                      failwith "Const_nativeint"
                  | _ -> failwith "Tstr_eval")
              | _ -> failwith "unsupported")
          | _ -> failwith "unsupported"
        in
        match attr.Parsetree.attr_name.txt with
        | "mode" ->
            Debug.print @@ lazy ("[mode] " ^ content);
            ( {
                envs with
                mode =
                  (match content with
                  | "hfl_prop_as_expectation" -> HFL_Expectation false
                  | "hfl_prop_as_conditional_expectation" ->
                      HFL_Expectation true
                  | _ -> OCaml);
              },
              Skip )
        | "smtlib2" ->
            (* e.g., [@@@smtlib2 "some smtlib2 code"] *)
            let constrs', envs' (*ToDo: uni_senv is ignored*) =
              SMT.Smtlib2.from_string ~print:Debug.print ~inline:false (*ToDo*)
                ~exi_senv:envs.exi_senv ~kind_map:envs.kind_map ~fenv:envs.fenv
                ~dtenv:envs.dtenv content
            in
            let constrs' =
              Set.Poly.map ~f:(Typeinf.typeinf_formula ~print:Debug.print)
              @@ Set.Poly.of_list constrs'
            in
            update_fenv envs'.fenv;
            update_dtenv envs'.dtenv;
            (*ToDo: also update dtrenv with dtenv'*)
            ( {
                envs with
                constrs = Set.union envs.constrs constrs';
                exi_senv = envs'.exi_senv;
                kind_map = envs'.kind_map;
                fenv = envs'.fenv;
                dtenv = envs'.dtenv;
              },
              Skip )
        | "constraints" ->
            let constrs' =
              Rtype.cgen_config := config;
              Rtype.renv_ref := envs.renv;
              set_dtenv envs.dtenv;
              Set.Poly.map ~f:(Typeinf.typeinf_formula ~print:Debug.print)
              @@ Set.Poly.of_list
              @@ RtypeParser.constraints RtypeLexer.token
              @@ Lexing.from_string content
            in
            ({ envs with constrs = Set.union envs.constrs constrs' }, Skip)
        | "rtype" ->
            (* e.g. [@@@rtype "main :: (x:{v : int | v > 0}) -> unit"] *)
            let renv0 =
              Rtype.cgen_config := config;
              Rtype.renv_ref := envs.renv;
              set_dtenv envs.dtenv;
              RtypeParser.val_ty_env RtypeLexer.token
              @@ Lexing.from_string content
            in
            Debug.print @@ lazy ("[rtype] " ^ Rtype.Env.str_of ~config renv0);
            let renv_cons, renv_vars =
              Map.Poly.partitioni_tf (fst renv0)
                ~f:(fun ~key:(Ident.Tvar name) ~data:_ ->
                  DTEnv.name_is_func envs.dtenv name)
            in
            let renv_cons =
              Map.rename_keys_and_drop_unused
                ~f:(name_of_tvar >> Option.return)
                renv_cons
            in
            let renv' = Rtype.Env.set_with envs.renv (renv_vars, snd renv0) in
            update_dtrenv_with_renv renv_cons;
            ({ envs with renv = renv' }, Skip)
        | "check" | "assert" ->
            (* e.g., [@@@assert "type_of(main) <: int -> unit "] *)
            Debug.print @@ lazy ("[check] " ^ content);
            let assertions =
              Rtype.cgen_config := config;
              Rtype.renv_ref := envs.renv;
              set_dtenv envs.dtenv;
              RtypeParser.assertions RtypeLexer.token
              @@ Lexing.from_string content
            in
            (envs, Check assertions)
        | "infer" | "optimize" | "infer_optimized_type" ->
            Debug.print @@ lazy ("[infer] " ^ content);
            let problems =
              Rtype.cgen_config := config;
              Rtype.renv_ref := envs.renv;
              set_dtenv envs.dtenv;
              RtypeParser.opt_problems RtypeLexer.token
              @@ Lexing.from_string content
            in
            (envs, Infer problems)
        | name ->
            Debug.print @@ lazy ("unknown annotation: " ^ name);
            (envs, Skip))

  let rec top_level_aux ~config envs = function
    | [] ->
        Debug.print
        @@ lazy
             "======================== Constraints Generated \
              ========================";
        []
    | item :: tl -> (
        match of_struct_item ~config envs item with
        | envs, Skip -> top_level_aux ~config envs tl
        | envs, Check asserts ->
            List.map asserts ~f:(function
              | tvar, Assertion.Type rty ->
                  let rty_def, constrs_def, kind_map_def =
                    match Rtype.Env.look_up envs.renv tvar with
                    | Some rty_def ->
                        let dom = Rtype.Env.dep_args_of envs.renv in
                        Rtype.instantiate_val ~print:Debug.print ~config dom
                          envs.kind_map
                          (Map.Poly.empty, Map.Poly.empty)
                          (rty_def, Rtype.sort_of_val rty)
                    | None ->
                        failwith @@ Ident.name_of_tvar tvar ^ " not defined"
                  in
                  let envs =
                    {
                      envs with
                      kind_map = Map.force_merge envs.kind_map kind_map_def;
                    }
                  in
                  let pcsp =
                    pcsp_of envs @@ Set.union constrs_def
                    @@ cgen_subtype_val ~config envs.renv rty_def rty
                  in
                  Debug.print @@ lazy "\n*** constraints generated:\n";
                  ( sprintf "type_of(%s) <: %s" (name_of_tvar tvar)
                      (Rtype.str_of_val ~config rty),
                    Problem.PAssertion (!mu_preds, !nu_preds, pcsp) )
              | tvar, Assertion.FinEff eff ->
                  Debug.print
                  @@ lazy
                       (sprintf "fin_eff_of(%s) <: %s" (name_of_tvar tvar)
                          (Grammar.RegWordExp.str_of Fn.id eff));
                  assert false
              | tvar, Assertion.InfEff eff ->
                  Debug.print
                  @@ lazy
                       (sprintf "inf_eff_of(%s) <: %s" (name_of_tvar tvar)
                          (Grammar.RegWordExp.str_of Fn.id eff));
                  assert false)
            @ top_level_aux ~config envs tl
        | envs, Infer objs ->
            let dir_maps, _frontss, priorities, constrss, space_constrss =
              List.unzip5
              @@ List.map objs ~f:(fun (tvar, sorted_dir_map, space_constrs) ->
                     let rty = Rtype.Env.look_up_exn envs.renv tvar in
                     Debug.print_log ~tag:"cgen_dir_map/fronts/prior"
                     @@ lazy (Rtype.str_of_val ~config rty);
                     let dir_map =
                       if List.is_empty sorted_dir_map then
                         cgen_dir_map ~is_up:false rty
                       else Map.Poly.of_alist_exn sorted_dir_map
                     in
                     let _rty_def, constr, _kind_map (*ToDo*) =
                       match Rtype.Env.look_up envs.renv tvar with
                       | Some rty_def ->
                           let dom = Rtype.Env.dep_args_of envs.renv in
                           Rtype.instantiate_val ~print:Debug.print ~config dom
                             envs.kind_map
                             (Map.Poly.empty, Map.Poly.empty)
                             (rty_def, Rtype.sort_of_val rty)
                       | None ->
                           failwith @@ Ident.name_of_tvar tvar
                           ^ " not defined" (*Set.Poly.empty*)
                     in
                     let fronts =
                       cgen_fronts ~renv:envs.renv ~is_up:false rty
                     in
                     let priority =
                       if List.is_empty sorted_dir_map then
                         CHCOpt.Problem.topological_sort (Map.Poly.keys dir_map)
                           []
                       else List.map sorted_dir_map ~f:fst
                     in
                     (dir_map, fronts, priority, [ constr ], space_constrs))
            in
            let dir_map = Map.force_merge_list dir_maps in
            let fronts = Map.Poly.empty in
            (* TODO *)
            let priority = List.concat priorities in
            let sol_space =
              SolSpace.of_space_constrs @@ List.concat space_constrss
            in
            Debug.print_log ~tag:"Generate lexicographic optimization"
            @@ lazy
                 (sprintf "\ndir_map: %s\nprior: %s\nfronts: %s"
                    (CHCOpt.Problem.str_of_dir_map dir_map)
                    (CHCOpt.Problem.str_of_priority priority)
                    (CHCOpt.Problem.str_of_fronts fronts));
            let pcsp =
              pcsp_of ~skolem_pred:true ~sol_space envs
              @@ Set.Poly.union_list @@ List.concat constrss
            in
            ("infer", Problem.POptimization ((dir_map, priority, fronts), pcsp))
            :: top_level_aux ~config envs tl)

  let top_level ~config ps =
    try
      let ts, _, _, _, _ =
        Typemod.type_structure (Compmisc.initial_env ()) ps
      in
      (*Debug.print @@ lazy (sprintf "typedtree structure:\n%s"
                             (MBcgen.str_of_typedtree_structure ts));*)
      init_dtenv ();
      init_fenv ();
      init_dummy_term_senv ();
      mu_preds := Map.Poly.empty;
      nu_preds := Map.Poly.empty;
      inst_pvs_dtrenv := Set.Poly.empty;
      dtrenv := Map.Poly.empty;
      update_dtrenv_with_dts ~config (Map.data @@ get_dtenv ());
      MBcgen.ref_id := Map.Poly.empty;
      Rtype.cgen_config := config;
      Rtype.renv_ref := Rtype.Env.mk_empty ();
      let envs =
        {
          mode = OCaml;
          constrs = Set.Poly.empty;
          exi_senv = Map.Poly.empty;
          kind_map = Map.Poly.empty;
          fenv = get_fenv ();
          dtenv = get_dtenv ();
          renv = !Rtype.renv_ref;
        }
      in
      Result.return @@ top_level_aux ~config envs ts.str_items
    with
    | Typemod.Error (loc, env, err) ->
        failwith @@ "Typemod.Error:\n"
        ^ MBcgen.str_of_stdbuf ~f:Location.print_report
        @@ Typemod.report_error ~loc env err
    | Env.Error err ->
        failwith @@ "Env.Error:" ^ MBcgen.str_of_stdbuf ~f:Env.report_error err
    | Typecore.Error (loc, env, err) ->
        failwith @@ "Typecore.Error:\n"
        ^ MBcgen.str_of_stdbuf ~f:Location.print_report
        @@ Typecore.report_error ~loc env err

  let from_ml_file config =
    In_channel.create >> Lexing.from_channel >> Parse.implementation
    >> top_level ~config
end
