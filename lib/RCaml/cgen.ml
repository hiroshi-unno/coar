(* RCaml's constraint generator: refinement type checking and inference for
   OCaml programs, reduced to predicate constraint satisfaction.

   [from_ml_file] parses and type-checks the source with the OCaml compiler's
   own front end and walks the typed structure item by item ([of_struct_item],
   [top_level_aux]).  Item attributes drive what is produced: [[@@@rtype]]
   declares refinement types (of program variables and of datatype
   constructors), [[@@@constraints]] and [[@@@smtlib2]] add side constraints,
   [[@@@mode]] selects reading Boolean properties as (conditional)
   expectations, [[@@@check]]/[[@@@assert]] yield one [Problem.PAssertion] per
   asserted subtyping [type_of(x) <: ty], [[@@@property]] one for a formula
   about the top-level functions' graphs, [[@@@lemma]] adds claims for MuCyc's
   relational search to prove and use (both in the application notation of
   [formula_of_notation]), and [[@@@infer]]/[[@@@optimize]] yield a
   [Problem.POptimization] for maximally precise refinement types.  Any other
   attribute is named once on stderr and ignored.

   Expressions are traversed by [MBcgen.fold_expr] (simple types and effects,
   solved by [MBcsol]); its callbacks here generate the refinement constraints:
   subtyping ([cgen_subtype_val] and siblings), effect composition, pattern
   matching, and generalisation and instantiation of refinement types.

   Least and greatest fixpoint predicates ([mu_preds], [nu_preds]) are read off
   by [fixpoint], which needs every intermediate predicate variable eliminated:
   the preprocessor below is configured with an unbounded elimination threshold
   for that reason.  Anything here that introduces an intermediate predicate
   per nesting level therefore makes elimination exponential in practice;
   distribute the context over the branches instead (as [MBcgen] does for
   impure [&&]/[||] conditions), and keep continuation closures re-entrant,
   since one may be invoked from several branches.

   Implements the refinement type systems of Unno and Kobayashi (PPDP 2009),
   Unno, Terauchi and Kobayashi (POPL 2013), Hashimoto and Unno (SAS 2015, the
   optimization problems), Nanjo et al. (LICS 2018), Sekiyama and Unno (POPL
   2023, POPL 2025), Kawamata et al. (POPL 2024), Kura and Unno (ICFP 2024,
   the expectation modes) and Kura et al. (ESOP 2026).  Translation state is
   global ([dtrenv], [mu_preds], the [Ast.LogicOld] environments) and reset by
   [top_level], so a translation is not reentrant. *)

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

  module MBcgen = MBcgen.Make (
    struct
      let config =
        MBcgen.Config.
          {
            verbose = config.verbose;
            for_cps_trans = false;
            atp_operations = config.atp_operations;
          }
    end :
      MBcgen.Config.ConfigType)

  module MBcsol = MBcsol.Make (
    struct
      let config = { config.mbcsol with verbose = config.verbose }
    end :
      MBcsol.Config.ConfigType)

  (* How a file is read, chosen by its [[@@@mode]] attribute.
     - [OCaml] (no attribute, or any unknown string): an OCaml program; a
       [let rec] is typed by partial correctness (assume the type, check the
       body).
     - [HFL_Expectation adm]: a lambda-HFL term whose [prop] is the truth-value
       domain [adm] names; a recursive function is a fixed point in that
       domain's order and the refinement of its answer-valued result is
       admissible in that order (kind [Adm adm]).  The instances:
       ["hfl_prop_as_expectation"] ([Adm_expectation]: the non-negative reals,
       least fixed points, upper bounds); ["hfl_prop_as_conditional_expectation"]
       ([Adm_conditional]: pairs, the second component in the opposite order);
       ["hfl_prop_as_probability"] ([Adm_probability]: [0, 1], least fixed
       points, upper bounds); ["hfl_prop_as_liberal_probability"]
       ([Adm_liberal]: [0, 1] in the opposite order, so a recursive function
       is the greatest fixed point in the usual order -- a liberal
       pre-expectation, divergence counted as success -- and its admissible
       refinements are lower bounds).  The two [0, 1] instances are read
       only after [probability_prescan] has refused any term that is not a
       sub-probability term: on such a term every operator maps [0, 1] into
       [0, 1] and is continuous in both orders, so the term is a lambda-HFL
       term of either model, and the typing rules are those of the
       expectation mode with the admissible template of the instance.
     - [HFL_Bool] (["hfl_prop_as_bool"]): a lambda-HFL term whose [prop] is
       [bool]; each recursive binding is a fixed point of the kind its
       [[@@fix "nu"]] or [[@@fix "mu"]] names (greatest when absent), and the
       refinement of its Boolean result is built in the shape
       [theta(args) => v] for a greatest and [v => theta(args)] for a least
       fixed point, which are exactly the refinements admissible in the
       two-valued orders (an admissible set contains the order's bottom: [tt]
       for a greatest fixed point, [ff] for a least), so the partial-correctness
       rule for [let rec] is sound for the fixed point.  A file mixing the two
       kinds (alternation), an existential quantifier inside a greatest fixed
       point or a universal one inside a least ([exists_int]/[forall_int]
       applied in such a body, where the quantifier is not continuous in the
       fixed point's order) is refused by [hfl_prescan].
     The ordinary mode must never read an HFL file: under partial correctness
     a diverging conjunction has every type, while the greatest fixed point of
     the same equation can be false, so [hfl_prescan] refuses any [[@@fix]]
     outside [HFL_Bool]. *)
  type mode = OCaml | HFL_Expectation of Kind.adm | HFL_Bool

  type constr = Formula.t

  type item =
    | Skip
    | Check of (tvar * Rtype.Assertion.kind) list
    | Infer of
        (tvar
        * (tvar * Rtype.Assertion.direction) list (* priority *)
        * (tvar * SolSpace.space_flag * int) list (* solution space *))
        list

  (** Refinement Type Inference *)

  let mu_preds = ref Map.Poly.empty (*ToDo*)
  let nu_preds = ref Map.Poly.empty (*ToDo*)

  (* The copies of the fixpoint definitions an instance of a
     predicate-polymorphic scheme needs (installed as
     [Rtype.instantiate_fixpoint_preds], whose comment states the contract).
     A definition is copied when its body mentions a renamed predicate or a
     definition that is itself copied, so the copied set is the least set
     closed under that rule; each copy's body is the original's with the scheme
     renaming and the copy renaming applied together, so a copy refers to the
     copies of the definitions it uses and to itself, and its kind (least or
     greatest) and arguments are the original's.  Copies are added beside the
     originals, which an earlier instance or the definition's own constraints
     may still name. *)
  let instantiate_fixpoint_preds pmap =
    if Map.Poly.is_empty !mu_preds && Map.Poly.is_empty !nu_preds then
      Map.Poly.empty
    else
      let defs =
        Map.Poly.to_alist !mu_preds @ Map.Poly.to_alist !nu_preds
      in
      let mentions renamed (_, (_, phi)) =
        not @@ Set.is_empty @@ Set.inter renamed @@ Formula.pvs_of phi
      in
      let rec close copied =
        let renamed =
          Set.union (Set.Poly.of_list @@ Map.Poly.keys pmap) copied
        in
        let copied' =
          Set.Poly.of_list @@ List.map ~f:fst
          @@ List.filter defs ~f:(mentions renamed)
        in
        if Set.equal copied copied' then copied else close copied'
      in
      let copied = close Set.Poly.empty in
      if Set.is_empty copied then Map.Poly.empty
      else
        let cmap =
          Map.of_set_exn
          @@ Set.Poly.map copied ~f:(fun pvar ->
              ( pvar,
                Ident.mk_fresh_pvar ()
                  ~prefix:(Some (Ident.name_of_pvar pvar ^ "@")) ))
        in
        let ren = Map.force_merge pmap cmap in
        let copy defs =
          Map.Poly.fold defs ~init:defs ~f:(fun ~key ~data:(env, phi) acc ->
              match Map.Poly.find cmap key with
              | Some key' ->
                  Map.Poly.set acc ~key:key'
                    ~data:(env, Formula.rename_pvars ren phi)
              | None -> acc)
        in
        mu_preds := copy !mu_preds;
        nu_preds := copy !nu_preds;
        cmap

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
        let svs =
          Datatype.svs_of dt
          (* ToDo: does it work for GADTs? *)
        in
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
                      Formula.mk_atom @@ Atom.pvar_app_of_senv pv [ (tv, sort) ]
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

  (* [hide_constructors names] moves the templates of the constructors in
     [names] to keys no constructor can have, so that a declaration whose
     constructors share names with earlier ones ([None] and [Some] of a
     user's [type int_option = None | Some of int] against the built-in
     [option]) gets templates of its own, as OCaml's later constructors hide
     the earlier ones of the same name.  A hidden template stays in the map
     because its predicate variables may already occur in constraints
     generated before the declaration, and the predicate environment
     ([get_penv_dtrenv]) is read from the map's values; it is never found by a
     constructor name again. *)
  let hide_constructors names =
    dtrenv :=
      Map.Poly.fold !dtrenv ~init:Map.Poly.empty ~f:(fun ~key ~data acc ->
          let key =
            if List.mem names key ~equal:String.equal then
              let rec fresh k =
                let key' = sprintf "%s (hidden %d)" key k in
                if Map.Poly.mem !dtrenv key' then fresh (k + 1) else key'
              in
              fresh 1
            else key
          in
          Map.Poly.set acc ~key ~data)

  (* [dts] holds one [Datatype.t] per declared type, a mutually recursive
     group ([type a = ... and b = ...]) giving one per member, each selecting
     its own name and carrying the whole group.  Each member contributes the
     templates of its own constructors only: a sibling's constructor is not
     found in the member selected ([Datatype.sorts_of_cons_name]) and would
     also be generated once per member. *)
  let update_dtrenv_with_dts ~config dts =
    let open Datatype in
    hide_constructors
    @@ List.concat_map dts ~f:(fun datatype ->
        List.map (conses_of datatype) ~f:(fun cons -> cons.name));
    update_dtrenv_with_renv @@ Map.Poly.of_alist_exn
    @@ List.concat_map dts ~f:(fun datatype ->
        List.map (conses_of datatype) ~f:(fun cons ->
            (cons.name, of_constructor ~config cons.name datatype)))

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
                      (* No kind map is threaded here, and none is lost:
                         a negative instantiation replaces the constructor
                         type's predicate parameters by [true] before
                         instantiating, so no kinded unknown is copied, and
                         the fresh refinements it makes for type variables
                         are ordinary. *)
                      let cty, constrs, _kind_map =
                        let cty = Map.Poly.find_exn !dtrenv cons.name in
                        instantiate_val_con false ~config dom Map.Poly.empty
                          (cty, None, ty)
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
                          Set.Poly.singleton @@ Formula.eq x_term t_cons )
                      in
                      let constrs_args, phi_args =
                        constr_of ~config ~depth:(depth - 1) renv_args
                      in
                      ( Set.Poly.union_list [ constrs; constrs_args ],
                        Formula.mk_imply (Formula.eq x_term t_cons) phi_args ))
              in
              Option.return
                ( Set.Poly.union_list css,
                  Formula.and_of (Formula.apply_pred pred x_term :: phis) )
          | RTuple (elems, pred) ->
              let args =
                List.map elems ~f:(fun t -> (mk_fresh_tvar_with "v", t))
              in
              let constrs_elems, phi_elems =
                constr_of ~config ~depth
                  ( Map.Poly.of_alist_exn args,
                    Set.Poly.singleton @@ Formula.eq x_term
                    @@ T_tuple.mk_tuple_cons (List.map elems ~f:sort_of_val)
                    @@ List.map args ~f:(fun (x, t) ->
                        Term.mk_var x @@ sort_of_val t) )
              in
              Option.return
                ( constrs_elems,
                  Formula.and_of [ Formula.apply_pred pred x_term; phi_elems ]
                )
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
             @@ String.concat_map_set ~sep:"\n  " constrs ~f:Formula.str_of);
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
              (String.concat_map_set ~sep:"\n  " constrs ~f:Formula.str_of));
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
               >> Tuple2.uncurry
                  @@ cgen_subtype_val ~first:false ~config ~depth renv)
      else
        failwith
        @@ sprintf "[cgen_subtype_opsig] %s and %s" (str_of_opsig ~config o1)
             (str_of_opsig ~config o2)
    in
    if first then
      Debug.print
      @@ lazy
           (sprintf "[cgen_subtype_opsig] constraints:\n  %s\n"
              (String.concat_map_set ~sep:"\n  " constrs ~f:Formula.str_of));
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
              (String.concat_map_set ~sep:"\n  " constrs ~f:Formula.str_of));
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
            [
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
            [
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
              (String.concat_map_set ~sep:"\n  " constrs ~f:Formula.str_of));
    constrs

  let compose_temp_eff_inv ~config renv ((x1, phi1), (y1, psi1))
      ((x2, phi2), (y2, psi2)) =
    let open Rtype in
    let sub1 =
      Map.Poly.singleton x2
      @@ T_trace.mk_concat ~fin:true
           (Term.mk_var x1 @@ T_trace.STrace true)
           (Term.mk_var x2 @@ T_trace.STrace true)
    in
    let sub2 =
      Map.Poly.singleton y2
      @@ T_trace.mk_concat ~fin:false
           (Term.mk_var x1 @@ T_trace.STrace true)
           (Term.mk_var y2 @@ T_trace.STrace false)
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
          Formula.forall [ (x1, T_trace.STrace true) ]
          @@ Evaluator.simplify @@ Formula.mk_imply phi1
          @@ Formula.subst sub1 phi2 ),
        ( y2,
          Formula.forall [ (x1, T_trace.STrace true) ]
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
        let renv2' =
          Env.set_ty renv2 x2 t2
          (* [t2] can depend on x2 *)
        in
        let constrs, c3 =
          (* [fresh_pred_for_cont_composition] (default): a fresh template
             [c3] for the sequenced computation, related by subtyping; off,
             the effect is composed into [c1] by the inverse composition,
             which adds no predicate variable but is incomplete *)
          if config.Rtype.fresh_pred_for_cont_composition then
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
        compose_cont_eff ~config ((pat2, renv2, t2, First (es1 @ es2)) :: ss)
    | ((_, _, _, Second _) as s1)
      :: (_, _, _, First es1)
      :: (pat2, renv2, t2, First es2)
      :: ss ->
        (*ToDo*)
        compose_cont_eff ~config
          (s1 :: (pat2, renv2, t2, First (es1 @ es2)) :: ss)
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
          compose_cont_eff ~config ((pat2, renv2, t2, Second s) :: ss)
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
          compose_cont_eff ~config (s1 :: (pat2, renv2, t2, Second s) :: ss)
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
            (String.concat_map_set ~sep:"\n  " constrs ~f:Formula.str_of));
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
            (String.concat_map_set ~sep:"\n  " constrs ~f:Formula.str_of));
    constrs

  (** assume [pat] is instantiated to [sort_of_val rty].
      Returns [(pat_renv, outer_phis, constrs, not_matched)].  The types of
      [pat_renv] and the formulas [outer_phis] (the scrutinee's refinements,
      whose dependency arguments are outer variables) are read in the scope
      enclosing the match, and a caller binding the pattern must rename them
      with that scope where the pattern rebinds a name; the formulas of
      [pat_renv] (equations between the scrutinee's parts and the pattern's
      variables) are read in the pattern's scope and must not be renamed.
      [term] is never a variable the pattern binds. *)
  let rec pattern_match_with ~config renv (pat : Pattern.t)
      (term, (rty : Rtype.t)) =
    match (pat, rty) with
    | PAny _, _ ->
        ( Rtype.Env.mk_empty (),
          Set.Poly.empty,
          Set.Poly.empty,
          (* always match *) Formula.mk_false () )
    | PVar (x, _), _ ->
        (*assert Stdlib.(sort = Rtype.sort_of_val rty);*)
        ( Rtype.Env.add_phi (Rtype.Env.singleton_ty x rty)
          @@ Formula.eq term @@ Term.mk_var x @@ Rtype.sort_of_val rty,
          Set.Poly.empty,
          Set.Poly.empty,
          (* always match *) Formula.mk_false () )
    | PTuple pats, RTuple (elems, pred) ->
        let sorts = List.map elems ~f:Rtype.sort_of_val in
        let renvs, outer_phiss, constrss, not_matched, args_targs =
          List.unzip5
          @@ List.mapi (List.zip_exn pats elems) ~f:(fun i (pi, ti) ->
              let arg = Ident.mk_fresh_tvar () in
              let sort = List.nth_exn sorts i in
              let targ = Term.mk_var arg sort in
              let renv, outer_phis, constrs, not_matched =
                pattern_match_with ~config renv pi (targ, ti)
              in
              (* the not-matched condition is used outside this branch, where
                 [arg] is unbound: express it through the projection of the
                 scrutinee instead *)
              let not_matched =
                Formula.subst
                  (Map.Poly.singleton arg (T_tuple.mk_tuple_sel sorts term i))
                  not_matched
              in
              (renv, outer_phis, constrs, not_matched, ((arg, ti), targ)))
        in
        let args, targs = List.unzip args_targs in
        let renv_args =
          ( Map.Poly.of_alist_exn args,
            Set.Poly.singleton @@ Formula.eq term
            @@ T_tuple.mk_tuple_cons sorts targs )
        in
        ( Rtype.Env.disj_union_list (* assume distinct *) (renv_args :: renvs),
          Set.Poly.union_list
          @@ Set.Poly.singleton
               (Formula.apply_pred pred term (*ToDo: redundant?*))
             :: outer_phiss,
          Set.Poly.union_list constrss,
          Formula.or_of
          @@ (Formula.mk_atom @@ T_tuple.mk_is_not_tuple sorts term)
             :: not_matched )
    | PCons (dt, cons_name, pats), RGeneral (_, T_dt.SDT dt', pred)
      when String.(Datatype.name_of dt = Datatype.name_of dt') ->
        (*Debug.print @@ lazy cons_name;*)
        (* No kind map is threaded here, and none is lost: a negative
           instantiation replaces the constructor type's predicate parameters
           by [true] before instantiating, so no kinded unknown is copied. *)
        let ( cty (* may contain a predicate variable *),
              constrs,
              _kind_map ) =
          let cty = Map.Poly.find_exn !dtrenv cons_name in
          instantiate_val_con false ~config
            (Rtype.Env.dep_args_of renv)
            Map.Poly.empty
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
        let renvs, outer_phiss, constrss_args, not_matched =
          List.unzip4
          @@ List.mapi (List.zip_exn pats args) ~f:(fun i (pi, (xi, tyi)) ->
              let renv, outer_phis, constrs, not_matched =
                pattern_match_with renv ~config pi
                  (Term.mk_var xi @@ Rtype.sort_of_val tyi, tyi)
              in
              (* see the tuple case: [xi] is bound only inside this branch, so
                 the not-matched condition refers to the selector on the
                 scrutinee *)
              let not_matched =
                Formula.subst
                  (Map.Poly.singleton xi
                     (T_dt.mk_sel_by_cons dt cons_name i term))
                  not_matched
              in
              (renv, outer_phis, constrs, not_matched))
        in
        ( Rtype.Env.disj_union_list (* assume distinct *) (renv_args :: renvs),
          Set.Poly.union_list
          @@ Set.Poly.singleton
               (Formula.apply_pred pred term (*ToDo: redundant?*))
             :: outer_phiss,
          Set.Poly.union_list (constrs :: constrss_args),
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
              [
                (if is_impure_pure then
                   cgen_subtype_val ~config renv_branch c_branch.val_type
                     c.val_type
                 else Set.Poly.empty);
                cgen_subeff ~config renv_matched rev_comp_effs c_branch.val_type
                  c;
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
                let pat_renv, outer_phis, constrs_params, not_matched =
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
                         constraints: %s"
                        (Pattern.str_of pat)
                        (Env.str_of ~config pat_renv)
                        (String.concat_map_set ~sep:"\n" ~f:Formula.str_of
                           constrs_params));

                ( Env.add_phi renv
                  @@ Formula.rename
                       (Map.Poly.singleton x_tentative x)
                       not_matched,
                  let renv_branch, c_matched, c =
                    (* the scrutinee's refinements [outer_phis] are renamed
                       with the outer scope; the pattern's equations are not.
                       Adding both unrenamed read [match (b, a) with (a, c)]'s
                       refinement of the old [a] as one of the new [a] *)
                    let renv_branch, map =
                      Env.update_with ~config renv (fst pat_renv, outer_phis)
                    in
                    let renv_branch =
                      Env.add_phis renv_branch (snd pat_renv)
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
                      [
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

  (* The refinement predicates of a recursive function's result that must be
     admissible: in the expectation modes, a recursive function whose result
     is an answer value -- a [Prop], represented as a real, or with
     conditioning as a pair of reals (the value and its score) -- is typed by
     the fixpoint rule for answer values, which is sound only for an
     admissible refinement (Scott induction), so each predicate in the
     result's refinement gets kind [Adm].

     The result must actually have the answer sort.  That was assumed
     unchecked, and a result of any other sort was given [Adm] as well: a
     Boolean, an integer or a datatype was excluded, but a unit, a string, a
     type variable, a tuple with a non-real component, or a plain real under
     conditioning was not, and the admissible template refuses every such sort
     at solving time.  None of these can be an answer value, so they are
     treated as the excluded sorts are -- ordinary refinements -- and the
     refusal is reported.  A type variable is the one exception: a use may
     instantiate it to the answer sort, so its refinement is decided at each
     use ([adm_kinds_at_instance]) and nothing is reported at the
     definition.

     What the sort cannot say is whether a real result is an answer value or a
     real number computed by the program: the source language's [prop] and
     [float] are one sort here.  A real result is taken to be an answer value,
     which the solver then reads over the non-negative reals; a real-valued
     recursive function whose result can be negative is outside the mode.

     [answer_refinement_pvars] is the sort test: [Some] the predicate
     variables of [rett]'s refinement when its sort is the mode's answer
     sort, [None] otherwise. *)
  let answer_refinement_pvars adm rett =
    let with_cond = Kind.adm_with_cond adm in
    let scalar_only =
      match adm with
      | Kind.Adm_probability | Kind.Adm_liberal -> true
      | Kind.Adm_expectation | Kind.Adm_conditional -> false
    in
    let sort = Rtype.sort_of_val rett in
    let is_answer_sort =
      match sort with
      | T_real.SReal -> not with_cond
      | T_tuple.STuple [ T_real.SReal; T_real.SReal ] when with_cond -> true
      | T_tuple.STuple (_ :: _ as sorts) ->
          (not with_cond) && (not scalar_only)
          && List.for_all sorts ~f:Term.is_real_sort
      | _ -> false
    in
    if is_answer_sort then
      let _, phi = Rtype.pred_of_val rett in
      Some (Formula.pred_sort_env_of phi)
    else None

  (* The predicate variables of the result refinement of every recursive
     function met in an expectation mode, whatever the result's sort.  A use
     of a generalised function copies these unknowns, and when the result is
     a type variable only the use knows whether it is an answer value, so the
     use consults this set to recognise the return refinement of a recursive
     function ([adm_kinds_at_instance]).  Unknown names are globally fresh,
     so the set is only ever added to. *)
  let rec_result_pvars = ref Set.Poly.empty

  let adm_pvars_of_rec_result mode ~is_rec rty =
    match mode with
    | HFL_Expectation adm when is_rec -> (
        let with_cond = Kind.adm_with_cond adm in
        let rett = Rtype.ret_of_val rty in
        let sort = Rtype.sort_of_val rett in
        (let _, phi = Rtype.pred_of_val rett in
         rec_result_pvars :=
           Set.union !rec_result_pvars
             (Set.Poly.map ~f:fst @@ Formula.pred_sort_env_of phi));
        match answer_refinement_pvars adm rett with
        | Some penv -> Set.Poly.map ~f:(fun (p, sorts) -> (p, adm, sorts)) penv
        | None ->
            let is_excluded =
              Term.is_bool_sort sort || Term.is_int_sort sort
              || Term.is_dt_sort sort
            in
            (* A type-variable result is decided at each use, where the
               variable has been instantiated. *)
            let is_deferred = match sort with Sort.SVar _ -> true | _ -> false in
            if not (is_excluded || is_deferred) then
              Debug.print
              @@ lazy
                   (sprintf
                      "[warning] a recursive function's result has sort %s, \
                       which is not the %s answer sort, so its refinement is \
                       not made admissible"
                      (Term.str_of_sort sort)
                      (if with_cond then "conditional-expectation (real * real)"
                       else "expectation (real)"));
            Set.Poly.empty)
    | HFL_Expectation _ | OCaml | HFL_Bool -> Set.Poly.empty

  (* At a use of a variable whose type [xty0] has the result refinement of a
     recursive function (one of [rec_result_pvars] occurs in it), give kind
     [Adm] to every predicate of the instantiated result refinement when the
     instantiated result sits at an answer-valued position.  Two things make
     this necessary beyond the kind given at the definition.  A result of a
     type-variable sort is refined at each use by a fresh unknown for the
     variable, conjoined into the return refinement: the fixpoint rule needs
     that whole set to contain bottom and be closed under chain suprema, and
     an ordinary unknown there may take the empty set as its least solution,
     so that every bound on the use holds vacuously.  And the definition's
     kind was decided before the variable's sort was known.  Requiring each
     conjunct to be admissible is sufficient for the conjunction (an
     intersection of admissible sets is admissible); it restricts the search
     to the admissible template, so a [sat] stays sound and answers can only
     be lost, never gained. *)
  let adm_kinds_at_instance mode ~xty0 ~xty kind_map =
    match mode with
    | HFL_Expectation adm -> (
        let ret_pvs ty =
          let _, phi =
            Rtype.pred_of_val @@ Rtype.ret_of_val @@ Rtype.mono_type_of_val ty
          in
          Set.Poly.map ~f:fst @@ Formula.pred_sort_env_of phi
        in
        if not (Set.exists (ret_pvs xty0) ~f:(Set.mem !rec_result_pvars)) then
          kind_map
        else (
          (* Preserve the obligation through a still-generic copy. Its sort
             may become answer-valued only at a later use or assertion. *)
          rec_result_pvars := Set.union !rec_result_pvars (ret_pvs xty);
          match
            answer_refinement_pvars adm
            @@ Rtype.ret_of_val @@ Rtype.mono_type_of_val xty
          with
          | None -> kind_map
          | Some penv ->
              Set.fold penv ~init:kind_map ~f:(fun acc (p, _) ->
                  Map.Poly.update acc (Ident.pvar_to_tvar p) ~f:(function
                    | None | Some Kind.Ord -> Kind.Adm adm
                    | Some kind -> kind))))
    | OCaml | HFL_Bool -> kind_map

  (* Follow the same value positions as structural arrow subtyping. An
     actual argument flows into the callee's parameter contravariantly;
     shared result predicates can then carry its obligation to the returned
     function. Process arguments before results so this sharing is visible.
     A parameter unrelated to the result does not mark that result. *)
  let rec adm_kinds_at_subtype mode ~xty0 ~xty kind_map =
    match (Rtype.mono_type_of_val xty0, Rtype.mono_type_of_val xty) with
    | Rtype.RArrow (_, arg0, comp0, _), Rtype.RArrow (_, arg, comp, _) ->
        let kind_map =
          adm_kinds_at_subtype mode ~xty0:arg ~xty:arg0 kind_map
        in
        adm_kinds_at_subtype mode ~xty0:comp0.val_type ~xty:comp.val_type
          kind_map
    | _ -> adm_kinds_at_instance mode ~xty0 ~xty kind_map

  (* ---- The Boolean HFL mode ----
     [hfl_fix_is_nu] maps the name of every recursive binding of a file in the
     Boolean HFL mode to whether its [[@@fix]] names a greatest fixed point;
     filled by [hfl_prescan] before any item is translated, reset per file.
     Keyed by the source name: an HFL file binds each equation once. *)
  let hfl_fix_is_nu : (string, bool) Hashtbl.t = Hashtbl.create (module String)

  (* The admissible shape of a recursive binding's Boolean result in the
     Boolean HFL mode (see [mode]): the refinement [P(args, v)] that
     [Rtype.val_of_sort] made for the final result is replaced by
     [theta(args) => v] for a greatest and [v => theta(args)] for a least
     fixed point, with [theta] a fresh ordinary unknown over the same
     arguments without [v].  Every instance of these shapes is admissible, so
     no kind is needed; generalisation copies [theta] like any unknown.  A
     trivially true refinement is admissible as it is.  Other modes,
     non-recursive bindings and non-Boolean results are left unchanged. *)
  let hfl_bool_admissible_shape mode ~is_rec name rty =
    match mode with
    | HFL_Bool when is_rec ->
        let is_nu =
          match name with
          | Some n ->
              Option.value (Hashtbl.find hfl_fix_is_nu n) ~default:true
          | None -> true
        in
        let rec shape = function
          | Rtype.RArrow (y, t, c, p) ->
              Rtype.RArrow (y, t, { c with val_type = shape c.val_type }, p)
          | Rtype.RGeneral ([], T_bool.SBool, (v, phi)) as t -> (
              match phi with
              | Formula.Atom (atom, _) when Atom.is_pvar_app atom -> (
                  let _, sorts, args, _ = Atom.let_pvar_app atom in
                  match (List.last args, List.drop_last sorts, List.drop_last args) with
                  | Some (Term.Var (v', _, _)), Some sorts', Some args'
                    when Ident.tvar_equal v v' ->
                      let theta =
                        Formula.mk_atom
                        @@ Atom.mk_pvar_app
                             (Ident.mk_fresh_pvar ~prefix:(Some "HFL_") ())
                             sorts' args'
                      in
                      let vb = Formula.of_bool_var v in
                      Rtype.RGeneral
                        ( [],
                          T_bool.SBool,
                          ( v,
                            if is_nu then Formula.mk_imply theta vb
                            else Formula.mk_imply vb theta ) )
                  | _ -> t)
              | phi when Formula.is_true phi -> t
              | _ ->
                  Common.Refusal.refuse "%s"
                    "[hfl] a recursive binding's Boolean result has a \
                     refinement that is not an unknown: its admissible shape \
                     cannot be built")
          | t -> t
        in
        shape rty
    | _ -> rty

  (* The environment returned for [pat] is read in two scopes once the caller
     binds it over [renv]: its types are read in the outer scope (their
     dependency arguments are [dom], renamed by [Env.update_with] where the
     pattern rebinds them), its formulas in the pattern's scope (their free
     variables are the pattern's own, never renamed; see [cgen_let]).  So no
     formula here may mention a variable of [dom] that the binding rebinds:
     [bound] is the set of every variable the whole binding introduces, all
     patterns of a [let ... and ...] included. *)
  let rec env_and_rty_of_pat ~config mode ?(is_top_level = false)
      ?(bound = Set.Poly.empty) dom = function
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
          let refine =
            not is_fun
            (*ToDo*)
          in
          Rtype.val_of_sort ~config ~refine ~svmap dom sort
        in
        let rty = hfl_bool_admissible_shape mode ~is_rec None rty in
        let adm_pvars = adm_pvars_of_rec_result mode ~is_rec rty in
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
          let refine =
            not is_fun
            (*ToDo*)
          in
          Rtype.val_of_sort ~config ~refine ~svmap ~name dom sort
        in
        let rty =
          hfl_bool_admissible_shape mode ~is_rec (Some (name_of_tvar x)) rty
        in
        let adm_pvars = adm_pvars_of_rec_result mode ~is_rec rty in
        (Rtype.Env.singleton_ty x rty, rty, adm_pvars)
    | ( (Pattern.PTuple pats as pat),
        is_fun,
        is_rec,
        (T_tuple.STuple sorts as sort) ) ->
        let renvs, rtys, adm_pvarss =
          List.unzip3
          @@ List.map2_exn pats sorts ~f:(fun pat sort ->
              env_and_rty_of_pat ~config mode ~bound dom
                (pat, is_fun, is_rec, sort))
        in
        (* [phi] relates the outer variables [dom] to the pattern's variables
           in one formula.  A variable of [dom] that the binding rebinds
           ([let (a, c) = (b, a)]) is read through a fresh alias [y'] bound as
           [{v | v = y}]: that type is renamed with the outer scope, while
           [phi] mentions only [y'] and the new [a].  Without the alias the
           [a] of [dom] was read as the new [a], and the contradictory
           relation that resulted made every assertion after the binding
           hold. *)
        let alias_env, phi_terms =
          let terms, sorts = List.unzip dom in
          let alias_env, terms' =
            List.fold_map (List.zip_exn terms sorts)
              ~init:(Some (Rtype.Env.mk_empty ()))
              ~f:(fun acc (t, s) ->
                match (acc, t) with
                | Some acc, Term.Var (y, _, _) when Set.mem bound y -> (
                    match s with
                    | T_tuple.STuple _ ->
                        (* no base alias for a tuple; [phi] is dropped *)
                        (None, t)
                    | _ ->
                        let y' = Ident.mk_fresh_tvar () in
                        let v = Rtype.mk_fresh_tvar_with "v" in
                        ( Some
                            (Rtype.Env.set_ty acc y'
                            @@ Rtype.mk_rbase s
                                 (v, Formula.eq (Term.mk_var v s) t)),
                          Term.mk_var y' s ))
                | _ -> (acc, t))
          in
          (alias_env, terms')
        in
        let tup_ty, phi =
          let terms, sorts = List.unzip dom in
          let pvar = mk_fresh_pvar () in
          let phi =
            match alias_env with
            | None -> Formula.mk_true ()
            | Some _ ->
                Formula.mk_atom
                @@ Atom.mk_pvar_app pvar (sorts @ [ sort ])
                     (phi_terms @ [ Pattern.term_of pat ])
          in
          let v = Rtype.mk_fresh_tvar_with "v" in
          ( Rtype.mk_rtuple rtys
              ( v,
                Formula.mk_atom
                @@ Atom.mk_pvar_app pvar (sorts @ [ sort ])
                     (terms @ [ Term.mk_var v sort ]) ),
            phi )
        in
        ( Rtype.Env.add_phi
            (Rtype.Env.disj_union_list (* assume distinct *)
               (Option.value alias_env ~default:(Rtype.Env.mk_empty ())
               :: renvs))
            phi,
          tup_ty,
          Set.Poly.union_list adm_pvarss )
    | Pattern.PCons _, _, _, _ ->
        failwith
          "[env_and_rty_of_pat] not reachable here because [let T x = ... in \
           ...] is parsed as [match ... with T x -> ...]"
    | _ -> failwith "[env_and_rty_of_pat] unsupported pattern"

  module Preprocessor = Preprocessor.Make (struct
    (* every preprocessing field not given here takes its default, as on the
       constraint solver's own entry point *)
    let config =
      let base =
        Preprocessor.Config.make config.enable_pvar_elim false
          (*config.verbose*)
          Int.max_value
          (* [fixpoint] assumes that any intermediate predicate variables are eliminated for GFP predicate generation*)
          4 false
      in
      {
        base with
        (* the threshold above is unbounded, so a predicate defined once per
           path of a conditional (a callee's result on each branch, copied to
           every call site) would split every clause it is resolved into, and
           the clause count would grow exponentially with the nesting of the
           conditionals; merging its definitions first keeps it linear *)
        Preprocessor.Config.elimination =
          { base.elimination with merge_definitions = true };
      }
  end)

  (* The same, for the definitions of a functor body, with no unknown losing
     an argument: an unknown created in the body takes the functor's members
     as its leading arguments, and [dq_constraints] reads the dependency
     structure off those positions.  The argument reductions would drop a
     member that the clauses force equal to another argument (a member of
     base type and the program variable bound to it), or reorder what is
     left, and the positions would no longer say which arguments are the
     members.  Every reduction is equisatisfiable, so leaving them out
     changes the shape of the extracted constraints and not their meaning. *)
  module FunctorPreprocessor = Preprocessing.Preprocessor.Make (struct
    let config =
      let c = Preprocessor.config in
      {
        c with
        Preprocessing.Preprocessor.Config.argument_reduction =
          {
            reduce = Preprocessing.Preprocessor.Config.No_arg_reduction;
            share_determined = Preprocessing.Preprocessor.Config.No_share_determined;
            drop_constant_args = false;
            drop_fn_copy_args = false;
          };
      }
  end)

  (* whether the definitions being processed are a functor body's *)
  let in_functor_body = ref false

  (* The phase-2 continuation [MBcgen.fold_expr] returns for an expression:
     given the kind map, a solution of the expression's effect and
     signature constraints, a refinement environment and the expected
     refinement computation type, it returns the refinement constraints and
     the extended kind map. *)
  type cont =
    (tvar, Kind.t) Map.Poly.t ->
    (rvar, Sort.o) Map.Poly.t * (svar, Sort.t) Map.Poly.t * (evar, Sort.e) Map.Poly.t ->
    Rtype.Env.t ->
    Rtype.c ->
    constr Set.Poly.t * (tvar, Kind.t) Map.Poly.t

  (* The effect scheme of a top-level item (a constrained type scheme over
     the item's sort, effect and row variables): the effect and signature
     constraints of the item's phase 1, its templates, the instantiations of
     sort variables its traversal recorded, the solution its own typing
     used, and what is needed to run its phase 2 again under another
     solution.  Every variable of the constraints, the templates and the
     recorded instantiations may be renamed, because the environment the
     item was typed in is ground in effects and rows: every earlier item's
     stored type had its effect and row variables defaulted.

     [sc_path] is the OCaml identifier the bound name has, so that a later
     local binding of the same name is not taken for it. *)
  type eff_scheme = {
    sc_path : Path.t;
    sc_name : tvar;
    sc_is_rec : bool;
    sc_vbs : value_binding list;
    sc_pats : Pattern.t list;
    sc_is_pures : bool list;
    sc_is_funs : bool list;
    sc_nexts : cont list;
    sc_templates : Sort.c list;
    sc_template : Sort.c; (* the bound name's own template *)
    sc_extra_templates : Sort.c list;
        (* the templates of the instances the item's own typing made *)
    sc_eff_constrs : (Sort.e list * Sort.e) Set.Poly.t;
    sc_opsig_constrs : (Sort.o * Sort.o) Set.Poly.t;
    sc_ref_id : (svar, Sort.t) Map.Poly.t;
    sc_maps :
      (rvar, Sort.o) Map.Poly.t * (svar, Sort.t) Map.Poly.t * (evar, Sort.e) Map.Poly.t;
    sc_renv : Rtype.Env.t;
  }

  type envs = {
    mode : mode;
    constrs : constr Set.Poly.t;
    exi_senv : sort_env_map;
    kind_map : (tvar, Kind.t) Map.Poly.t;
    fenv : FunEnv.t;
    lifted_universals : (Ident.tvar, sort_env_list) Map.Poly.t;
    dtenv : DTEnv.t;
    renv : Rtype.Env.t;
    eff_schemes : (tvar, eff_scheme) Map.Poly.t;
        (* the effect scheme of each top-level name bound so far whose item
           admits one ([scheme_of_item]); read only when an item's typing
           without them fails *)
  }

  (* [dq], when given, is the universal structure of a functor body's problem
     ([dq_of_functor]): its universal sorts, its universal functions and the
     dependency arguments of each unknown, with every unknown application of
     [constrs] already carrying those arguments ([dq_constraints]).  The
     problem is then made as the SMT-LIB2 reader makes one from the
     corresponding [declare-forall-sort]/[declare-forall-fun]/
     [declare-dep-exists-fun] declarations: the universal sorts are rigid for
     sort inference, the Bool-valued universals are entered in the kind map,
     the dependency map reaches [PCSP.Problem.make] (whose skolemisation of a
     head existential reads it), and the structure is recorded in the
     parameters for the printer. *)
  let pcsp_of ?(skolem_pred = false) ?(sol_space = Map.Poly.empty) ?(dq = None)
      ?(witness_deps = true) envs constrs =
    let uni_sort, uni_senv, dep_map =
      match dq with
      | None -> (Set.Poly.empty, Map.Poly.empty, Map.Poly.empty)
      | Some (svs, unis, deps) ->
          ( Set.Poly.of_list @@ List.map svs ~f:(fun sv -> Sort.SVar sv),
            Map.Poly.of_alist_exn unis,
            deps )
    in
    if false then
      Debug.print
      @@ lazy
           (sprintf "\n*** original:\n%s"
              (String.concat_map_set ~sep:"\n" constrs ~f:Formula.str_of));
    let phis =
      Set.Poly.map (Set.union envs.constrs constrs) ~f:(fun phi ->
          let phi = Evaluator.simplify phi in
          let tvs =
            (*ToDo: use sort_env_of instead?*)
            Formula.term_sort_env_of phi
          in
          Formula.mk_forall_if_bounded (Set.to_list tvs) phi)
    in
    if false then
      Debug.print
      @@ lazy
           (sprintf "\n*** simplified and quantified:\n%s"
              (String.concat_map_set ~sep:"\n" phis ~f:Formula.str_of));
    let phis =
      Typeinf.typeinf
        ~print:(fun _ -> () (*Debug.print*))
        ~rigid:(SMT.Smtlib2.rigid_of uni_sort) ~default:None ~to_sus:true
      @@ Set.to_list phis
    in
    if false then
      Debug.print
      @@ lazy
           (sprintf "\n*** type inferred:\n%s"
              (String.concat_map_list ~sep:"\n" phis ~f:Formula.str_of));
    let pcsp =
      let kind_map =
        (* the reader's [declare-forall-fun] of a Bool result enters the kind
           map as an ordinary predicate; [PCSP.Problem.make] reads the
           universals there as the ones a dependency set can name *)
        Map.Poly.fold uni_senv ~init:envs.kind_map
          ~f:(fun ~key ~data acc ->
            let ret =
              let rec ret s =
                if T_array.is_sarray s then ret (T_array.elem_sort_of s) else s
              in
              ret data
            in
            if Term.is_bool_sort ret && not (Map.Poly.mem acc key) then
              Map.Poly.add_exn acc ~key ~data:Kind.Ord
            else acc)
      in
      let exi_senv, kind_map =
        (* ToDo: given exi_senv and kind_map are incomplete? *)
        List.map phis ~f:Formula.pred_sort_env_of
        |> Set.Poly.union_list
        |> Set.fold ~init:(envs.exi_senv, kind_map)
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
             decl_reading = SMT.Problem.Synthesize;
             lifted_universals = envs.lifted_universals;
             candidates = Map.Poly.empty;
             uni_sort;
             uni_senv;
             exi_senv;
             dep_map = (if witness_deps then dep_map else Map.Poly.empty);
             kind_map;
             fenv = Map.Poly.filter envs.fenv ~f:Quintuple.fth (*ToDo*);
             dtenv = envs.dtenv;
           }
    in
    let pcsp = PCSP.Problem.set_params_sol_space pcsp sol_space in
    match dq with
    | None -> pcsp
    | Some (svs, unis, deps) ->
        PCSP.Problem.update_params pcsp
          {
            (PCSP.Problem.params_of pcsp) with
            dq_universals =
              {
                forall_sorts = svs;
                forall_funs = unis;
                dep_args = Map.Poly.map deps ~f:(List.map ~f:fst);
              };
          }

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

  (* The interface clauses are recognised by the bound variables of their
     premises.  Their premise quantifies over an unknown, which the
     let-time elimination's own problem construction would skolemise into a
     Skolem function that the extracted constraints cannot state, so
     [fixpoint] keeps them out of the elimination (and keeps their
     predicates). *)
  let pp_bound_prefix = "%ppa"

  let rec is_pp_interface = function
    | Formula.Bind (Formula.Forall, (Ident.Tvar x, _) :: _, body, _) ->
        String.is_prefix x ~prefix:pp_bound_prefix || is_pp_interface body
    | Formula.Bind (_, _, body, _) | Formula.UnaryOp (_, body, _) ->
        is_pp_interface body
    | Formula.BinaryOp (_, p, q, _) -> is_pp_interface p || is_pp_interface q
    | _ -> false

  let fixpoint ~config renv kind_map fenv dtenv penv_dtrenv pvs_preds bpvs pvmap
      constrs =
    let interfaces, constrs =
      match config.Rtype.pred_poly_encoding with
      | Rtype.Copying -> (Set.Poly.empty, constrs)
      | Rtype.Universal_interface -> Set.partition_tf constrs ~f:is_pp_interface
    in
    let bpvs = Set.union bpvs (Set.concat_map interfaces ~f:Formula.pvs_of) in
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
      (* Set.Poly.map constrs ~f:(Formula.map_atom ~f:(function
         | Atom.App (Predicate.Var (pvar, sorts), ts, _)
           when Set.mem pvs_dtrenv pvar &&
                Set.is_empty @@ Set.Poly.union_list @@
                List.map sorts ~f:Term.svs_of_sort ->
           let name = Ident.name_of_pvar pvar ^ String.bracket @@ String.concat_map_list ~sep:"\n" sorts ~f:Term.str_of_sort in
           Formula.mk_atom @@ Atom.mk_pvar_app (Ident.Pvar name) sorts ts
         | atom -> Formula.mk_atom atom)) *)
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
          lifted_universals = Map.Poly.empty;
          dtenv;
          renv = Rtype.Env.mk_empty () (*dummy*);
          eff_schemes = Map.Poly.empty;
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
        @@ Set.Poly.union_list
             [
               bpvs;
               pvs_dummy;
               (* every fixpoint predicate defined so far, the copies made
                  while generating this binding's body included: a caller's
                  [bpvs] was computed before the body instantiated any scheme,
                  and a copy missing from it was eliminated here as an unknown
                  with no lower bound, which made the definition being read off
                  [false] *)
               Set.Poly.of_list Map.Poly.(keys !mu_preds @ keys !nu_preds);
               (* and every unknown such a definition applies: the definition
                  lives outside these clauses, so the elimination cannot see
                  that it uses the unknown, and eliminating one dropped its
                  clauses (a callee's precondition at its call site) while the
                  definition kept naming it, which left it unconstrained *)
               Set.Poly.union_list
               @@ List.map ~f:(fun (_, phi) -> Formula.pvs_of phi)
               @@ Map.Poly.data !mu_preds @ Map.Poly.data !nu_preds;
               (* and, when instances are shared, every shared instance:
                  other definitions' clauses name it too, and eliminating it
                  from this definition's clauses alone would drop the
                  constraints they put on it (empty when sharing is off) *)
               Rtype.shared_instance_copies ();
             ]
      in
      (* the following is needed since Z3interface.sort_of invokes RtypeParser *)
      Rtype.cgen_config := config;
      Rtype.renv_ref := renv;
      set_dtenv dtenv;
      (* not a satisfiability question: the clauses are simplified so that
         the definitions of the (co)inductive predicates can be read off
         them, and a refutation would replace them by [false] and leave no
         definition to read *)
      (if !in_functor_body then FunctorPreprocessor.preprocess
       else Preprocessor.preprocess)
        pcsp0
        ~purpose:(Preprocessing.Preprocessor.Purpose.Eliminate_keeping bpvs)
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
    (* The definitions are read off the preprocessed clauses, so under the
       preprocessed problem's unknowns: preprocessing may replace an unknown
       of the body by a new one (an argument that is constant everywhere is
       dropped, and the unknown renamed), which the problem before it does not
       bind, and reading against that problem failed with an unbound name.
       The problem before it still binds a dummy the preprocessing removed with
       all its clauses, whose definition is then [false]; so both are read. *)
    let senv_read =
      Map.force_merge (PCSP.Problem.senv_of pcsp0) (PCSP.Problem.senv_of pcsp)
    in
    let theta_mu =
      (*if Fn.non Map.Poly.is_empty mu_pvmap then*)
      Debug.print @@ lazy "*** inductive predicates extracted:";
      Debug.print @@ lazy "";
      Map.Poly.mapi mu_pvmap ~f:(fun ~key:pvar' ~data:pvar ->
          let env, t =
            ClauseSet.pred_of_pos senv_read clauses2
            @@ Ident.pvar_to_tvar pvar
          in
          let phi =
            Logic.ExtTerm.to_old_fml
              (PCSP.Problem.senv_of pcsp)
              (Map.Poly.of_alist_exn env)
              t
          in
          assert (Set.are_disjoint (Formula.pvs_of phi) pvs_dummy);
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
            ClauseSet.pred_of_pos senv_read clauses2
            @@ Ident.pvar_to_tvar pvar
          in
          let phi =
            Logic.ExtTerm.to_old_fml
              (PCSP.Problem.senv_of pcsp)
              (Map.Poly.of_alist_exn env)
              t
          in
          assert (Set.are_disjoint (Formula.pvs_of phi) pvs_dummy);
          let env = Logic.to_old_sort_env_list env in
          Debug.print
          @@ lazy
               (sprintf "%s(%s) =nu\n  %s\n" (Ident.name_of_pvar pvar')
                  (str_of_sort_env_list Term.str_of_sort env)
                  (Formula.str_of phi));
          (env, phi))
    in
    nu_preds := Map.force_merge !nu_preds theta_nu;
    let to_old =
      Clause.normalize_uni_senv >> Clause.to_senv_formula
      >> Tuple2.uncurry
         @@ Logic.ExtTerm.to_old_fml (PCSP.Problem.senv_of pcsp)
    in
    (* A clause that applies a placeholder only negatively is not part of
       its definition but a constraint on it: the derivation of the body
       uses the effect the placeholder stands for (passing it on to a
       continuation's answer effect, say).  The placeholder denotes the
       fixpoint once the definition is closed, so the clause holds of the
       fixpoint predicate: it is kept with each placeholder replaced by its
       fixpoint predicate.  Dropped, as it was, it left the unknown it
       constrains with no lower bound, whose least interpretation [false]
       then made the effects that apply it vacuous. *)
    let constrs_using =
      let key_of_dummy =
        Map.Poly.of_alist_exn
        @@ List.map
             (Map.Poly.to_alist mu_pvmap @ Map.Poly.to_alist nu_pvmap)
             ~f:(fun (key, dummy) -> (dummy, key))
      in
      Set.Poly.map ~f:(to_old >> Formula.rename_pvars key_of_dummy)
      @@ Set.filter clauses2 ~f:(fun c ->
          Set.are_disjoint pvs_dummy
          @@ Set.Poly.map ~f:Ident.tvar_to_pvar
          @@ Clause.pos_pvars c)
    in
    let constrs = Set.union (Set.Poly.map clauses1 ~f:to_old) constrs_using in
    Debug.print @@ lazy "*** predicate constraints extracted:";
    Debug.print @@ lazy "";
    Debug.print
    @@ lazy (String.concat_map_set ~sep:"\n" constrs ~f:Formula.str_of);
    Debug.print @@ lazy "";
    Set.union constrs interfaces

  let generalize ~config renv pat_renv constrs =
    (* ToDo: note that nu_preds and mu_preds can be type-polymorphic as well! *)
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
          with exn_ when not (Common.Timer.is_async exn_) ->
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

  (** Predicate polymorphism checked once ([Rtype.Universal_interface]).

      [generalize] gives a definition the bounded predicate-polymorphic type
      [forall P1..Pn. C => T] over its own refinement predicates, and a use
      copies [C] onto fresh predicates.  Under [Universal_interface] a
      definition that qualifies ([pp_universal_generalize]) is instead checked
      once, for every behaviour of its functional parameters:
      - a predicate occurring in [T] only at negative positions inside the
        type of a functional parameter (what a function the definition is
        given guarantees about its result) becomes a universally quantified
        Bool-valued function [X^], a term variable of array sort applied by
        [select];
      - a predicate occurring only at negative positions outside the
        functional parameters (the refinement of a first-order argument)
        stays one predicate shared by the definition and all its uses: each
        use must establish it, and it does not depend on the universals;
      - every other own predicate [P] (positive in [T], or internal to [C])
        becomes [P'], which takes the universals as leading arguments: its
        dependency set;
      - the constraints of [C] that mention only universals are the bound
        [B]; the others are emitted once, rewritten, under the premise
        [forall-closure of B]; the bound is also kept in the type, so a use
        must establish it of its instance;
      - for each [P] of [T] at a positive position, the type keeps the
        interface clause [(/\_X forall a. X^(a) => X(a)) /\ P'(X^, y) => P(y)];
        a use renames [X] and [P] to its instance [K] and [Q], so it reads
        "[Q] contains [P'] at every array no larger than [K]".
      The interface is exact when every universal occurs only negatively in
      the emitted constraints and those are Horn: the least [P'] is then
      monotone in the universals, so its value at [K] is the largest among
      the arrays below [K].  A definition that does not qualify keeps the
      copying type.  Sound because the emitted constraints type the
      definition by [forall X. B(X) => T[X, P'(X)]] and a use instantiates
      [X] by its own predicates, which the bound copy makes admissible. *)

  (* the universals made so far, in order, and the dependency set of each
     [P']; reset by [top_level] *)
  let pp_universals : sort_env_list ref = ref []
  let pp_deps : (Ident.pvar, sort_env_list) Map.Poly.t ref = ref Map.Poly.empty

  let rec has_binder = function
    | Formula.Bind ((Formula.Forall | Formula.Exists), _, _, _) -> true
    | Formula.Bind (_, _, body, _) | Formula.UnaryOp (_, body, _) ->
        has_binder body
    | Formula.BinaryOp (_, p, q, _) -> has_binder p || has_binder q
    | _ -> false

  exception Pp_refuse of string

  (* the predicate occurrences of a value type, as (predicate, positive,
     inside a functional parameter); refuses a shape outside the fragment *)
  let rec pp_occ_val ~config pos inside acc = function
    | Rtype.RGeneral ([], _, (_, phi)) -> pp_occ_phi pos inside acc phi
    | Rtype.RArrow (_, t, c, (_, phi)) ->
        if not (Rtype.is_pure_comp ~config c) then
          raise (Pp_refuse "an effectful computation in the type");
        let acc = pp_occ_phi pos inside acc phi in
        let acc =
          pp_occ_val ~config (not pos) (inside || Rtype.is_rarrow t) acc t
        in
        pp_occ_val ~config pos inside acc c.val_type
    | _ -> raise (Pp_refuse "a type other than base types and arrows")

  and pp_occ_phi pos inside acc phi =
    let ps, ns = Formula.atoms_of ~pos phi in
    let add polarity atoms acc =
      Set.fold atoms ~init:acc ~f:(fun acc -> function
        | Atom.App (Predicate.Var (pv, _), _, _) -> (pv, polarity, inside) :: acc
        | _ -> acc)
    in
    add true ps @@ add false ns acc

  let pp_pvs_of_atoms atoms =
    Set.Poly.filter_map atoms ~f:(function
      | Atom.App (Predicate.Var (pv, _), _, _) -> Some pv
      | _ -> None)

  (* [Some (ty', emitted)] when the definition [name] of generalised type
     [ty] qualifies: [ty'] is its type with the interface as its bound and
     [emitted] its constraints, checked once; [None] keeps [ty]. *)
  let pp_universal_generalize ~config kind_map name ty =
    match ty with
    | Rtype.RForall (penv, constrs, c) when Rtype.is_pure_comp ~config c -> (
        try
          if not (Map.is_empty !mu_preds && Map.is_empty !nu_preds) then
            raise (Pp_refuse "fixpoint predicates");
          let own = Map.Poly.key_set penv in
          let occ = pp_occ_val ~config true false [] c.val_type in
          let occ_of p =
            List.filter_map occ ~f:(fun (q, pos, inside) ->
                if Ident.pvar_equal p q then Some (pos, inside) else None)
          in
          let classify p =
            match occ_of p with
            | [] -> `Internal
            | os when List.for_all os ~f:(fun (pos, _) -> pos) -> `Out
            | os when List.for_all os ~f:(fun (pos, ins) -> (not pos) && ins) ->
                `Uni
            | os when List.for_all os ~f:(fun (pos, ins) -> not (pos || ins)) ->
                `Shared
            | _ ->
                raise
                  (Pp_refuse
                     ("the predicate " ^ Ident.name_of_pvar p
                    ^ " occurs at two kinds of position"))
          in
          let cls = Set.to_list own |> List.map ~f:(fun p -> (p, classify p)) in
          let of_cls k =
            List.filter_map cls ~f:(fun (p, k') ->
                if Stdlib.(k = k') then Some p else None)
          in
          let unis_p = of_cls `Uni and shared = of_cls `Shared in
          let outs = of_cls `Out and internals = of_cls `Internal in
          if List.is_empty unis_p then
            raise (Pp_refuse "no predicate of a functional parameter's result");
          Set.iter own ~f:(fun p ->
              match Map.Poly.find kind_map (Ident.pvar_to_tvar p) with
              | None | Some Kind.Ord -> ()
              | Some _ -> raise (Pp_refuse "a predicate of a non-ordinary kind"));
          let uset = Set.Poly.of_list unis_p in
          Set.iter constrs ~f:(fun phi ->
              if has_binder phi && not (is_pp_interface phi) then
                raise (Pp_refuse "a quantified constraint");
              let ps, _ = Formula.atoms_of phi in
              if not (Set.are_disjoint (pp_pvs_of_atoms ps) uset) then
                raise
                  (Pp_refuse
                     "a predicate of a functional parameter's result is \
                      required by the definition, not only assumed"));
          let unis =
            List.map unis_p ~f:(fun p ->
                let sorts = Map.Poly.find_exn penv p in
                if List.is_empty sorts then
                  raise (Pp_refuse "a predicate without arguments");
                ( p,
                  ( Ident.Tvar ("!" ^ name ^ "." ^ Ident.name_of_pvar p),
                    T_array.of_arrow @@ Sort.mk_fun (sorts @ [ T_bool.SBool ]) ) ))
          in
          let uenv = List.map unis ~f:snd in
          let uni_of p = List.Assoc.find unis ~equal:Ident.pvar_equal p in
          let bound, body =
            Set.partition_tf constrs ~f:(fun phi ->
                let pvs = Set.inter (Formula.pvs_of phi) own in
                (not (Set.is_empty pvs)) && Set.is_subset pvs ~of_:uset)
          in
          let os = outs @ internals in
          (* The dependency set of each [P']: the universals its derivations
             read, i.e. those in the body of a constraint with it in the head,
             closed under the other [P']s in such bodies, plus those of the
             bound (a [P'] is empty where the bound fails).  The least [P'] is
             a function of these alone, since the constraints are its only
             lower bounds; a [P'] that reads none is connected to its uses
             without any premise. *)
          let deps =
            let bound_unis =
              Set.inter uset (Set.concat_map bound ~f:Formula.pvs_of)
            in
            let init =
              Map.Poly.of_alist_exn @@ List.map os ~f:(fun p -> (p, bound_unis))
            in
            let step deps =
              Set.fold body ~init:deps ~f:(fun deps phi ->
                  let ps, ns = Formula.atoms_of phi in
                  let read =
                    Set.fold (pp_pvs_of_atoms ns) ~init:Set.Poly.empty
                      ~f:(fun acc q ->
                        if Set.mem uset q then Set.add acc q
                        else
                          match Map.Poly.find deps q with
                          | Some d -> Set.union acc d
                          | None -> acc)
                  in
                  Set.fold (pp_pvs_of_atoms ps) ~init:deps ~f:(fun deps q ->
                      match Map.Poly.find deps q with
                      | Some d -> Map.Poly.set deps ~key:q ~data:(Set.union d read)
                      | None -> deps))
            in
            let rec fix deps =
              let deps' = step deps in
              if Map.Poly.equal Set.equal deps deps' then deps else fix deps'
            in
            Map.Poly.map (fix init) ~f:(fun d ->
                List.filter_map unis_p ~f:(fun x ->
                    if Set.mem d x then Some x else None))
          in
          let dep_env p =
            List.map (Map.Poly.find_exn deps p) ~f:(fun x ->
                Option.value_exn (uni_of x))
          in
          let pmap =
            Map.Poly.of_alist_exn
            @@ List.map os ~f:(fun p ->
                (p, Ident.mk_fresh_pvar ~prefix:(Some (Ident.name_of_pvar p ^ "'")) ()))
          in
          let sel (u, us) args =
            Formula.mk_atom @@ Atom.of_bool_term
            @@ T_array.mk_select_app (Term.mk_var u us) args
          in
          let app' p sorts args =
            let denv = dep_env p in
            Formula.mk_atom
            @@ Atom.mk_pvar_app (Map.Poly.find_exn pmap p)
                 (List.map denv ~f:snd @ sorts)
                 (List.map denv ~f:(fun (x, s) -> Term.mk_var x s) @ args)
          in
          let rewrite =
            Formula.map_atom ~f:(function
              | Atom.App (Predicate.Var (p, _), args, _) when Option.is_some (uni_of p)
                ->
                  sel (Option.value_exn (uni_of p)) args
              | Atom.App (Predicate.Var (p, sorts), args, _)
                when Map.Poly.mem pmap p ->
                  app' p sorts args
              | atom -> Formula.mk_atom atom)
          in
          let close phi =
            let fvs =
              Set.to_list
              @@ Set.filter (Formula.term_sort_env_of phi) ~f:(fun (x, _) ->
                  not (List.Assoc.mem uenv ~equal:Stdlib.( = ) x))
            in
            Formula.mk_forall_if_bounded fvs phi
          in
          let premise =
            Formula.and_of @@ List.map (Set.to_list bound) ~f:(rewrite >> close)
          in
          let emitted =
            Set.Poly.map body ~f:(fun phi ->
                let phi = rewrite phi in
                if Set.is_empty bound then phi else Formula.mk_imply premise phi)
          in
          let interface =
            Set.Poly.of_list
            @@ List.map outs ~f:(fun p ->
                let sorts = Map.Poly.find_exn penv p in
                let ys =
                  List.map sorts ~f:(fun s -> (Rtype.mk_fresh_tvar_with "y", s))
                in
                let instance_premise =
                  Formula.and_of
                  @@ List.map (Map.Poly.find_exn deps p) ~f:(fun x ->
                      let xs =
                        List.map (Map.Poly.find_exn penv x) ~f:(fun s ->
                            ( Ident.mk_fresh_tvar ~prefix:(Some pp_bound_prefix) (),
                              s ))
                      in
                      let args = Term.of_sort_env xs in
                      Formula.mk_forall xs
                      @@ Formula.mk_imply
                           (sel (Option.value_exn (uni_of x)) args)
                           (Formula.mk_atom
                           @@ Atom.mk_pvar_app x (List.map xs ~f:snd) args))
                in
                Formula.mk_imply
                  (Formula.mk_and instance_premise
                     (app' p sorts (Term.of_sort_env ys)))
                  (Formula.mk_atom
                  @@ Atom.mk_pvar_app p sorts (Term.of_sort_env ys)))
          in
          pp_universals := !pp_universals @ uenv;
          pp_deps :=
            Map.Poly.fold pmap ~init:!pp_deps ~f:(fun ~key ~data acc ->
                Map.Poly.set acc ~key:data ~data:(dep_env key));
          let penv' =
            Map.Poly.filter_keys penv ~f:(fun p ->
                not (List.mem shared p ~equal:Ident.pvar_equal))
          in
          Debug.print
          @@ lazy
               (sprintf
                  "[pred_poly] %s is checked once over %s; %d constraints \
                   emitted, %d interface clauses"
                  name
                  (String.concat_map_list ~sep:", " uenv ~f:(fst >> Ident.name_of_tvar))
                  (Set.length emitted) (Set.length interface));
          Some (Rtype.RForall (penv', Set.union bound interface, c), emitted)
        with Pp_refuse reason ->
          Debug.print
          @@ lazy (sprintf "[pred_poly] %s is copied per use: %s" name reason);
          None)
    | _ -> None

  let cgen_let ~config mode ~is_top_level ?opsig fenv dtenv is_rec pats
      (is_pures, is_funs, next1s, c1s) kind_map maps renv =
    let open Rtype in
    let bound = Set.Poly.union_list @@ List.map pats ~f:Pattern.tvars_of in
    let pat_renvs, cs, adm_pvarss =
      List.unzip3
      @@ List.map3_exn pats (List.zip_exn is_funs is_pures) c1s
           ~f:(fun pat (is_fun, is_pure) c1 ->
             let dom = Env.dep_args_of renv in
             (* Reusing a source name after shadowing must not reuse its old
                predicate signature, whose dependency arguments may differ. *)
             let name_top_level =
               is_top_level
               && Set.for_all (Pattern.tvars_of pat) ~f:(fun x ->
                   Option.is_none (Env.look_up renv x))
             in
             let pat_renv, t, adm_pvars =
               env_and_rty_of_pat ~config mode ~is_top_level:name_top_level
                 ~bound dom
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
      Set.fold adm_pvars ~init:kind_map ~f:(fun acc (pv, adm, _) ->
          Map.Poly.add_exn acc ~key:(Ident.pvar_to_tvar pv)
            ~data:(Kind.Adm adm))
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
                     [
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
    let kind_map_out = Map.force_merge_list kind_maps in
    let generalized, emitted =
      if generalizable then
        let constrs_merged = Set.Poly.union_list constrss in
        let generalized =
          List.map2_exn pat_renvs constrss
            ~f:(fun (pat_renv, phis (* must be empty *)) constrs ->
              ( generalize ~config renv pat_renv
                  (if is_rec then constrs_merged else constrs),
                phis ))
        in
        match (config.pred_poly_encoding, pats, generalized) with
        | Universal_interface, [ Pattern.PVar (x, _) ], [ (pat_renv, phis) ]
          when is_top_level && (not !in_functor_body)
               && Map.Poly.length pat_renv = 1 -> (
            match
              pp_universal_generalize ~config kind_map_out (Ident.name_of_tvar x)
                (Map.Poly.find_exn pat_renv x)
            with
            | Some (ty, emitted) ->
                ([ (Map.Poly.singleton x ty, phis) ], emitted)
            | None -> (generalized, Set.Poly.empty))
        | _ -> (generalized, Set.Poly.empty)
      else (pat_renvs, Set.Poly.empty)
    in
    let renv_body, map =
      (* shadowing: the patterns' types are read in the outer scope and are
         renamed with it; their formulas are read in the patterns' scope and
         are not (see [env_and_rty_of_pat]) *)
      let senv, phis =
        Env.disj_union_list
        (* assume the following are distinct *)
        generalized
      in
      let renv_body, map =
        Env.update_with ~config renv (senv, Set.Poly.empty)
      in
      (Env.add_phis renv_body phis, map)
    in
    ( List.map cs ~f:(rename_comp ~config map),
      renv_bound,
      adm_pvars,
      (if generalizable then emitted else Set.Poly.union_list constrss),
      kind_map_out,
      renv_body,
      map,
      constrss )

  (* ---- Labelled calls: [(f a1 ... an [@copy lbl])] ----
     Every use of a generalised function instantiates its refinement
     predicates afresh (bounded predicate polymorphism), so a call has its own
     copy of [f]'s predicates, constrained by the arguments that call passes.
     A label names that copy for the lemmas and properties of the file.
     [pending_copy_label] is the label of the call whose head is being
     instantiated (set by [f_copy_label] around the head's [f_var], read and
     cleared there), and [copy_label_copies] maps each label to the renamings
     its call's instantiations made (one per invocation of the head's
     continuation; a continuation may run more than once, and then the label
     names every copy it made).  Reset per file. *)
  let pending_copy_label : string option ref = ref None

  let copy_label_copies :
      (string, (Ident.pvar * Ident.pvar) list list) Hashtbl.t =
    Hashtbl.create (module String)

  (* OCaml's integer [/] and [mod] raise [Division_by_zero] when the divisor
     is 0, and RCaml reads an escaping exception as a failure, as it reads
     [assert false]: a program whose division can see a zero divisor does not
     have the type it is checked against.  So these two primitives are typed
       [x:int -> (y:{y':int | y' <> 0}) -> {v:int | v = x op y}]
     where [op] truncates toward zero ([Value.Truncated], OCaml's rounding for
     both).  The refinement on the divisor is a precondition: every
     application must prove its argument non-zero in its environment, exactly
     where a refinement-typed [assert (y <> 0)] would put the obligation, and
     the result's meaning at a non-zero divisor is unchanged.  This
     over-approximates the failures of a program that catches the exception
     with [try ... with Division_by_zero -> ...]: such a handler is not
     consulted, so a division it guards is still an obligation (a refutation,
     never a wrong proof).  The total reading (an arbitrary value at a zero
     divisor, as SMT-LIB's [div] and [mod]) is not OCaml's meaning. *)
  let is_int_division = function
    | "Stdlib./" | "Stdlib.mod" | "Stdlib.\\#mod" -> true
    | _ -> false

  let rtype_of_int_division ~config name =
    let open Rtype in
    let fsym = Rtype.fsym_of_str T_int.SInt name in
    let x = Rtype.mk_fresh_tvar_with "x" in
    let y = Rtype.mk_fresh_tvar_with "y" in
    let y' = Rtype.mk_fresh_tvar_with "y" in
    let v = Rtype.mk_fresh_tvar_with "v" in
    mk_rarrow x
      (simple_val_of_sort ~config T_int.SInt)
      (pure_comp_of_val ~config
      @@ mk_rarrow y
           (mk_val ~config T_int.SInt
              (y', Formula.neq (Term.mk_var y' T_int.SInt) (T_int.zero ())))
           (pure_comp_of_val ~config
           @@ mk_val ~config T_int.SInt
                ( v,
                  Formula.eq (Term.mk_var v T_int.SInt)
                  @@ Term.mk_fsym_app fsym
                       [ Term.mk_var x T_int.SInt; Term.mk_var y T_int.SInt ]
                ))
           (mk_fresh_trivial_pred ()))
      (mk_fresh_trivial_pred ())

  let sort_of_either = function
    | First (_, _, c) -> c.Sort.val_type
    | Second (_, sort) -> sort

  let cgen_either ~config mode kind_map renv maps opsig =
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
        (* A variable in argument position is a use like any other: an
           instance of a generalised type copies its unknowns, and the copies
           take their kinds from the caller's kind map, which is returned
           extended with them. *)
        let c, constrs, kind_map =
          match Env.look_up renv x with
          | Some xty0 ->
              let xty, constrs, kind_map =
                instantiate_val ~print:Debug.print ~config
                  (Env.dep_args_of renv) kind_map
                  (Map.Poly.empty, Map.Poly.empty)
                  (xty0, sort)
              in
              let kind_map = adm_kinds_at_instance mode ~xty0 ~xty kind_map in
              (comp_of_term ~config (Term.mk_var x sort) xty, constrs, kind_map)
          | None ->
              failwith
              @@ sprintf "[cgen_either] unbound variable: %s : %s\nrenv = %s"
                   (name_of_tvar x) (Term.str_of_sort sort)
                   (Env.str_of ~config renv)
        in
        ((x, c, true), (constrs, kind_map))

  (* [has_scheme p] says whether the top-level binding [p] names is to be
     instantiated from its effect scheme at this traversal's occurrences,
     and [scheme_instance p] makes one such instance (see
     [instance_of_scheme]); by default no occurrence is, which is the
     traversal of an item typed without effect polymorphism. *)
  let cgen_expr ?(has_scheme = fun (_ : Path.t) -> false)
      ?(scheme_instance =
        fun (p : Path.t) ->
          failwith @@ sprintf "[cgen_expr] no effect scheme for %s" (Path.name p))
      ~config mode fenv dtenv senv (expr : expression) =
    let open Rtype in
    MBcgen.fold_expr dtenv false senv expr
      ~f:
        (object
           method has_scheme p = has_scheme p
           method f_scheme_instance p = scheme_instance p

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
             let enable_lhs_param =
               true
               (*ToDo*)
             in
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
                               (T_real.mk_real Q.(one / of_int 2), T_real.SReal);
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
                           (List.map2_exn coeffs_t args ~f:T_real.mk_rmul)
                           ~f:T_real.mk_radd
                       in
                       let phi =
                         Formula.mk_and
                           (Formula.mk_atom
                           @@ T_real.mk_rleq (T_real.rzero ()) vt)
                           (Formula.mk_atom
                           @@ T_real.mk_rleq
                                (if enable_lhs_param then
                                   T_real.mk_rmul lhs_coeff_t vt
                                 else vt)
                           @@ T_real.mk_radd cx (T_real.mk_rmul coeff_t yt))
                       in
                       let phi' =
                         Formula.mk_and
                           (Formula.mk_atom
                           @@ T_real.mk_rleq (T_real.rzero ()) vt)
                           (Formula.mk_atom
                           @@ T_real.mk_rleq
                                (if enable_lhs_param then
                                   T_real.mk_rmul lhs_coeff_t vt
                                 else vt)
                           @@ T_real.mk_radd cx
                                (T_real.mk_rmul coeff_t
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
                         @@ Atom.pvar_app_of_senv p [ (x, T_int.SInt) ])
                       @@ Formula.leq (T_int.one ()) xt)
                 in
                 let constrs_rhs_pvars =
                   if true (*ToDo*) then
                     Set.Poly.of_list
                     @@ List.map2_exn rhs_pvars rhs_params ~f:(fun p x ->
                         let xt = Term.mk_var x T_int.SInt in
                         Formula.mk_imply
                           (Formula.mk_atom
                           @@ Atom.pvar_app_of_senv p [ (x, T_int.SInt) ])
                         @@ Formula.leq (T_int.zero ()) xt)
                   else Set.Poly.empty
                 in
                 ( Rtype.Env.add_phis renv
                     (Set.Poly.of_list
                     @@ List.map2_exn (lhs_pvars @ rhs_pvars)
                          (lhs_params @ rhs_params) ~f:(fun p x ->
                            Formula.mk_atom
                            @@ Atom.pvar_app_of_senv p [ (x, T_int.SInt) ])),
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

           method f_copy_label lbl next kind_map maps renv ty =
             let saved = !pending_copy_label in
             pending_copy_label := Some lbl;
             Exn.protect
               ~f:(fun () -> next kind_map maps renv ty)
               ~finally:(fun () -> pending_copy_label := saved)

           method f_var (_is_handled, _rec_vars) (x, sort) kind_map maps renv ty
               =
             let sort = Term.subst_sort maps sort in
             (* the label of the call this variable heads, if any: this
                instantiation makes the copy it names *)
             let label = !pending_copy_label in
             pending_copy_label := None;
             (*print_endline @@ Ident.name_of_tvar x ^ ": " ^ Term.str_of_sort sort;*)
             let xty, constrs, kind_map =
               match Env.look_up renv x with
               | Some xty ->
                   let xty0 = xty in
                   let recorder = ref [] in
                   if Option.is_some label then
                     Rtype.recorded_renamings := Some recorder;
                   let xty, constrs, kind_map =
                     Exn.protect
                       ~finally:(fun () -> Rtype.recorded_renamings := None)
                       ~f:(fun () ->
                         instantiate_val ~print:Debug.print ~config
                           (Env.dep_args_of renv) kind_map
                           (Map.Poly.empty, Map.Poly.empty)
                           (xty, sort))
                   in
                   Option.iter label ~f:(fun lbl ->
                       Hashtbl.add_multi copy_label_copies ~key:lbl
                         ~data:!recorder);
                   let kind_map =
                     adm_kinds_at_instance mode ~xty0 ~xty kind_map
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
             (* A binding checks this value against a fresh return refinement.
                Carry recursive-result provenance to that refinement as well
                as to the instance, before the binding is generalised. *)
             let kind_map =
               adm_kinds_at_subtype mode ~xty0:xty.val_type ~xty:ty.val_type
                 kind_map
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
                   else if is_int_division (Ident.name_of_tvar x) then
                     rtype_of_int_division ~config (Ident.name_of_tvar x)
                   else of_term ~print:Debug.print ~config term
                 with exn_ when not (Common.Timer.is_async exn_) -> of_term ~print:Debug.print ~config term
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
                 [
                   constrs;
                   cgen_subtype_comp ~config renv
                     (pure_comp_of_val ~config cty)
                     ty;
                 ],
               kind_map )

           method f_construct _dt cons_name nexts_either kind_map maps renv ty =
             (*let dt = Datatype.subst maps dt in*)
             let nexts_either =
               List.map nexts_either ~f:(MBcgen.subst_all_either maps)
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
               (* [generic_constructor_instantiation] (default): the generic
                  instantiation at [sorts -> sort of ty]; off, the
                  constructor-specific one *)
               if config.Rtype.generic_constructor_instantiation then
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
                     cgen_either ~config mode kind_map renv maps opsig next
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
                 [
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
               List.map next2s_either ~f:(MBcgen.subst_all_either maps)
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
                     cgen_either ~config mode kind_map renv maps opsig next
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
                 [
                   cgen_subeff ~config renv rev_comp_effs ty.val_type ty;
                   constrs';
                   constrs;
                 ],
               kind_map )

           method f_tuple nexts_either kind_map maps renv ty =
             let nexts_either =
               List.map nexts_either ~f:(MBcgen.subst_all_either maps)
             in
             (* *)
             Debug.print
             @@ lazy (sprintf "[rcaml:tuple] %s\n" @@ str_of_comp ~config ty);
             let res, constrs, kind_map =
               let opsig = `Refined ty.op_sig in
               List.fold_right nexts_either ~init:([], Set.Poly.empty, kind_map)
                 ~f:(fun next (res, constrs1, kind_map) ->
                   let r, (constrs2, kind_map) =
                     cgen_either ~config mode kind_map renv maps opsig next
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
                 [
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
             let next3_opt = MBcgen.subst_all_opt maps next3_opt in
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
             let next1_either = MBcgen.subst_all_either maps next1_either in
             (* *)
             let opsig = `Refined ty.op_sig in
             let matched, (constrs1, kind_map) =
               cgen_either ~config mode kind_map renv maps opsig next1_either
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
                     [
                       constrs;
                       cgen_subeff ~config renv_then rev_comp_effs ty_then ty;
                       cgen_subtype_val ~config renv_then ty_then @@ ty.val_type;
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
                   map,
                   _definition_constrss ) =
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
                 [
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
                 [
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
                    else mk_temp_trivial ());
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

           method f_perform _is_atp attrs (op_name, op_sort, op_cont)
               nexts_either kind_map maps renv ty =
             let op_sort = Term.subst_sort maps op_sort in
             let op_cont = Term.subst_cont maps op_cont in
             let nexts_either =
               List.map nexts_either ~f:(MBcgen.subst_all_either maps)
             in
             (* *)
             Debug.print
             @@ lazy (sprintf "[rcaml:perform] %s\n" @@ str_of_comp ~config ty);
             let res, constrs, kind_map =
               let opsig = `Refined ty.op_sig in
               List.fold_right nexts_either ~init:([], Set.Poly.empty, kind_map)
                 ~f:(fun next (res, constrs1, kind_map) ->
                   let r, (constrs2, kind_map) =
                     cgen_either ~config mode kind_map renv maps opsig next
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
             let t_op, c_pfm, t_pfm =
               match op_cont with
               | Sort.Eff (cret1, cret2) ->
                   let x = Ident.mk_fresh_tvar () in
                   let y = Ident.mk_fresh_tvar () in
                   let t_y = val_of_sort ~config ~refine:true dom' op_sort in
                   let c1 =
                     let refine, dom =
                       (true, dom' @ [ (Term.mk_var y op_sort, op_sort) ])
                     in
                     let temp, opsig, cont =
                       (true (*ToDo*), `Sort cret1.op_sig, cret1.cont_eff)
                     in
                     comp_of_sort ~config ~refine ~temp ~opsig ~cont dom
                       cret1.val_type
                   in
                   let c2 =
                     let sort = Sort.mk_arrow op_sort cret1.val_type in
                     let refine, dom =
                       (true, dom' @ [ (Term.mk_var x sort, sort) ])
                     in
                     let temp, opsig, cont =
                       (true (*ToDo*), `Sort cret2.op_sig, cret2.cont_eff)
                     in
                     comp_of_sort ~config ~refine ~temp ~opsig ~cont dom
                       cret2.val_type
                   in
                   let t_pfm = rename_val ~config ren t_y in
                   let c_pfm =
                     {
                       op_sig = ty.op_sig;
                       val_type = t_pfm;
                       temp_eff =
                         (if config.enable_temp_eff then
                            mk_temp_fresh ~config dom
                          else mk_temp_trivial ());
                       cont_eff = rename_cont ~config ren @@ Eff (y, c1, c2);
                     }
                   in
                   if false then
                     Debug.print
                     @@ lazy ("c_pfm: " ^ Rtype.str_of_comp ~config c_pfm);
                   let t_op =
                     (* ToDo *)
                     trd3
                     @@ of_args_ret ~config dom x_args t_args
                     @@ mk_rarrow x
                          (mk_rarrow y t_y c1 (mk_fresh_trivial_pred ()))
                          c2 (mk_fresh_trivial_pred ())
                   in
                   if false then
                     Debug.print
                     @@ lazy ("t_op: " ^ Rtype.str_of_val ~config t_op);
                   (t_op, c_pfm, t_pfm)
               | Sort.Pure ->
                   (* an answer-type-polymorphic call: an application of the
                      operation's entry [(x : T1) -> T2], whose result is
                      [T2[v/x]] with the context's signature and a pure
                      control effect (no answer types); the handler's
                      tail-resumptive clause supplies the value *)
                   let t_y = val_of_sort ~config ~refine:true dom' op_sort in
                   let t_pfm = rename_val ~config ren t_y in
                   let c_pfm =
                     {
                       op_sig = ty.op_sig;
                       val_type = t_pfm;
                       temp_eff =
                         (if config.enable_temp_eff then
                            mk_temp_fresh ~config dom
                          else mk_temp_trivial ());
                       cont_eff = Pure;
                     }
                   in
                   let t_op = trd3 @@ of_args_ret ~config dom x_args t_args t_y in
                   (t_op, c_pfm, t_pfm)
               | _ -> assert false
             in
             let t_op_o = ALMap.find_exn op_name (fst ty.op_sig) in
             if false then
               Debug.print @@ lazy ("t_op_o: " ^ Rtype.str_of_val ~config t_op_o);
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
                   match Env.look_up renv @@ Tvar (op_name ^ "_arm") with
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
               List.map (c_pfm :: (*ToDo:List.rev*) c_args) ~f:(fun c ->
                   (Pattern.PAny (sort_of_comp c), renv', c))
             in
             ( Set.Poly.union_list
                 [
                   constr_o;
                   cgen_subtype_val ~config renv' t_pfm ty.val_type;
                   cgen_subeff ~config renv' rev_comp_effs t_pfm ty;
                   constrs;
                 ],
               kind_map )

           method f_handling (next_b, c_b) (next_r, x_r, c_r) op_handlers
               kind_map maps renv ty =
             let c_b = Term.subst_triple maps c_b in
             let c_r = Term.subst_triple maps c_r in
             let names, kinds, nexts, clauses = List.unzip4 op_handlers in
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

             let renv_r = Env.set_ty renv x_r t_b in
             let c_r =
               let refine, dom_r = (true, Env.dep_args_of renv_r) in
               let temp, opsig, cont = (true, `Sort c_r.op_sig, c_r.cont_eff) in
               comp_of_sort ~config ~refine ~temp ~opsig ~cont dom_r
                 c_r.val_type
             in
             let constr_r, kind_map = next_r kind_map maps renv_r c_r in

             let (constrs, kind_map), t_ops =
               List.fold_right2_exn (List.zip_exn kinds nexts) clauses
                 ~init:((Set.Poly.empty, kind_map), [])
                 ~f:(fun
                     (kind, next)
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
                   match (kind : MBcgen.handler_type) with
                   | ATPHandler ->
                       (* a tail-resumptive clause [op(z, k) -> let x = N in
                          continue k x]: [N] is typed pure under [z : T1] and
                          the handling construct's own signature, and the
                          operation's entry is [(z : T1) -> T2] for [N]'s
                          value type [T2].  The continuation is not typed:
                          resuming it with [N]'s value continues the handled
                          computation, which the handled body's typing
                          already covers *)
                       let c =
                         let refine, dom = (true, Env.dep_args_of renv') in
                         comp_of_sort ~config ~refine ~temp:true
                           ~opsig:(`Refined ty.op_sig) ~cont:Sort.Pure dom
                           c0.val_type
                       in
                       let constrs', kind_map = next kind_map maps renv' c in
                       ( (Set.union constrs constrs', kind_map),
                         (trd3 @@ of_args_ret ~config [] x_args t_args c.val_type)
                         :: t_ops )
                   | ATMHandler | ExceptionHandler ->
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
                     ((* ToDo *) trd3
                     @@ of_args_ret ~config [] x_args t_args
                     @@ mk_rarrow k t_k c @@ mk_fresh_trivial_pred ())
                     :: t_ops ))
             in

             let constr_b, kind_map =
               let c_b =
                 {
                   op_sig =
                     (ALMap.of_alist_exn @@ List.zip_exn names t_ops, None);
                   val_type = t_b;
                   temp_eff =
                     (if config.Rtype.enable_temp_eff then
                        mk_temp_fresh ~config dom
                      else mk_temp_trivial ());
                   cont_eff = Eff (x_r, c_r, ty);
                 }
               in
               next_b kind_map maps renv c_b
             in

             (Set.Poly.union_list [ constr_b; constr_r; constrs ], kind_map)
        end)

  (** Refinement Type Optimization *)

  let cgen_dir_map ~is_up t =
    let open Rtype in
    let rec inner (d : Rtype.Assertion.direction) = function
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
    if is_up then inner Rtype.Assertion.DUp t else inner Rtype.Assertion.DDown t

  let cgen_fronts ~config ~is_up ?(renv = Rtype.Env.mk_empty ()) t :
      Rtype.Assertion.fronts =
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
                  | _ :: tl -> List.rev (Term.mk_var x (sort_of_val t) :: tl)
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
      (if is_up then Rtype.Assertion.DUp else Rtype.Assertion.DDown)
      (constr_of ~config renv) t

  (** Constraint Generation *)

  let _ = Compmisc.init_path ()

  let print_load_info str =
    Debug.print
    @@ lazy
         (sprintf "==================== processing %s ====================" str)

  (* The four [@@@...] annotations are parsed from a string, so a syntax error
     in one surfaced as an uncaught [RtypeParser.MenhirBasics.Error] with a
     stack trace and no indication of *which* annotation or *where* -- unlike
     the OCaml source itself, which reports through
     [LexingHelper.print_error_information].  This names the annotation and its
     position before re-raising. *)
  let parse_annotation ~what ~content parse =
    let lexbuf = Lexing.from_string content in
    try parse RtypeLexer.token lexbuf
    with e ->
      Printf.fprintf stderr "%s: syntax error in [@@@%s \"%s\"]\n"
        (LexingHelper.get_position_string lexbuf)
        what content;
      raise e

  let compiler_result_svar dtenv vb =
    let visited = Hash_set.Poly.create () in
    let rec result ty =
      let repr = Types.Transient_expr.repr ty in
      if Hash_set.mem visited repr.id then None
      else (
        Hash_set.add visited repr.id;
        match repr.desc with
        | Types.Tarrow (_, _, ret, _) -> result ret
        | Types.Tvar _
          when Types.get_level (Types.Transient_expr.type_expr repr)
               = Btype.generic_level -> (
            match MBcgen.sort_of_type_expr ~env:vb.vb_pat.pat_env dtenv ty with
            | Sort.SVar sv -> Some sv
            | _ -> None)
        | _ -> None)
    in
    result vb.vb_pat.pat_type

  (* A sort is independent of [sv] when its complete set of sort variables
     omits it. The traversal fails on a sort it does not know, which is read
     as dependence. *)
  let sort_independent sv sort =
    try not (Set.mem (Term.svs_of_sort sort) sv)
    with exn_ when not (Common.Timer.is_async exn_) -> false

  (* This deliberately small grammar makes the independence check complete
     without relying on the shallow Formula.svs_of collector: every variable,
     bound variable and predicate argument has its sort checked, and the only
     interpreted symbols admitted are integer/real literals, arithmetic,
     conditionals, embedded formulas and the comparison predicates, none of
     which carries a sort of its own. Anything else is refused. *)
  let prefix_constraint_independent sv pvs =
    let scalar = sort_independent sv in
    let rec term = function
      | Term.Var (_, sort, _) -> scalar sort
      | Term.FunApp ((T_int.Int _ | T_real.Real _), [], _) -> true
      | Term.FunApp
          ( ( T_int.Neg | T_int.Abs | T_int.Add | T_int.Sub | T_int.Mul
            | T_int.Div _ | T_int.Rem _ | T_int.Power | T_real.RNeg
            | T_real.RAbs | T_real.RAdd | T_real.RSub | T_real.RMul
            | T_real.RDiv | T_real.RPower | T_bool.IfThenElse ),
            args,
            _ ) ->
          List.for_all args ~f:term
      | Term.FunApp (T_bool.Formula phi, [], _) -> formula phi
      (* Constructors, selectors and reference operations carry sorts; the
         sorts are checked as completely as a variable's. *)
      | Term.FunApp
          ((T_tuple.TupleCons sorts | T_tuple.TupleSel (sorts, _)), args, _) ->
          List.for_all sorts ~f:scalar && List.for_all args ~f:term
      | Term.FunApp (T_dt.DTSel (_, dt, sort), args, _) ->
          scalar (T_dt.SDT dt) && scalar sort && List.for_all args ~f:term
      | Term.FunApp (T_dt.DTCons (_, sorts, dt), args, _) ->
          scalar (T_dt.SDT dt)
          && List.for_all sorts ~f:scalar
          && List.for_all args ~f:term
      | Term.FunApp ((T_ref.Ref sort | T_ref.Deref sort | T_ref.Update sort), args, _)
        ->
          scalar sort && List.for_all args ~f:term
      | _ -> false
    and formula = function
      | Formula.Atom ((Atom.True _ | Atom.False _), _) -> true
      | Formula.Atom (Atom.App (Predicate.Var (pv, sorts), args, _), _) ->
          (not (Set.mem pvs pv))
          && List.for_all sorts ~f:scalar
          && List.for_all args ~f:term
      | Formula.Atom
          ( Atom.App
              ( Predicate.Psym
                  ( T_bool.Eq | T_bool.Neq | T_int.Leq | T_int.Geq | T_int.Lt
                  | T_int.Gt | T_real.RLeq | T_real.RGeq | T_real.RLt
                  | T_real.RGt ),
                args,
                _ ),
            _ ) ->
          List.for_all args ~f:term
      | Formula.Atom
          ( Atom.App
              ( Predicate.Psym
                  (T_tuple.IsTuple sorts | T_tuple.NotIsTuple sorts),
                args,
                _ ),
            _ ) ->
          List.for_all sorts ~f:scalar && List.for_all args ~f:term
      | Formula.Atom
          ( Atom.App
              ( Predicate.Psym (T_dt.IsCons (_, dt) | T_dt.NotIsCons (_, dt)),
                args,
                _ ),
            _ ) ->
          scalar (T_dt.SDT dt) && List.for_all args ~f:term
      | Formula.UnaryOp (_, phi, _) -> formula phi
      | Formula.BinaryOp (_, phi1, phi2, _) -> formula phi1 && formula phi2
      | Formula.Bind (_, bounds, phi, _) ->
          List.for_all bounds ~f:(snd >> scalar) && formula phi
      | _ -> false
    in
    formula

  (* The candidate's own extracted bounds may be quantified together with its
     refinement predicates when each bound mentions only those predicates and
     predicates free in the context the candidate is checked against (the
     preceding environment, and in a group also the siblings' stored types);
     those stay unquantified and every instance shares them. A predicate of
     any other origin, such as an intermediate one elimination left, could
     not be given one meaning across instances, so it refuses. The
     candidate's predicates are fresh, so renaming them in a copy captures
     nothing; [Formula.pvs_of] and [Formula.rename_pvars] both enter embedded
     formulas, so the copy renames every occurrence this test sees. *)
  let own_bounds_over_own_predicates prefix_renv pvs constrs =
    let allowed = Set.union pvs (Rtype.Env.pvs_of prefix_renv) in
    Set.for_all constrs ~f:(fun phi ->
        Set.is_subset (Formula.pvs_of phi) ~of_:allowed)

  (* Whether the right-hand side of [vb] reads a name bound by the group
     [vbs]. Names are compared by their last component, so a qualified path
     or a local binder reusing a group name also counts, and a group with a
     member that is not a plain variable is answered [true]: the test errs
     towards [true], which only keeps a binding monomorphic. OCaml's own check
     on recursive definitions already rejects an application that reads a
     member; this test does not rely on it. *)
  let mentions_group_member vbs vb =
    let names =
      Set.Poly.of_list
      @@ List.filter_map vbs ~f:(fun vb ->
          match vb.vb_pat.pat_desc with
          | Tpat_var (_, name, _) -> Some name.txt
          | _ -> None)
    in
    let found = ref false in
    let iterator =
      {
        Tast_iterator.default_iterator with
        expr =
          (fun self expr ->
            (match expr.exp_desc with
            | Texp_ident (path, _, _) when Set.mem names (Path.last path) ->
                found := true
            | _ -> ());
            Tast_iterator.default_iterator.expr self expr);
      }
    in
    iterator.expr iterator vb.vb_expr;
    !found
    || List.exists vbs ~f:(fun vb ->
        match vb.vb_pat.pat_desc with Tpat_var _ -> false | _ -> true)

  (* An application can retain a compiler-generalized covariant result. Handle
     the top-level expectation case independent of the prefix constraints; keep
     weak arguments and environment predicates shared.

     [constrs] are the binding's own extracted bounds B. When B is nonempty it
     is put into the scheme, quantified over the binding's refinement
     predicates, so every use instantiates a fresh copy of the predicates
     together with B on the copy. The caller also keeps B in the enclosing
     problem on the original predicates, which no stored type mentions any
     longer: that copy is the obligation that some interpretation of the
     predicates satisfies B, so a definition whose bounds cannot hold is not
     turned into a vacuous scheme. The value is computed once and purely,
     and B is equivalent, for each interpretation of the predicates it keeps,
     to the existence of the eliminated intermediate ones (the property
     let-generalization of a syntactic function relies on too), so any
     interpretation satisfying B makes the definition's derivation valid and
     the one value has every instance type.

     A [let rec] binding is admitted when its right-hand side reads no name
     the group binds ([mentions_group_member]): its constraints are then
     generated exactly as for a nonrecursive binding, the member templates in
     scope being consulted by nothing it contains. *)
  let generalize_application_result ~config (envs : envs) is_rec vbs constrs
      renv =
    match (envs.mode, vbs) with
    | ( HFL_Expectation
          (Kind.Adm_expectation | Kind.Adm_probability | Kind.Adm_liberal),
        [ vb ] )
      when Map.is_empty !mu_preds && Map.is_empty !nu_preds
           && ((not is_rec) || not (mentions_group_member vbs vb)) -> (
        match (vb.vb_pat.pat_desc, vb.vb_expr.exp_desc) with
        | Tpat_var (_, name, _), Texp_apply _ -> (
            let key = Tvar name.txt in
            match
              (compiler_result_svar envs.dtenv vb, Rtype.Env.look_up renv key)
            with
            | Some compiler_sv, Some ty when Rtype.is_rarrow ty -> (
                let args, ret = Rtype.args_ret_of_val ty in
                match ret with
                | Rtype.RGeneral ([], Sort.SVar sv, _)
                  when Poly.(sv = compiler_sv)
                       && (not (Set.mem (Rtype.Env.svs_of envs.renv) sv))
                       && Set.for_all envs.constrs
                            ~f:
                              (prefix_constraint_independent sv
                                 (Rtype.pvs_of_val ty))
                       && own_bounds_over_own_predicates envs.renv
                            (Rtype.pvs_of_val ty) constrs
                       && List.for_all args ~f:(fun (_, arg) ->
                           not
                             (Set.mem
                                (Term.svs_of_sort (Rtype.sort_of_val arg))
                                sv)) ->
                    let generalized =
                      generalize ~config envs.renv
                        (Map.Poly.singleton key ty)
                        constrs
                      |> fun types -> Map.Poly.find_exn types key
                    in
                    let available, body = Rtype.let_type_poly generalized in
                    if Set.mem available sv then
                      Rtype.Env.set_ty renv key
                      @@ Rtype.mk_type_poly ~config (Set.Poly.singleton sv)
                      @@ Rtype.pure_comp_of_val ~config body
                    else renv
                | _ -> renv)
            | _ -> renv)
        | _ -> renv)
    | _ -> renv

  (* A sibling of a nonrecursive group may share weak argument ranks with the
     candidate, but not the result being generalized or its refinement
     predicates. Inspect every refinement formula as well as the value
     structure; rank collection alone does not inspect formulas inside a
     refinement. The test reads only the stored type, so it does not depend on
     the sibling's expression form. *)
  let application_sibling_independent ~config sv pvs ty =
    let scalar = sort_independent sv in
    (* A type or predicate quantifier of the sibling binds its own
       variables; the candidate's result rank and predicates must not be among
       them (they are fresh to the candidate, so this only fails on a
       malformed environment). The quantifier's bounds are formulas and are
       inspected below together with every other refinement formula. *)
    let rec value = function
      | Rtype.RGeneral (params, sort, _) ->
          scalar sort && List.for_all params ~f:value
      | Rtype.RTuple (elems, _) -> List.for_all elems ~f:value
      | Rtype.RRef (elem, _) -> value elem
      | Rtype.RArrow (_, arg, comp, _) ->
          value arg && Rtype.is_pure_comp ~config comp && value comp.val_type
      | Rtype.RPoly (svs, comp) ->
          (not (Set.mem svs sv))
          && Rtype.is_pure_comp ~config comp
          && value comp.val_type
      | Rtype.RForall (penv, _bounds, comp) ->
          (* A quantified predicate's signature is part of the type even when
             no formula applies the predicate, and rank collection does not
             see it, so every stored argument sort is checked. *)
          Set.are_disjoint (Map.Poly.key_set penv) pvs
          && Map.Poly.for_all penv ~f:(List.for_all ~f:scalar)
          && Rtype.is_pure_comp ~config comp
          && value comp.val_type
    in
    let independent = ref true in
    ignore
      (Rtype.map_formula_val ty ~f:(fun phi ->
           independent :=
             !independent && prefix_constraint_independent sv pvs phi;
           phi));
    value ty && !independent

  (* Compare map/set contents rather than their functional comparator records.
     An unsupported functional payload cannot certify exact retention. *)
  let retained_type_equal left right =
    let atom_equal left right = Poly.(left = right) in
    let pred_equal (x, phi) (y, psi) =
      atom_equal x y && atom_equal phi psi
    in
    let rec value left right =
      match left, right with
      | Rtype.RGeneral (xs, sort, p), Rtype.RGeneral (ys, sort', p') ->
          List.equal value xs ys && atom_equal sort sort' && pred_equal p p'
      | Rtype.RTuple (xs, p), Rtype.RTuple (ys, p') ->
          List.equal value xs ys && pred_equal p p'
      | Rtype.RRef (x, p), Rtype.RRef (y, p') -> value x y && pred_equal p p'
      | Rtype.RArrow (x, arg, c, p), Rtype.RArrow (y, arg', c', p') ->
          atom_equal x y && value arg arg' && comp c c' && pred_equal p p'
      | Rtype.RForall (penv, bounds, c), Rtype.RForall (penv', bounds', c') ->
          Map.Poly.equal atom_equal penv penv'
          && Set.equal bounds bounds' && comp c c'
      | Rtype.RPoly (svs, c), Rtype.RPoly (svs', c') ->
          Set.equal svs svs' && comp c c'
      | _ -> false
    and comp left right =
      let ops, row = left.Rtype.op_sig in
      let ops', row' = right.Rtype.op_sig in
      List.equal
        (fun (name, ty) (name', ty') -> String.equal name name' && value ty ty')
        (ALMap.to_alist ops) (ALMap.to_alist ops')
      && atom_equal row row'
      && value left.val_type right.val_type
      && pred_equal (fst left.temp_eff) (fst right.temp_eff)
      && pred_equal (snd left.temp_eff) (snd right.temp_eff)
      && control left.cont_eff right.cont_eff
    and control left right =
      match left, right with
      | Rtype.Pure, Rtype.Pure -> true
      | Rtype.EVar x, Rtype.EVar y -> atom_equal x y
      | Rtype.Eff (x, c1, c2), Rtype.Eff (y, d1, d2) ->
          atom_equal x y && comp c1 d1 && comp c2 d2
      | _ -> false
    in
    try value left right
    with Invalid_argument message when String.equal message "compare: functional value" -> false

  (* Keep extracted ownership: sibling bounds stay in the enclosing problem.
     In a nonrecursive group the constraints of each binding are generated
     from that binding's expression alone, in the environment preceding the
     group, so they are exactly that binding's obligations whatever its
     expression form (application, function, alias, conditional, local let).
     A sibling therefore qualifies when its stored type and its own bounds
     are independent of the candidate rank and predicates; the candidate's
     own bounds go into its scheme under the conditions of
     [generalize_application_result]. Shadowed scalar or function values require
     preserved old types and no ambiguous old-name constraint references;
     dependent prior types must retain their renamed identities. The
     candidate may itself shadow under the same conditions: generalization
     changes only the candidate's new type, and the old value stays at its
     retained name. Effectful siblings remain excluded.

     In a [let rec] group the same holds for a candidate whose right-hand
     side reads no member: each member's constraints are generated from its
     own expression in the environment preceding the group plus the member
     templates, and the candidate's expression consults none of them. A
     member that calls the candidate does mention its predicates (and may
     share its result rank), and is refused by the independence test like
     any dependent sibling. Shadowing inside a recursive group is not
     admitted. *)
  let generalize_application_group ~config (envs : envs) is_rec vbs constrss
      shadow_map renv =
    (* The expression form of a sibling does not matter (see above), except
       that a local alias must name a binding of the preceding environment; a
       well-typed source always does, and the test keeps a malformed
       environment from being read as an independent one. *)
    let well_formed_sibling vb =
      match vb.vb_expr.exp_desc with
      | Texp_ident ((Path.Pident _ as path), _, _) ->
          Option.is_some (Rtype.Env.look_up envs.renv (Tvar (Path.name path)))
      | _ -> true
    in
    let key_of vb =
      match vb.vb_pat.pat_desc with
      | Tpat_var (_, name, _) -> Some (Tvar name.txt)
      | _ -> None
    in
    let scalar_sibling vb =
      match Option.bind (key_of vb) ~f:(Rtype.Env.look_up renv) with
      | Some
          (Rtype.RGeneral ([], (T_int.SInt | T_real.SReal | T_bool.SBool), _))
        ->
          true
      | _ -> false
    in
    let scalar_type = function
      | Rtype.RGeneral ([], (T_int.SInt | T_real.SReal | T_bool.SBool), _) -> true
      | _ -> false
    in
    (* A shadowed or shadowing value is a concrete scalar or a function
       value, possibly under its own type/predicate quantifiers. Whether a
       function value is independent of a particular candidate is decided per
       candidate below. *)
    let rec shadow_shape = function
      | Rtype.RArrow _ -> true
      | Rtype.RPoly (_, comp) | Rtype.RForall (_, _, comp) ->
          shadow_shape comp.Rtype.val_type
      | ty -> scalar_type ty
    in
    let group_keys = List.filter_map vbs ~f:key_of |> Set.Poly.of_list in
    let shared = Set.inter group_keys (Map.Poly.key_set (fst envs.renv)) in
    let shadow_targets = Set.Poly.of_list (Map.Poly.data shadow_map) in
    let shadow_terms_independent =
      Set.is_empty shared
      ||
      let excludes_shadow phi =
        Set.are_disjoint shared (Formula.tvs_of phi)
      in
      Set.for_all envs.constrs ~f:excludes_shadow
      && List.for_all constrss ~f:(fun bounds ->
             Set.for_all bounds ~f:excludes_shadow)
      && Map.Poly.for_alli (fst envs.renv) ~f:(fun ~key ~data:ty ->
             let independent = ref true in
             ignore
               (Rtype.map_formula_val ty ~f:(fun phi ->
                    independent := !independent && excludes_shadow phi;
                    phi));
             !independent
             ||
             let retained_key =
               Option.value (Map.Poly.find shadow_map key) ~default:key
             in
             match Rtype.Env.look_up renv retained_key with
             | Some retained_ty ->
                 retained_type_equal retained_ty (Rtype.rename_val ~config shadow_map ty)
             | None -> false)
    in
    let scalar_shadows_preserved =
      shadow_terms_independent
      && Set.equal shared (Map.Poly.key_set shadow_map)
      && Set.length shadow_targets = Map.Poly.length shadow_map
      && Set.are_disjoint shadow_targets
           (Set.union group_keys (Map.Poly.key_set (fst envs.renv)))
      && Map.Poly.for_alli shadow_map ~f:(fun ~key ~data:old_key ->
             match
               ( Rtype.Env.look_up envs.renv key,
                 Rtype.Env.look_up renv key,
                 Rtype.Env.look_up renv old_key )
             with
             | Some old_ty, Some new_ty, Some retained_ty ->
                 shadow_shape old_ty && shadow_shape new_ty
                 && retained_type_equal retained_ty (Rtype.rename_val ~config shadow_map old_ty)
             | _ -> false)
    in
    if
      (is_rec && not (Map.Poly.is_empty shadow_map && Set.is_empty shared))
      || List.length vbs < 2
      || List.length vbs <> List.length constrss
      || not scalar_shadows_preserved
      || (not (Set.is_empty (snd renv)))
      || not
           (List.for_all vbs ~f:(fun vb ->
                match key_of vb with
                | Some key ->
                    Option.is_none (Rtype.Env.look_up envs.renv key)
                    || Map.Poly.mem shadow_map key
                | None -> false))
    then renv
    else
      List.foldi (List.zip_exn vbs constrss) ~init:renv
        ~f:(fun index acc (vb, own_constrs) ->
          let candidate_key = key_of vb in
          if
            Option.is_some candidate_key
            && ((not is_rec) || not (mentions_group_member vbs vb))
            && (match
                  ( compiler_result_svar envs.dtenv vb,
                    Option.bind candidate_key ~f:(Rtype.Env.look_up renv) )
                with
               | Some sv, Some ty ->
                   (* The shadowed values stay in the environment under their
                      retained names; a function value among them must be
                      independent of the candidate exactly as a sibling is. *)
                   Map.Poly.for_alli shadow_map ~f:(fun ~key ~data:_ ->
                       match Rtype.Env.look_up envs.renv key with
                       | Some old_ty ->
                           scalar_type old_ty
                           || application_sibling_independent ~config sv
                                (Rtype.pvs_of_val ty) old_ty
                       | None -> false)
               | _ -> false)
            && List.for_alli vbs ~f:(fun other_index other ->
                index = other_index || scalar_sibling other
                ||
                match
                  ( compiler_result_svar envs.dtenv vb,
                    Option.bind (key_of vb) ~f:(Rtype.Env.look_up renv),
                    Option.bind (key_of other) ~f:(Rtype.Env.look_up renv) )
                with
                | Some sv, Some ty, Some sibling_ty ->
                    well_formed_sibling other
                    && Set.for_all (List.nth_exn constrss other_index)
                      ~f:(prefix_constraint_independent sv (Rtype.pvs_of_val ty))
                    && application_sibling_independent ~config sv
                         (Rtype.pvs_of_val ty) sibling_ty
                | _ -> false)
          then
            let context =
              Rtype.Env.remove renv (Option.value_exn (key_of vb))
            in
            generalize_application_result ~config
              {
                envs with
                renv = context;
                (* The siblings' bounds stay prefix constraints of the
                   candidate and must exclude its rank and predicates; its
                   own bounds are the scheme's (see
                   [generalize_application_result]). *)
                constrs =
                  Set.union envs.constrs
                    (Set.Poly.union_list
                       (List.filteri constrss ~f:(fun other_index _ ->
                            other_index <> index)));
              }
              false [ vb ] own_constrs acc
          else acc)

  (* the string an attribute carries, [[@@@name "content"]]: the payload is
     typed as an OCaml structure and its last item must be a string constant *)
  let attr_string_content (attr : Parsetree.attribute) =
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

  (** Functors verified against refinement-typed signatures.

      A functor [module F (X : S) = struct ... end] is verified once, for every
      module [X] that implements [S] and satisfies its contract: the body's
      problem quantifies universally over [S]'s abstract types and value
      members, and every unknown of the body may depend on those members and
      on nothing else -- the Henkin reading of a parameter bundle, which is
      what makes the problem a dependency-quantified one (DQpCSP; DQCHC when
      Horn).  The translation, member by member:
      - an abstract type [type t] of [S] is a universally quantified sort, the
        sort variable [X.t] (rigid: no step instantiates it);
      - a value member [val v : s1 -> ... -> sn -> s] is a universally
        quantified function, the term variable [X/v] of sort
        [Array s1 (... (Array sn s))] ([s] when [n = 0]), and the program
        variable [X.v] the body refers to is given the type
        [(x1:s1) -> ... -> (xn:sn) -> {r:s | r = X/v[x1]...[xn]}] -- a member
        is a pure total function of the bundle, so its result is the
        universal applied to its arguments;
      - the signature's contract [[@@contract "phi"]] (an SMT-LIB2 formula
        over the member and type names) is a premise of every clause of the
        body's problems;
      - every unknown of a body problem takes the members, in declaration
        order, as leading arguments (its dependency set is the whole bundle).
      The members' names are kept apart from the program variables ([X/v]
      against [X.v]) because the two have different sorts: a refinement may
      mention a program variable of base type, and one name at two sorts would
      not type.  The body's definitions are local to the functor; an
      application [F (M)] is not translated (it is refused). *)

  type modtype_info = {
    mt_types : string list;  (** the abstract types, in declaration order *)
    mt_vals : (string * Types.type_expr) list;
        (** the value members, in declaration order *)
    mt_contract : string option;  (** an SMT-LIB2 formula over the members *)
  }

  (* module types declared so far, by name; reset by [top_level] *)
  let modtypes : (string, modtype_info) Map.Poly.t ref = ref Map.Poly.empty

  type functor_ctx = {
    fc_sorts : Ident.svar list;  (** the universal sorts [X.t] *)
    fc_unis : sort_env_list;  (** the universal members [X/v], in order *)
    fc_contract : Formula.t option;  (** the contract over [fc_unis] *)
    fc_svmap : (Ident.svar, Sort.t) Map.Poly.t;
        (** the signature's type names to the universal sorts: an annotation
            in the body names an abstract type as the signature does ([t]),
            the annotation language having no path [X.t] *)
  }

  let modtype_of_decl (mtd : module_type_declaration) =
    let name = mtd.mtd_name.txt in
    let items =
      match mtd.mtd_type with
      | Some { mty_desc = Tmty_signature sg; _ } -> sg.sig_items
      | _ ->
          failwith
          @@ sprintf
               "module type %s: only a signature [sig ... end] is supported"
               name
    in
    let types, vals =
      List.partition_map items ~f:(fun item ->
          match item.sig_desc with
          | Tsig_type (_, decls) ->
              First
                (List.map decls ~f:(fun (td : type_declaration) ->
                     match (td.typ_kind, td.typ_manifest, td.typ_params) with
                     | Ttype_abstract, None, [] -> td.typ_name.txt
                     | _ ->
                         failwith
                         @@ sprintf
                              "module type %s: type %s must be abstract and \
                               without parameters"
                              name td.typ_name.txt))
          | Tsig_value vd -> Second [ (vd.val_name.txt, vd.val_desc.ctyp_type) ]
          | Tsig_attribute _ -> Second []
          | _ ->
              failwith
              @@ sprintf
                   "module type %s: only abstract types and values are \
                    supported as members"
                   name)
    in
    let contract =
      match
        List.filter mtd.mtd_attributes ~f:(fun at ->
            String.(at.attr_name.txt = "contract"))
      with
      | [] -> None
      | [ at ] -> Some (attr_string_content at)
      | _ -> failwith @@ sprintf "module type %s: more than one contract" name
    in
    ( name,
      {
        mt_types = List.concat types;
        mt_vals = List.concat vals;
        mt_contract = contract;
      } )

  (* The universal's name for member [v] of parameter [x].  The universals
     are variables of the body's refinement environment, and an unknown
     created there takes the environment's variables of base sort as its
     first arguments, in the order of their names; the leading [!] orders
     the universals before every other variable (no OCaml identifier and no
     name this generator draws starts with a character below it), so they
     are the unknown's leading arguments, in the order of their names --
     [dq_constraints] reads them there.  The constraints
     of a generalised definition are renamed apart clause by clause, so a
     universal is identified in a constraint by that position and not by
     its name. *)
  let universal_name x v = "!" ^ x ^ "." ^ v

  (* the curried argument sorts and the result sort of a member's sort *)
  let rec args_ret_of_member_sort = function
    | Sort.SArrow (s, c) ->
        let args, ret = args_ret_of_member_sort c.val_type in
        (s :: args, ret)
    | s -> ([], s)

  (* [(x1:s1) -> ... -> {r:s | r = u[x1]...[xn]}] for the universal [u] of
     array sort [usort] *)
  let member_rtype ~config sort u usort =
    let rec go xs = function
      | Sort.SArrow (s, c) ->
          let x = Rtype.mk_fresh_tvar_with "x" in
          Rtype.mk_rarrow x
            (Rtype.simple_val_of_sort ~config s)
            (Rtype.simple_comp_of_val ~config
               (go (xs @ [ Term.mk_var x s ]) c.val_type))
            (Rtype.mk_fresh_trivial_pred ())
      | s ->
          let r = Rtype.mk_fresh_tvar_with "v" in
          let app = T_array.mk_select_app (Term.mk_var u usort) xs in
          Rtype.mk_rbase s (r, Formula.eq (Term.mk_var r s) app)
    in
    go [] sort

  (* The context of a functor body with parameter [x : mt]: the universals,
     the contract over them, and the refinement type environment extended
     with the members. *)
  let dq_of_functor ~config (envs : envs) x (mt : modtype_info) =
    List.iter mt.mt_types ~f:(fun t ->
        if Option.is_some (DTEnv.look_up_dt envs.dtenv t) then
          failwith
          @@ sprintf
               "functor parameter %s: the abstract type %s shadows a declared \
                type of the same name"
               x t);
    let svmap =
      Map.Poly.of_alist_exn
      @@ List.map mt.mt_types ~f:(fun t ->
          (Ident.Svar t, Sort.SVar (Ident.Svar (x ^ "." ^ t))))
    in
    let members =
      List.map mt.mt_vals ~f:(fun (v, ty) ->
          let sort0 = MBcgen.sort_of_type_expr envs.dtenv ty in
          let sort = Term.subst_sorts_sort svmap sort0 in
          let args, ret = args_ret_of_member_sort sort in
          let usort s =
            if List.is_empty args then ret
            else T_array.of_arrow @@ Sort.mk_fun (s args @ [ ret ])
          in
          (v, sort, sort0, usort Fn.id, args, ret))
    in
    let fc_unis =
      (* in the order of their names, which is the order the environment
         lists them in and so the order of an unknown's leading arguments *)
      List.sort ~compare:(fun (a, _) (b, _) -> Stdlib.compare a b)
      @@ List.map members ~f:(fun (v, _, _, us, _, _) ->
          (Ident.Tvar (universal_name x v), us))
    in
    let fc_contract =
      Option.map mt.mt_contract ~f:(fun content ->
          (* read as SMT-LIB2 with the members as universal functions over the
             unprefixed sorts, then renamed into the functor's namespace *)
          let uni_sort =
            Set.Poly.of_list
            @@ List.map mt.mt_types ~f:(fun t -> Sort.SVar (Ident.Svar t))
          in
          let uni_senv =
            Map.Poly.of_alist_exn
            @@ List.map members ~f:(fun (v, _, sort0, _, _, _) ->
                let args, ret = args_ret_of_member_sort sort0 in
                ( Ident.Tvar v,
                  if List.is_empty args then ret
                  else T_array.of_arrow @@ Sort.mk_fun (args @ [ ret ]) ))
          in
          let phis, _ =
            SMT.Smtlib2.from_string ~print:Debug.print ~inline:true ~uni_sort
              ~uni_senv ~dtenv:envs.dtenv
              (sprintf "(assert %s)" content)
          in
          let phi =
            Formula.and_of
            @@ List.map phis
                 ~f:
                   (Typeinf.typeinf_formula ~print:Debug.print
                      ~rigid:(SMT.Smtlib2.rigid_of uni_sort) ~default:None)
          in
          let ren =
            Map.Poly.of_alist_exn
            @@ List.map members ~f:(fun (v, _, _, _, _, _) ->
                (Ident.Tvar v, Ident.Tvar (universal_name x v)))
          in
          Formula.subst_sorts svmap @@ Formula.rename ren phi)
    in
    let bind renv x ty =
      fst
      @@ Rtype.Env.update_with ~config renv
      @@ Rtype.Env.singleton_ty x ty
    in
    let renv =
      (* the universals first, as variables of the environment: every
         refinement unknown created in the body then takes them as its
         leading arguments (see [universal_name]) *)
      List.fold fc_unis ~init:envs.renv ~f:(fun renv (u, us) ->
          bind renv u (Rtype.simple_val_of_sort ~config us))
    in
    let renv =
      List.fold members ~init:renv ~f:(fun renv (v, sort, _, us, args, _) ->
          let pv = Ident.Tvar (x ^ "." ^ v)
          and u = Ident.Tvar (universal_name x v) in
          if List.is_empty args then
            (* a member of base type is a variable of the environment, whose
               refinement reaches a constraint as a fact of the environment
               (a refinement on the binding alone is not assumed where the
               variable is used) *)
            Rtype.Env.add_phi
              (bind renv pv (Rtype.simple_val_of_sort ~config sort))
              (Formula.eq (Term.mk_var pv sort) (Term.mk_var u us))
          else bind renv pv (member_rtype ~config sort u us))
    in
    ( { fc_sorts = Map.Poly.data svmap |> List.map ~f:(function
          | Sort.SVar sv -> sv | _ -> assert false);
        fc_unis; fc_contract; fc_svmap = svmap },
      renv )

  (* The constraints of a functor body's problem in the form the SMT-LIB2
     reader gives a dependency-quantified problem: every unknown (every
     predicate variable but the fixpoint predicates [bpvs]) takes the
     universals as its leading arguments, every constraint names them by
     their global names, and the contract is a premise of every constraint.
     Returns the constraints and the dependency map.

     The leading arguments are there already ([universal_name]); a
     constraint copied from a generalised definition names them by
     clause-local variables, which are renamed to the global names here.
     Within one constraint the renaming is consistent: each occurrence came
     from the one universal.  An unknown whose application does not start
     with variables of the universals' sorts was not created in the body,
     and the problem is refused rather than given a wrong dependency.

     Adding the premise to a constraint that does not mention a member
     changes nothing when the contract is satisfiable, since the constraint
     must then hold for an interpretation satisfying it; one that does
     mention a member is required exactly for the bundles the signature
     admits, which is the question asked. *)
  let dq_constraints ctx bpvs constrs =
    let k = List.length ctx.fc_unis in
    let unis = Array.of_list ctx.fc_unis in
    let is_unknown pvar = not (Set.mem bpvs pvar) in
    let leading pvar args =
      let fail () =
        failwith
        @@ sprintf
             "[functor] the unknown %s does not take the functor's members as \
              its leading arguments: %s"
             (Ident.name_of_pvar pvar)
             (String.concat_map_list ~sep:", " args ~f:(fun t ->
                  Term.str_of t ^ " : " ^ Term.str_of_sort (Term.sort_of t)))
      in
      if List.length args < k then fail ();
      List.mapi (List.take args k) ~f:(fun i t ->
          match t with
          | Term.Var (y, s, _) when Stdlib.(s = snd unis.(i)) -> (y, fst unis.(i))
          | _ -> fail ())
    in
    let constrs =
      Set.Poly.map constrs ~f:(fun phi ->
          let pos, neg = Formula.atoms_of phi in
          let ren =
            Set.fold (Set.union pos neg) ~init:Map.Poly.empty ~f:(fun ren atom ->
                match atom with
                | Atom.App (Predicate.Var (pvar, _), args, _) when is_unknown pvar
                  ->
                    List.fold (leading pvar args) ~init:ren ~f:(fun ren (y, u) ->
                        match Map.Poly.find ren y with
                        | Some u' when Stdlib.(u <> u') ->
                            failwith
                              "[functor] one variable stands for two members"
                        | _ -> Map.Poly.set ren ~key:y ~data:u)
                | _ -> ren)
          in
          let ren = Map.Poly.filteri ren ~f:(fun ~key ~data -> Stdlib.(key <> data)) in
          let phi = if Map.Poly.is_empty ren then phi else Formula.rename ren phi in
          match ctx.fc_contract with
          | None -> phi
          | Some a -> Formula.mk_imply a phi)
    in
    let penv =
      Set.Poly.union_list @@ Set.to_list
      @@ Set.Poly.map constrs ~f:(Formula.pred_sort_env_of ~bpvs)
    in
    let dep_map =
      Map.of_set_exn
      @@ Set.Poly.map penv ~f:(fun (pvar, _) ->
          (Ident.pvar_to_tvar pvar, ctx.fc_unis))
    in
    (constrs, dep_map)

  (* the attributes of the OCaml compiler, which RCaml leaves to it *)
  (* ---- Effect polymorphism of top-level bindings ----
     A top-level binding's stored type has every effect and row variable
     defaulted ([MBcsol.solve] grounds them), so a later item that applies a
     top-level function to an argument that performs an operation or raises
     meets a pure parameter and has no effect typing.  When, and only when,
     an item's typing without effect polymorphism fails, the item is typed
     again with every occurrence of an earlier binding that has an effect
     scheme read as a fresh instance of it ([instance_of_scheme]); the
     binding's refinement derivation is generated again for each such
     occurrence, under the instance's solution.  An item that types without
     schemes is therefore typed exactly as it would be without this
     mechanism.  Reading one evaluation of a binding as several, one per
     occurrence, is sound for a value that performs no operation when bound
     (which the purity check of top-level items ensures) under the demonic
     reading of non-determinism the safety verdicts use; it is not offered
     in the expectation modes or for an [[@@@infer]] problem, where a copy
     would be optimised or measured separately. *)

  (* set when an instance of an effect scheme has been made in the file
     being read (reset per file by [top_level]) *)
  let eff_scheme_instances_made = ref false

  (* whether an expression carries a [[@copy l]] label anywhere: a second
     derivation of it would make a second copy under the same label *)
  let has_copy_label (e : expression) =
    let found = ref false in
    let iter =
      {
        Tast_iterator.default_iterator with
        expr =
          (fun self e ->
            if Option.is_some (MBcgen.copy_label_of_attrs e.exp_attributes)
            then found := true;
            Tast_iterator.default_iterator.expr self e);
      }
    in
    iter.expr iter e;
    !found

  (* [scheme_of_item ~envs ...] is the effect scheme of each name a typed
     top-level item binds, keyed by name, or nothing for an item that
     admits none.  An item admits schemes when the file is read in the
     ordinary mode outside a functor body, every binding's pattern is a
     variable, and no binding carries a copy label; a name gets a scheme
     when its template's sort is a function sort (a value of another sort
     has no effect position an instance could change). *)
  let scheme_of_item (envs : envs) ~is_rec ~vbs ~pats ~is_pures ~is_funs
      ~nexts ~templates ~extra_templates ~eff_constrs ~opsig_constrs ~ref_id
      ~maps =
    let admits =
      (match envs.mode with
      | OCaml -> true
      | HFL_Expectation _ | HFL_Bool -> false)
      && (not !in_functor_body)
      && List.for_all vbs ~f:(fun vb ->
          (match vb.vb_pat.pat_desc with Tpat_var _ -> true | _ -> false)
          && not (has_copy_label vb.vb_expr))
    in
    if not admits then []
    else
      List.filter_map (List.zip_exn vbs templates) ~f:(fun (vb, template) ->
          match vb.vb_pat.pat_desc with
          | Tpat_var (id, name, _)
            when Sort.is_arrow (Sort.mono_type_of template.Sort.val_type) ->
              Some
                ( Tvar name.txt,
                  {
                    sc_path = Path.Pident id;
                    sc_name = Tvar name.txt;
                    sc_is_rec = is_rec;
                    sc_vbs = vbs;
                    sc_pats = pats;
                    sc_is_pures = is_pures;
                    sc_is_funs = is_funs;
                    sc_nexts = nexts;
                    sc_templates = templates;
                    sc_template = template;
                    sc_extra_templates = extra_templates;
                    sc_eff_constrs = eff_constrs;
                    sc_opsig_constrs = opsig_constrs;
                    sc_ref_id = ref_id;
                    sc_maps = maps;
                    sc_renv = envs.renv;
                  } )
          | _ -> None)

  (* the scheme of the top-level binding an occurrence's path names, if it
     has one; a local binding of the same name has another identifier *)
  let scheme_at (envs : envs) (p : Path.t) =
    match Map.Poly.find envs.eff_schemes (Tvar (Path.name p)) with
    | Some sc when Path.same sc.sc_path p -> Some sc
    | _ -> None

  (* [instance_of_scheme ~config envs sc] makes one instance of the effect
     scheme [sc] at an occurrence of its bound name: a renaming [rho] of
     every sort, effect and row variable of the scheme's constraints,
     templates and recorded sort instantiations to fresh variables.  It
     returns
     - the bound name's sort under [rho], the recorded instantiations
       applied (so that none of their variables is instantiated again);
     - the scheme's effect and signature constraints under [rho], which join
       the occurrence's item and are solved with it;
     - the occurrence's phase-2 continuation;
     - the scheme's templates under [rho], which the caller passes to
       [MBcsol.solve] so that a variable they mention and no constraint
       does is defaulted, as the scheme's own item had it defaulted.
     The renamed instantiations are entered into [MBcgen.ref_id], as an
     ordinary occurrence's are, so that the occurrence item's solution
     covers them.

     Assumes the scheme's variables occur nowhere outside it: they were
     created by its item's traversal, and the environment that item was
     typed in is ground in effects and rows.

     The continuation, given the occurrence item's solution [sigma], types
     the scheme's item again: it runs the item's phase-2 continuations
     under [theta], which is [sigma] after [rho] on the renamed variables
     and the item's own solution on every other variable (a variable met
     only inside a continuation keeps the value it had), in the refinement
     environment the item was typed in.  The item is generated as a local
     binding (fresh predicate names, no universal-interface encoding of
     predicate polymorphism, whose records are global and would be made
     twice) and is not passed through the two generalisations of
     application results an ordinary top-level item gets, which only
     weakens the instance's type.  An instance whose computation is impure
     is refused.  The regenerated type of the bound name is then
     instantiated at the occurrence as an ordinary variable's stored type
     is, and the regenerated refinement constraints are returned with the
     occurrence's own, so that they join the using item's constraints.
     Each occurrence gets its own derivation: instances are not shared
     between occurrences with the same solved sort. *)
  let instance_of_scheme ~config (envs : envs) sc =
    let open Rtype in
    eff_scheme_instances_made := true;
    let all_templates = sc.sc_templates @ sc.sc_extra_templates in
    let conts =
      List.concat_map (Set.to_list sc.sc_eff_constrs) ~f:(fun (effs, eff) ->
          eff :: effs)
    in
    let opsigs =
      List.concat_map (Set.to_list sc.sc_opsig_constrs) ~f:(fun (o1, o2) ->
          [ o1; o2 ])
    in
    let ref_sorts = Map.Poly.data sc.sc_ref_id in
    let vars_of of_triple of_cont of_opsig of_sort =
      Set.Poly.union_list
      @@ List.map all_templates ~f:of_triple
      @ List.map conts ~f:of_cont
      @ List.map opsigs ~f:of_opsig
      @ List.map ref_sorts ~f:of_sort
    in
    let evs =
      vars_of Term.evs_of_triple Term.evs_of_cont Term.evs_of_opsig
        Term.evs_of_sort
    in
    let rvs =
      vars_of Term.rvs_of_triple Term.rvs_of_cont Term.rvs_of_opsig
        Term.rvs_of_sort
    in
    let svs =
      Set.union (Map.Poly.key_set sc.sc_ref_id)
      @@ vars_of Term.svs_of_triple Term.svs_of_cont Term.svs_of_opsig
           Term.svs_of_sort
    in
    let rho_e =
      Map.of_set_exn @@ Set.Poly.map evs ~f:(fun v -> (v, Sort.mk_fresh_evar ()))
    in
    let rho_s =
      Map.of_set_exn @@ Set.Poly.map svs ~f:(fun v -> (v, Sort.mk_fresh_svar ()))
    in
    let rho_o =
      Map.of_set_exn
      @@ Set.Poly.map rvs ~f:(fun v -> (v, Sort.mk_fresh_empty_open_opsig ()))
    in
    let rho = (rho_o, rho_s, rho_e) in
    let ref_id' =
      Map.Poly.of_alist_exn
      @@ List.map (Map.Poly.to_alist sc.sc_ref_id) ~f:(fun (sv, s) ->
          ( (match Map.Poly.find_exn rho_s sv with
            | Sort.SVar sv' -> sv'
            | _ -> assert false),
            Term.subst_sort rho s ))
    in
    (MBcgen.ref_id :=
       let stheta = Map.Poly.map ~f:(Term.subst_sorts_sort !MBcgen.ref_id) ref_id' in
       let ref_id =
         Map.Poly.map !MBcgen.ref_id ~f:(Term.subst_sorts_sort stheta)
       in
       Map.force_merge ref_id stheta);
    let x_sort =
      Term.subst_sorts_sort ref_id'
      @@ Term.subst_sort rho sc.sc_template.val_type
    in
    let eff_constrs =
      Set.Poly.map sc.sc_eff_constrs ~f:(fun (effs, eff) ->
          (List.map effs ~f:(Term.subst_cont rho), Term.subst_cont rho eff))
    in
    let opsig_constrs =
      Set.Poly.map sc.sc_opsig_constrs ~f:(fun (o1, o2) ->
          (Term.subst_opsig rho o1, Term.subst_opsig rho o2))
    in
    let templates = List.map all_templates ~f:(Term.subst_triple rho) in
    let next : cont =
     fun kind_map maps renv ty ->
      let theta =
        let m_o, m_s, m_e = sc.sc_maps in
        let over rho_map orig f =
          Map.Poly.fold rho_map ~init:orig ~f:(fun ~key ~data acc ->
              Map.Poly.set acc ~key ~data:(f data))
        in
        ( over rho_o m_o (Term.subst_opsig maps),
          over rho_s m_s (Term.subst_sort maps),
          over rho_e m_e (Term.subst_cont maps) )
      in
      let cs = List.map sc.sc_templates ~f:(Term.subst_triple theta) in
      let cs, _renv_bound, _adm_pvars, constrs', kind_map, renv_body, _, _ =
        cgen_let ~config OCaml ~is_top_level:false envs.fenv envs.dtenv
          sc.sc_is_rec sc.sc_pats
          (sc.sc_is_pures, sc.sc_is_funs, sc.sc_nexts, cs)
          kind_map theta sc.sc_renv
      in
      (match List.find cs ~f:(Fn.non @@ is_pure_comp ~config) with
      | None -> ()
      | Some c ->
          Common.Refusal.refuse
            "RCaml does not support an impure top-level computation: %s, at \
             an instance of %s's effect scheme"
            (str_of_comp ~config c) (name_of_tvar sc.sc_name));
      let xty =
        match Env.look_up renv_body sc.sc_name with
        | Some xty -> xty
        | None ->
            failwith
            @@ sprintf "[instance_of_scheme] %s not bound by its own item"
                 (name_of_tvar sc.sc_name)
      in
      let sort = Term.subst_sort maps x_sort in
      let xty0 = xty in
      let xty, constrs, kind_map =
        instantiate_val ~print:Debug.print ~config (Env.dep_args_of renv)
          kind_map
          (Map.Poly.empty, Map.Poly.empty)
          (xty, sort)
      in
      let kind_map = adm_kinds_at_instance OCaml ~xty0 ~xty kind_map in
      let xty = comp_of_term ~config (Term.mk_var sc.sc_name sort) xty in
      let kind_map =
        adm_kinds_at_subtype OCaml ~xty0:xty.val_type ~xty:ty.val_type kind_map
      in
      Debug.print
      @@ lazy
           (sprintf "[rcaml:scheme instance] %s : %s <: %s\n"
              (name_of_tvar sc.sc_name) (str_of_comp ~config xty)
              (str_of_comp ~config ty));
      ( Set.Poly.union_list
          [ constrs'; constrs; cgen_subtype_comp ~config renv xty ty ],
        kind_map )
    in
    (x_sort, eff_constrs, opsig_constrs, next, templates)

  let compiler_attributes =
    [ "warning"; "warnerror"; "alert"; "deprecated"; "inline"; "inlined";
      "unboxed"; "boxed"; "immediate"; "tail_mod_cons"; "unrolled";
      "specialise"; "specialised"; "local"; "poll"; "noalloc"; "untagged" ]

  (* the names of the unread attributes already reported (reset per file) *)
  let noticed_attributes = Hash_set.create (module String)

  (* Raised by [of_struct_item], only while [wrap_impure_toplevel] is set, at
     a top-level item whose computation may perform an operation: the item's
     location and the refusal to give if it cannot be wrapped.  Set and
     caught by [from_ml_file] alone, so any other caller of [top_level] or
     [top_level_aux] sees the refusal as before. *)
  exception Impure_toplevel of Location.t * string

  let wrap_impure_toplevel = ref false

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
                MBcgen.find_val_attrs ~config ~renv:envs.renv ~dtenv:envs.dtenv
                  ~attr_name:"annot_MB" vb.vb_attributes
              in
              let t_annot_opt =
                MBcgen.find_val_attrs ~config ~renv:envs.renv ~dtenv:envs.dtenv
                  ~attr_name:"annot" vb.vb_attributes
              in
              if
                List.exists vb.vb_attributes ~f:(fun at ->
                    String.(at.attr_name.txt = "annot_rty"))
                || Option.is_some t_annot_opt
              then
                failwith "rtype annotations on let-bindings are not supported";
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
        let senv = Rtype.Env.to_sort_env envs.renv in
        let senv_bounds =
          if is_rec then
            let pat_senvs = List.map defs (* assume distinct *) ~f:fst3 in
            Map.update_with_list (*shadowing*) (senv :: pat_senvs)
          else senv
        in
        let templates = List.map defs ~f:trd3 in
        (* Phase 1 of the item: the effect and signature constraints of its
           definitions, solved.  Without [with_schemes] every occurrence of
           an earlier top-level name has that name's stored sort; with it,
           an occurrence of a name that has an effect scheme is a fresh
           instance of the scheme.  Returns the solution (closed under its
           own substitutions), the phase-2 continuations, the constraints,
           the templates of the instances made, and the sort
           instantiations the traversal recorded; raises
           [MBcsol.Solve_failure] when the solver finds no typing. *)
        let phase1 ~with_schemes =
          let ref_id0 = !MBcgen.ref_id in
          let instance_templates = ref [] in
          let has_scheme, scheme_instance =
            if with_schemes then
              ( (fun p -> Option.is_some (scheme_at envs p)),
                fun p ->
                  let sc = Option.value_exn (scheme_at envs p) in
                  let x_sort, econstrs, oconstrs, next, tmpls =
                    instance_of_scheme ~config envs sc
                  in
                  instance_templates := tmpls @ !instance_templates;
                  (x_sort, econstrs, oconstrs, next) )
            else
              ( (fun _ -> false),
                fun p ->
                  failwith
                  @@ sprintf "[of_struct_item] no effect scheme for %s"
                       (Path.name p) )
          in
          let eff_constrss, opsig_constrss, next1s =
            List.unzip3
            @@ List.map defs ~f:(fun (_, expr, c) ->
                cgen_expr ~has_scheme ~scheme_instance ~config envs.mode
                  envs.fenv envs.dtenv senv_bounds expr c)
          in
          let eff_constrs = Set.Poly.union_list eff_constrss in
          let opsig_constrs = Set.Poly.union_list opsig_constrss in
          let ref_id_delta =
            Map.Poly.filter_keys !MBcgen.ref_id ~f:(fun sv ->
                not (Map.Poly.mem ref_id0 sv))
          in
          let omap, smap, emap =
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
            (* Unused function arguments may contain lifted effect/row variables
               absent from every constraint. Resolve those before storing the
               refinement, using the solver's existing defaults.  The
               templates of the instances made here are passed for the same
               reason. *)
            (* [MBcsol.solve] either returns a substitution under which every
               effect and operation-signature constraint holds or raises
               [Solve_failure].  Its search is heuristic, so a failure says
               that it found no typing, not that none exists.  The solver
               also stops, with the same exception, when only an effect
               variable below an impure effect (or an unsettled row bound) is
               left, a residual constraint that needs a search it does not
               make. *)
            let sol =
              MBcsol.solve
                ~templates:(templates @ !instance_templates)
                eff_constrs opsig_constrs
            in
            let stheta =
              let stheta =
                Map.Poly.map sol.stheta
                  ~f:(Term.subst_sorts_sort !MBcgen.ref_id)
              in
              let ref_id =
                Map.Poly.map !MBcgen.ref_id ~f:(Term.subst_sorts_sort stheta)
              in
              try Map.force_merge ref_id stheta
              with exn_ when not (Common.Timer.is_async exn_) ->
                failwith
                @@ sprintf "fail to force merge:\nref_id: %s\nstheta: %s"
                     (str_of_sort_subst Term.str_of_sort ref_id)
                     (str_of_sort_subst Term.str_of_sort stheta)
            in
            let maps = (sol.otheta, stheta, sol.etheta) in
            Debug.print (lazy "==== MB type inferred:");
            List.iter2_exn pats defs ~f:(fun pat (_, _, c) ->
                Debug.print
                @@ lazy
                     (Pattern.str_of pat ^ ": " ^ Term.str_of_triple
                    @@ Term.subst_triple maps c));
            maps
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
          ( (omap', smap', emap'),
            next1s,
            eff_constrs,
            opsig_constrs,
            !instance_templates,
            ref_id_delta )
        in
        (* Two shapes the solver cannot type without effect polymorphism:
           (1) a top-level function's parameters keep the control effects
           inferred from its own item, so a later item that applies it to an
           argument that performs an operation or raises fails to unify a
           pure computation with an effectful one (the same function bound
           inside the item that uses it is typed); this is what the second
           attempt, with effect schemes, addresses, and only for an item the
           first attempt cannot type, so that every item typed without
           schemes is typed as before; (2) a recursive function whose call
           to itself sits under its own handler, where the handler forwards
           an answer-type-modifying operation by performing it again: a row
           variable of the clause's signature is then bounded below by a
           signature that mentions it, and these signatures are finite (an
           operation every [perform] of which is [perform_atp] carries no
           answer types and does not have this shape).  A recursive group
           is monomorphic in its own body in either attempt: an occurrence
           of a group member inside the group is not an instance
           (polymorphic recursion over effects is not supported).  Without
           a typing no refinement constraint can be generated for this
           binding and no verdict follows, so the input is refused in words
           rather than crashing. *)
        let refuse_effects reason =
          Common.Refusal.refuse
            "the effects of %s are not supported: RCaml's effect type \
             inference found no typing (%s); it is incomplete: an earlier \
             top-level function bound to a variable is instantiated afresh \
             at each use (effect polymorphism) only on a second attempt \
             after a failed first one, and only in the ordinary mode, \
             outside a functor body and for items without a [@copy] label; \
             a recursive group is monomorphic in its own body; a recursive \
             function that calls itself under its own handler, which \
             forwards an answer-type-modifying operation by performing it \
             again, has no typing; and a program whose property is a \
             [@@@check_toplevel] automaton is EffCaml's input"
            (String.concat_map_list ~sep:", " pats ~f:Pattern.str_of)
            reason
        in
        let ( maps,
              next1s,
              eff_constrs,
              opsig_constrs,
              instance_templates,
              ref_id_delta ),
            with_schemes =
          match phase1 ~with_schemes:false with
          | res -> (res, false)
          | exception MBcsol.Solve_failure reason -> (
              let uses_scheme =
                List.exists vbs ~f:(fun vb ->
                    let found = ref false in
                    let iter =
                      {
                        Tast_iterator.default_iterator with
                        expr =
                          (fun self e ->
                            (match e.exp_desc with
                            | Texp_ident (p, _, _)
                              when Option.is_some (scheme_at envs p) ->
                                found := true
                            | _ -> ());
                            Tast_iterator.default_iterator.expr self e);
                      }
                    in
                    iter.expr iter vb.vb_expr;
                    !found)
              in
              if not uses_scheme then refuse_effects reason
              else
                match envs.mode with
                | HFL_Expectation _ ->
                    refuse_effects
                      (reason
                     ^ "; effect polymorphism of top-level bindings is \
                        offered in the ordinary mode only, since reading \
                        one binding as one copy per use is not \
                        meaning-preserving for an expectation")
                | HFL_Bool ->
                    refuse_effects
                      (reason
                     ^ "; effect polymorphism of top-level bindings is \
                        offered in the ordinary mode only: reading one \
                        binding as one copy per use has not been argued \
                        meaning-preserving for a lambda-HFL term whose \
                        bindings are fixed points")
                | OCaml when !in_functor_body ->
                    refuse_effects
                      (reason
                     ^ "; effect polymorphism of top-level bindings is not \
                        offered inside a functor body")
                | OCaml when List.exists vbs ~f:(fun vb -> has_copy_label vb.vb_expr) ->
                    refuse_effects
                      (reason
                     ^ "; effect polymorphism of top-level bindings is not \
                        offered for an item with a [@copy] label")
                | OCaml -> (
                    match phase1 ~with_schemes:true with
                    | res -> (res, true)
                    | exception MBcsol.Solve_failure reason' ->
                        refuse_effects
                          (sprintf
                             "%s; with effect polymorphism of the earlier \
                              top-level bindings: %s%s"
                             reason reason'
                             (if is_rec then
                                "; a recursive group is typed \
                                 monomorphically in its own body \
                                 (polymorphic recursion over effects is not \
                                 supported)"
                              else ""))
                    | exception exn_
                      when not
                             (Common.Timer.is_async exn_
                             ||
                             match exn_ with
                             | Common.Refusal.Refused _ -> true
                             | _ -> false) ->
                        refuse_effects
                          (sprintf
                             "%s; with effect polymorphism of the earlier \
                              top-level bindings, the effect typing failed: \
                              %s"
                             reason (Exn.to_string exn_))))
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
              shadow_map,
              definition_constrss ) =
          let run () =
            cgen_let ~config envs.mode ~is_top_level:true envs.fenv envs.dtenv
              is_rec pats
              (is_pures, is_funs, next1s, cs)
              envs.kind_map maps envs.renv
          in
          if not with_schemes then run ()
          else
            (* an item typed with effect schemes that the refinement
               generation then fails on is refused as one without a typing:
               its instances' derivations are new, and their failure must
               not be read as a failure of the input *)
            try run ()
            with
            | exn_
            when not
                   (Common.Timer.is_async exn_
                   ||
                   match exn_ with
                   | Common.Refusal.Refused _ -> true
                   | _ -> false)
            ->
              refuse_effects
                (sprintf
                   "an effect typing was found with effect polymorphism of \
                    the earlier top-level bindings, but its refinement \
                    generation failed: %s"
                   (Exn.to_string exn_))
        in
        match List.find cs ~f:(Fn.non @@ Rtype.is_pure_comp ~config) with
        | None ->
            let eff_schemes =
              List.fold
                (scheme_of_item envs ~is_rec ~vbs ~pats ~is_pures ~is_funs
                   ~nexts:next1s ~templates ~extra_templates:instance_templates
                   ~eff_constrs ~opsig_constrs ~ref_id:ref_id_delta ~maps)
                ~init:envs.eff_schemes
                ~f:(fun acc (x, sc) -> Map.Poly.set acc ~key:x ~data:sc)
            in
            let renv_body =
              generalize_application_result ~config envs is_rec vbs constrs'
                renv_body
              |> generalize_application_group ~config envs is_rec vbs
                   definition_constrss shadow_map
            in
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
                eff_schemes;
              },
              Skip )
        | Some c ->
            (* A top-level binding whose computation may perform an operation
               or raise has no handler around it.  When [from_ml_file] reads
               such an operation as a failure, it is asked to wrap this item
               in a failing handler and read the file again: that applies
               only to an item of the file's own structure (not of a functor
               body) whose operation signature is not empty.  An item whose
               impurity is only a change of answer type (a [shift] outside
               every [reset]) or a temporal effect, an item the handler
               cannot be written around, and an item already wrapped that is
               still impure are refused: RCaml gives them no meaning. *)
            let msg =
              sprintf "RCaml does not support an impure top-level computation: %s"
                (Rtype.str_of_comp ~config c)
            in
            if
              !wrap_impure_toplevel && (not !in_functor_body)
              && not (Rtype.is_pure_opsig c.op_sig)
            then raise (Impure_toplevel (item.str_loc, msg))
            else Common.Refusal.refuse "%s" msg)
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
        (* A declaration hides every earlier datatype of a name it declares,
           the built-in [list], [option] and [unit] included: in OCaml a later
           [type t = ...] is a new type, and [t] in the code (and in the
           refinement annotations) after it denotes the new one.  The
           environments map a name to one datatype, so the earlier definition
           leaves both the environment threaded through the file and the
           global one before the new one enters; merging the two would refuse
           them as duplicate definitions, which is how a file declaring its
           own [type list = Nil | Cons of int * list] was refused.  The new
           group is built against the environment without the hidden
           definitions, since a name it declares refers to itself inside it
           (the declaration's [rec] flag is not read).  OCaml refuses two
           declarations of one type name in a structure, so what is hidden is
           a built-in; the built-in reached after the hiding anyway (a list
           written with [[]] and [::] beside a file's own [list]) is refused,
           since types are looked up by name.  Values made before the
           declaration keep the hidden definition in their sorts; a solver
           query mixing the two definitions is refused, not misread
           ([shadow_dtenv]). *)
        let declared =
          Set.Poly.of_list @@ List.map types ~f:(fun ty -> ty.typ_name.txt)
        in
        let visible = DTEnv.hide envs.dtenv declared in
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
          List.fold_left ustypes ~init:visible ~f:(fun dtenv ty ->
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
                      conses = List.map tds ~f:(MBcgen.cons_of dtenv datatypes);
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
        shadow_dtenv declared dtenv';
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
        let content = attr_string_content attr        in
        match attr.Parsetree.attr_name.txt with
        | "mode" ->
            Debug.print @@ lazy ("[mode] " ^ content);
            if !eff_scheme_instances_made then
              Common.Refusal.refuse
                "[@@@mode] after a use of effect polymorphism of top-level \
                 bindings is not supported: such a use is typed as a copy of \
                 the binding, which is meaning-preserving in the ordinary \
                 mode only";
            ( {
                envs with
                mode =
                  (match content with
                  | "hfl_prop_as_expectation" ->
                      HFL_Expectation Kind.Adm_expectation
                  (* the two [0, 1] instances are read once [hfl_prescan]
                     has checked the term is a sub-probability term *)
                  | "hfl_prop_as_probability" ->
                      HFL_Expectation Kind.Adm_probability
                  | "hfl_prop_as_liberal_probability" ->
                      HFL_Expectation Kind.Adm_liberal
                  | "hfl_prop_as_conditional_expectation" ->
                      HFL_Expectation Kind.Adm_conditional
                  | "hfl_prop_as_bool" -> HFL_Bool
                  | _ -> OCaml);
              },
              Skip )
        | "smtlib2" ->
            (* e.g., [@@@smtlib2 "some smtlib2 code"] *)
            let constrs', envs' (*ToDo: uni_senv is ignored*) =
              SMT.Smtlib2.from_string ~print:Debug.print ~inline:false (*ToDo*)
                ~exi_senv:envs.exi_senv ~kind_map:envs.kind_map ~fenv:envs.fenv
                ~lifted_universals:envs.lifted_universals
                ~dtenv:envs.dtenv content
            in
            let constrs' =
              Set.Poly.map
                ~f:(Typeinf.typeinf_formula ~print:Debug.print ~default:None)
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
                lifted_universals = envs'.lifted_universals;
                dtenv = envs'.dtenv;
              },
              Skip )
        | "constraints" ->
            let constrs' =
              Rtype.cgen_config := config;
              Rtype.renv_ref := envs.renv;
              set_dtenv envs.dtenv;
              Set.Poly.map
                ~f:(Typeinf.typeinf_formula ~print:Debug.print ~default:None)
              @@ Set.Poly.of_list
              @@ parse_annotation ~what:"constraints" ~content
                   RtypeParser.constraints
            in
            ({ envs with constrs = Set.union envs.constrs constrs' }, Skip)
        | "rtype" ->
            (* e.g. [@@@rtype "main :: (x:{v : int | v > 0}) -> unit"] *)
            let renv0 =
              Rtype.cgen_config := config;
              Rtype.renv_ref := envs.renv;
              set_dtenv envs.dtenv;
              parse_annotation ~what:"rtype" ~content RtypeParser.val_ty_env
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
              parse_annotation ~what:"assert" ~content RtypeParser.assertions
            in
            (envs, Check assertions)
        | "lemma" ->
            (* collected by [top_level] before the items are read *)
            (envs, Skip)
        | "property" | "chc" ->
            (* read by [top_level_aux], which makes its problem *)
            (envs, Skip)
        | "infer" | "optimize" | "infer_optimized_type" ->
            Debug.print @@ lazy ("[infer] " ^ content);
            let problems =
              Rtype.cgen_config := config;
              Rtype.renv_ref := envs.renv;
              set_dtenv envs.dtenv;
              parse_annotation ~what:"infer" ~content RtypeParser.opt_problems
            in
            (envs, Infer problems)
        | name ->
            (* An attribute RCaml does not read is ignored, but said once per
               name on stderr: a file whose property lives in such an
               attribute (another tool's annotation) would otherwise be read
               as a file without a property and print nothing.  The
               compiler's own attributes are not RCaml's to read and pass
               silently. *)
            if
              not
                (String.is_prefix name ~prefix:"ocaml."
                || List.mem compiler_attributes name ~equal:String.equal
                || Hash_set.mem noticed_attributes name)
            then (
              Hash_set.add noticed_attributes name;
              Out_channel.eprintf
                "[RCaml] attribute [@@@%s] is not read by RCaml and is \
                 ignored\n%!"
                name);
            (envs, Skip))

  (* The problem of an assertion when a definition was checked once
     ([pp_universal_generalize]): the universals are recorded with every
     unknown's dependency set, a [P'] its definition's universals and every
     other unknown none (it does not take them as arguments), so the printer
     states each.  A premise [forall a. X(a) => K(a)] is skolemised into a
     functional predicate.  Its witness must see the universal [X]: it is a
     point of [X] outside [K], not an element of [K]'s extension, so the
     dependency sets are not given to the skolemisation, whose restriction
     to them is meant for the witness of a head existential (none occurs
     here: a definition with a quantified constraint is copied). *)
  let pp_pcsp_of envs unis constrs =
    let constrs = Set.union envs.constrs constrs in
    let bpvs = Set.Poly.of_list @@ Map.Poly.(keys !mu_preds @ keys !nu_preds) in
    let dep_map =
      Set.fold
        (Set.concat_map constrs ~f:(Formula.pred_sort_env_of ~bpvs))
        ~init:Map.Poly.empty
        ~f:(fun acc (pv, _) ->
          Map.Poly.set acc ~key:(Ident.pvar_to_tvar pv)
            ~data:(Option.value ~default:[] (Map.Poly.find !pp_deps pv)))
    in
    pcsp_of ~skolem_pred:true ~witness_deps:false
      ~dq:(Some ([], unis, dep_map))
      { envs with constrs = Set.Poly.empty }
      constrs

  (* whether the file being read stated an assertion (reset per file) *)
  let has_assertion = ref false

  (* The [[@@@lemma "..."]] annotations of the file being read, in file order
     (reset per file; collected before the items are read, so a lemma counts
     wherever it stands in the file). *)
  let lemma_annotations : string list ref = ref []

  (* ---- The application notation of [[@@@lemma]] and [[@@@property]] ----

     A lemma or a property is a first-order formula about the file's top-level
     functions, written in OCaml's expression syntax:
       [forall x1 ... xk. e1 => ... => em]
     each [ei] a Boolean expression built from variables, integer literals,
     [true] and [false], datatype constructors, the integer operators
     [+ - * / mod] and unary minus, the comparisons [= <> < <= > >=], [&&],
     [||], [not], [=>], [<=>], applications [f a1 ... an] of a function [f]
     defined at the top level of the file to exactly its [n] arguments, the
     same with [f] replaced by a copy name [f@lbl] or [f@def], and argument
     atoms [called f@lbl a1 ... an].  [=>] binds more loosely than [||] and
     associates to the right; [<=>] binds like [=].  The [forall] prefix is
     optional: with it every variable must be declared there (a declared
     variable hides a function of its name), without it every name that is not
     a top-level function is a universally quantified variable.

     Semantics.  Let [G_f] be the graph of [f]: the tuples [(a1, ..., an, r)]
     such that [f a1 ... an] can evaluate to [r].  A call labelled
     [(f b1 ... bn [@copy lbl])] somewhere in the file has the argument set
     [A_lbl], the argument tuples with which [f] is entered from that call,
     directly or through the recursive calls it starts (reachable from the
     states in which the enclosing code reaches the call), and the copy
     graph [G_lbl], the part of [G_f] whose arguments are in [A_lbl].
     - [f] (unlabelled) and [f@def] denote [G_f]; [f@lbl] denotes [G_lbl].
       Below, [g] is any of these.
     - An equation [g a~ = t] (or [t = g a~]) whose other side [t] is not an
       application is the atom [g(a~, t)]: the application can evaluate to
       [t].
     - Any other application [g a~] stands for its values: an atomic formula
       [A[g a~]] is read [forall v. g(a~, v) => A[v]] in a positive position
       and [exists v. g(a~, v) /\ A[v]] in a negative one, so an application
       without a value makes its atom vacuous (true in a positive position,
       false in a premise) -- the partial-correctness reading.  In an
       equation between two applications the right one is read this way and
       the left one by the first rule.  An application under [<=>] or in a
       Boolean subterm (positive and negative at once) is refused.
     - [called f@lbl a~] is the atom [A_lbl(a~)].
     Since [v] occurs only in its atom, the quantifier moves to the front
     unchanged in both cases, so the formula is stated with [v] free (free
     variables are universal) and the atom replaced by [g(a~, v) => A[v]] or
     [g(a~, v) /\ A[v]].  A premise equation [g a~ = r] is therefore the same
     under both readings; the first rule differs from the second only in a
     positive position, where it claims that a value is returned.

     Resolution.  RCaml's refinement-type template gives a function [f] of [n]
     arguments the predicate [f[:j]] on its [j]-th argument, over the
     arguments up to it, and [f[:n]] on its result, over the arguments and the
     result, and copies them once per instantiation (bounded predicate
     polymorphism), the copies named [f[:j]@k@m] (a copy inside the definition
     of [h] is copied again with each instance of [h]).  A copy's argument
     refinements are inferred from the calls it serves, so its [f[:n]] is
     [G_f] restricted to those arguments and its [f[:n-1]] is the set of the
     argument tuples it is entered with.
     - [f@lbl] resolves to the copies of [f[:n]] made at the labelled call's
       instantiation, and [called f@lbl] to the copies of [f[:n-1]] made
       there, in every instance of the enclosing code in the problem.
     - [f@def] resolves to the whole-graph instance of [f]: [f] instantiated
       at its simple type with every refinement [true], whose argument
       refinements admit every argument, so that its [f[:n]] is [G_f].  The
       caller makes it ([graph_instances]).
     - [f] resolves to every copy of [f[:n]] in the problem, the whole-graph
       instance first when there is one.
     The formula is stated once per choice of a copy for each name it uses.
     Refused, with the reason: a name applied to fewer or more arguments than
     it takes, a name that is not a top-level function (a parameter, a local,
     a library function), a name without a copy in the problem, a label no
     call carries, a label refused where it was written (not on a call of a
     top-level function, not one identifier, used twice, or [def]), a label
     on a call of another function, and [called] of an unlabelled name or of
     [f@def] (every argument tuple: write [true]). *)

  exception Notation_error of string

  let notation_fail fmt = ksprintf (fun s -> raise (Notation_error s)) fmt

  (* the names atoms carry until they are resolved to RCaml's predicates (no
     predicate of a generated problem is named so: they contain a space) *)
  let graph_placeholder_prefix = "graph of "
  let arguments_placeholder_prefix = "arguments of "

  (* the spelling [f@lbl] takes inside the OCaml expression the notation is
     parsed as ([@] is OCaml's list append, which binds more loosely than
     application, so it is rewritten to one identifier before parsing) *)
  let copy_name_sep = "__at__"

  (* which predicate of [f] a name in the notation denotes *)
  type copy_target = Graph (* [f]: every copy *) | Def (* [f@def] *) | Label of string

  let label_reserved = "def"

  let split_copy_name x =
    match String.substr_index x ~pattern:copy_name_sep with
    | None -> (x, Graph)
    | Some i ->
        let f = String.prefix x i in
        let l = String.drop_prefix x (i + String.length copy_name_sep) in
        (f, if String.equal l label_reserved then Def else Label l)

  let target_suffix = function
    | Graph -> ""
    | Def -> "@" ^ label_reserved
    | Label l -> "@" ^ l

  (* the inverse of the placeholders: [Some (`Result | `Args, f, target)] *)
  let parse_placeholder n =
    let of_rest kind rest =
      match String.lsplit2 rest ~on:'@' with
      | None -> (kind, rest, Graph)
      | Some (f, l) ->
          (kind, f, if String.equal l label_reserved then Def else Label l)
    in
    match String.chop_prefix n ~prefix:graph_placeholder_prefix with
    | Some rest -> Some (of_rest `Result rest)
    | None ->
        Option.map
          (String.chop_prefix n ~prefix:arguments_placeholder_prefix)
          ~f:(of_rest `Args)

  let is_identifier x =
    (not (String.is_empty x))
    && (Char.is_lowercase x.[0] || Char.equal x.[0] '_')
    && String.for_all x ~f:(fun c ->
        Char.is_alphanum c || Char.equal c '_' || Char.equal c '\'')

  let is_ident_char c = Char.is_alphanum c || Char.equal c '_' || Char.equal c '\''

  (* [split_notation s]: the variables of [s]'s [forall] prefix, if it has
     one, and [s]'s body in OCaml's expression syntax, its [=>] written [:=]
     and its copy names [f@lbl] written [f__at__lbl] *)
  let split_notation s =
    let s = String.strip s in
    let declared, body =
      match String.chop_prefix s ~prefix:"forall" with
      | Some rest when String.length rest > 0 && Char.is_whitespace rest.[0]
        -> (
          match String.index rest '.' with
          | None -> notation_fail "a [forall] prefix without its '.'"
          | Some k ->
              let vars =
                List.filter ~f:(Fn.non String.is_empty)
                @@ String.split_on_chars (String.prefix rest k)
                     ~on:[ ' '; '\t'; '\n'; '\r' ]
              in
              List.iter vars ~f:(fun x ->
                  if not (is_identifier x) then
                    notation_fail "%S in the [forall] prefix is not a variable" x);
              (Some vars, String.drop_prefix rest (k + 1)))
      | _ -> (None, s)
    in
    (* [=>] becomes [:=], the one infix operator of OCaml's syntax that
       binds more loosely than [||] and associates to the right, which is how
       implication is read; a [:=] of the text itself is refused, since it
       would be read as an implication *)
    if String.is_substring body ~substring:":=" then
      notation_fail "[:=] is not part of the notation";
    if String.is_substring body ~substring:copy_name_sep then
      notation_fail "[%s] is not part of the notation" copy_name_sep;
    let n = String.length body in
    let is_op_char c = String.mem "<>=!:|&@^+-*/$%.~?" c in
    let b = Buffer.create n in
    let i = ref 0 in
    while !i < n do
      if
        Char.equal body.[!i] '='
        && !i + 1 < n
        && Char.equal body.[!i + 1] '>'
        && (!i = 0 || not (is_op_char body.[!i - 1]))
        && (!i + 2 >= n || not (is_op_char body.[!i + 2]))
      then (
        Buffer.add_string b ":=";
        i := !i + 2)
      else if
        (* a copy name: [@] between a name and a label, no space *)
        Char.equal body.[!i] '@'
        && !i > 0
        && is_ident_char body.[!i - 1]
        && !i + 1 < n
        && (Char.is_lowercase body.[!i + 1] || Char.equal body.[!i + 1] '_')
      then (
        Buffer.add_string b copy_name_sep;
        incr i)
      else (
        Buffer.add_char b body.[!i];
        incr i)
    done;
    (declared, Buffer.contents b)

  type polarity = Pos | Neg | Both

  let flip = function Pos -> Neg | Neg -> Pos | Both -> Both

  type notation_ctx = {
    nt_renv : Rtype.Env.t;
    nt_declared : string list option;
    nt_vars : (string, Sort.t) Hashtbl.t;
    nt_is_property : bool;
    nt_preds : (string * Sort.t list) list;
        (* the auxiliary predicates of a [[@@@chc]] block, each with its
           argument sorts (shared by every atom of it, so that one typing of
           the block gives every atom the same sorts); [] elsewhere *)
  }

  (* the predicate of the generated problem an auxiliary predicate [p] of a
     [[@@@chc]] block is ([chc_pred_pvar_clash] refuses a block one of whose
     names a predicate RCaml generated already has) *)
  let chc_pred_pvar p = Ident.Pvar ("chc_" ^ p)

  (* the number of arguments of [f]'s refinement type *)
  let rec rtype_arity = function
    | Rtype.RArrow (_, _, c, _) -> 1 + rtype_arity c.Rtype.val_type
    | Rtype.RForall (_, _, c) | Rtype.RPoly (_, c) ->
        rtype_arity c.Rtype.val_type
    | _ -> 0

  (* [Some (f, target, n, sargs, sret)] when [x] is [f], [f@lbl] or [f@def]
     for a top-level function [f] of [n] arguments of sorts [sargs] and result
     sort [sret], and [x] is not a declared variable; a copy name whose [f]
     is not such a function is refused *)
  let notation_function ctx x =
    let f, target = split_copy_name x in
    if
      match (target, ctx.nt_declared) with
      | Graph, Some vars -> List.mem vars x ~equal:String.equal
      | _ -> false
    then None
    else
      let info =
        match Rtype.Env.look_up ctx.nt_renv (Ident.Tvar f) with
        | Some rty when rtype_arity rty > 0 ->
            let rec strip = function Sort.SPoly (_, s) -> strip s | s -> s in
            let sargs, sret =
              Sort.args_ret_of (strip (Rtype.sort_of_val rty))
            in
            let n = rtype_arity rty in
            if List.length sargs < n then None
            else
              let sargs, rest = List.split_n sargs n in
              (* a function returning a function: its result sort is the
                 arrow *)
              let sret =
                List.fold_right rest ~init:sret ~f:(fun s acc ->
                    Sort.mk_arrow s acc)
              in
              Some (f, target, n, sargs, sret)
        | _ -> None
      in
      match (info, target) with
      | None, (Def | Label _) ->
          notation_fail
            "%s%s: %s is not a function defined at the top level of the file"
            f (target_suffix target) f
      | _ -> info

  let display_name f target = f ^ target_suffix target

  let operator_of (e : Parsetree.expression) =
    match e.pexp_desc with
    | Pexp_ident { txt = Longident.Lident x; _ }
    | Pexp_ident { txt = Longident.Ldot ({ txt = Longident.Lident "Stdlib"; _ }, { txt = x; _ }); _ } ->
        Some x
    | _ -> None

  let unlabelled what args =
    List.map args ~f:(function
      | Asttypes.Nolabel, a -> a
      | _ -> notation_fail "a labelled argument in %s" what)

  (* [direct_application ctx e]: [Some (f, target, n, sargs, sret, args)]
     when [e] is an application of a top-level function (or a copy name of
     one) to exactly its arguments *)
  let direct_application ctx (e : Parsetree.expression) =
    match e.pexp_desc with
    | Pexp_apply (fe, args) -> (
        match operator_of fe with
        | Some x -> (
            match notation_function ctx x with
            | Some (f, target, n, sargs, sret) ->
                let name = display_name f target in
                let args = unlabelled name args in
                if List.length args < n then
                  notation_fail
                    "%s is applied to %d of its %d arguments (a partial \
                     application has no graph)"
                    name (List.length args) n
                else if List.length args > n then
                  notation_fail
                    "%s takes %d arguments and is applied to %d (its result is \
                     a function)"
                    name n (List.length args)
                else Some (f, target, n, sargs, sret, args)
            | None -> None)
        | None -> None)
    | _ -> None

  let graph_atom f target sargs sret args res =
    Formula.mk_atom
    @@ Atom.mk_pvar_app
         (Ident.Pvar (graph_placeholder_prefix ^ display_name f target))
         (sargs @ [ sret ])
         (args @ [ res ])

  let arguments_atom f target sargs args =
    Formula.mk_atom
    @@ Atom.mk_pvar_app
         (Ident.Pvar (arguments_placeholder_prefix ^ display_name f target))
         sargs args

  (* [called_application ctx e]: [Some (x, args)] when [e] is
     [called x a1 ... an] and [x] names a top-level function or a copy of
     one (the notation's word [called] takes precedence over a function of
     that name only there) *)
  let called_application ctx (e : Parsetree.expression) =
    match e.pexp_desc with
    | Pexp_apply
        ( { pexp_desc = Pexp_ident { txt = Longident.Lident "called"; _ }; _ },
          (Asttypes.Nolabel, { pexp_desc = Pexp_ident { txt = Longident.Lident x; _ }; _ })
          :: args )
      when Option.is_some (notation_function ctx x) ->
        Some (x, args)
    | _ -> None

  (* [notation_term ctx hoisted e]: the term of [e], each application in it
     replaced by a fresh variable whose graph atom is pushed on [hoisted]
     (innermost first) *)
  let rec notation_term ctx hoisted (e : Parsetree.expression) : Term.t =
    match e.pexp_desc with
    | Pexp_constraint (e, _) -> notation_term ctx hoisted e
    | Pexp_constant { pconst_desc = Pconst_integer (s, None); _ } ->
        T_int.mk_int (Z.of_string s)
    | Pexp_construct ({ txt = Longident.Lident (("true" | "false") as b); _ }, None)
      ->
        T_bool.make (String.equal b "true")
    | Pexp_construct ({ txt = Longident.Lident c; _ }, arg) -> (
        let args =
          match arg with
          | None -> []
          | Some { pexp_desc = Pexp_tuple es; _ } ->
              List.map es ~f:(fun (_, e) -> notation_term ctx hoisted e)
          | Some e -> [ notation_term ctx hoisted e ]
        in
        match DTEnv.look_up_dt_by_cons_name (get_dtenv ()) c with
        | Some dt -> T_dt.mk_cons dt c args
        | None -> notation_fail "unknown constructor %s" c)
    | Pexp_ident { txt = Longident.Lident x; _ } -> (
        match notation_function ctx x with
        | Some (f, target, n, _, _) ->
            notation_fail
              "%s is used without its %d arguments (a function value has no \
               graph atom)"
              (display_name f target) n
        | None ->
            if List.Assoc.mem ctx.nt_preds x ~equal:String.equal then
              notation_fail "the predicate %s is used as a term" x;
            (match ctx.nt_declared with
            | Some vars when not (List.mem vars x ~equal:String.equal) ->
                notation_fail
                  "%s is neither declared in the [forall] prefix nor a \
                   top-level function"
                  x
            | _ -> ());
            let sort =
              Hashtbl.find_or_add ctx.nt_vars x ~default:Sort.mk_fresh_svar
            in
            Term.mk_var (Ident.Tvar x) sort)
    | Pexp_apply (fe, args) -> (
        match direct_application ctx e with
        | Some (f, target, _, sargs, sret, args) ->
            let args = List.map args ~f:(notation_term ctx hoisted) in
            let v =
              Term.mk_var
                (Ident.mk_fresh_tvar ~prefix:(Some (f ^ "_value")) ())
                sret
            in
            hoisted := graph_atom f target sargs sret args v :: !hoisted;
            v
        | None -> (
            let args = unlabelled "an operator application" args in
            let t = notation_term ctx hoisted in
            match (operator_of fe, args) with
            | Some "+", [ a; b ] -> T_num.mk_nadd (t a) (t b)
            | Some "-", [ a; b ] -> T_num.mk_nsub (t a) (t b)
            | Some "*", [ a; b ] -> T_num.mk_nmul (t a) (t b)
            (* OCaml's / and mod truncate toward zero *)
            | Some "/", [ a; b ] -> T_num.mk_ndiv Value.Truncated (t a) (t b)
            | Some "mod", [ a; b ] -> T_num.mk_nrem Value.Truncated (t a) (t b)
            | Some ("~-" | "-"), [ a ] -> T_num.mk_nneg (t a)
            | Some
                ( "=" | "<>" | "<" | "<=" | ">" | ">=" | "&&" | "&" | "||"
                | "or" | "not" | ":=" | "<=>" | "called" ),
              _ ->
                (* a Boolean subterm is both positive and negative *)
                T_bool.of_formula (notation_formula ctx Both e)
            | Some x, _ ->
                notation_fail
                  "%s is not a function defined at the top level of the file \
                   (a parameter, a local or a library function cannot be \
                   applied here)"
                  x
            | None, _ -> notation_fail "only a named function can be applied"))
    | _ ->
        notation_fail "unsupported expression: %s"
          (Pprintast.string_of_expression e)

  (* [notation_atom ctx pol build]: the atomic formula [build hoisted] at
     polarity [pol], its applications' graph atoms ([hoisted]) placed as the
     semantics above says *)
  and notation_atom _ctx pol build =
    let hoisted = ref [] in
    let atom = build hoisted in
    match (List.rev !hoisted, pol) with
    | [], _ -> atom
    | hs, Pos -> Formula.mk_imply (Formula.and_of hs) atom
    | hs, Neg -> Formula.and_of (hs @ [ atom ])
    | _, Both ->
        notation_fail
          "an application inside [<=>] or a Boolean subterm (it would be both \
           a premise and a claim)"

  and notation_formula ctx pol (e : Parsetree.expression) : Formula.t =
    let refuse_claim what =
      (* a property is a goal: an atom of it in a positive position would
         define its predicate instead of asking about it *)
      if ctx.nt_is_property && not (Stdlib.( = ) pol Neg) then
        notation_fail
          "%s: a property is a goal and cannot claim it (write it as a \
           premise, [... => ...])"
          what;
      if Stdlib.( = ) pol Both then
        notation_fail "%s inside [<=>] or a Boolean subterm" what
    in
    let graph_claim f target sargs sret args other =
      (* [f args = other], [other] not an application of a top-level
         function: the graph atom *)
      refuse_claim
        (sprintf "%s is claimed to return a value" (display_name f target));
      notation_atom ctx pol (fun hoisted ->
          let args = List.map args ~f:(notation_term ctx hoisted) in
          let res = notation_term ctx hoisted other in
          graph_atom f target sargs sret args res)
    in
    let pred_atom x args =
      (* an atom [p a~] of an auxiliary predicate of a [[@@@chc]] block *)
      let sorts = List.Assoc.find_exn ctx.nt_preds x ~equal:String.equal in
      let args = unlabelled x args in
      if List.length args <> List.length sorts then
        notation_fail "the predicate %s takes %d arguments and is given %d" x
          (List.length sorts) (List.length args);
      refuse_claim (sprintf "the predicate %s" x);
      notation_atom ctx pol (fun hoisted ->
          Formula.mk_atom
          @@ Atom.mk_pvar_app (chc_pred_pvar x) sorts
               (List.map args ~f:(notation_term ctx hoisted)))
    in
    let is_pred x = List.Assoc.mem ctx.nt_preds x ~equal:String.equal in
    match e.pexp_desc with
    | Pexp_constraint (e, _) -> notation_formula ctx pol e
    | Pexp_ident { txt = Longident.Lident x; _ } when is_pred x -> pred_atom x []
    | Pexp_apply (fe, args)
      when Option.value_map (operator_of fe) ~default:false ~f:is_pred ->
        pred_atom (Option.value_exn (operator_of fe)) args
    | Pexp_construct ({ txt = Longident.Lident "true"; _ }, None) ->
        Formula.mk_true ()
    | Pexp_construct ({ txt = Longident.Lident "false"; _ }, None) ->
        Formula.mk_false ()
    | Pexp_apply _ when Option.is_some (called_application ctx e) -> (
        let x, args = Option.value_exn (called_application ctx e) in
        match notation_function ctx x with
        | Some (f, (Label _ as target), n, sargs, _) ->
            let name = display_name f target in
            let args = unlabelled ("called " ^ name) args in
            if List.length args <> n then
              notation_fail "called %s takes %d arguments and is given %d" name
                n (List.length args);
            refuse_claim (sprintf "called %s" name);
            notation_atom ctx pol (fun hoisted ->
                arguments_atom f target sargs
                  (List.map args ~f:(notation_term ctx hoisted)))
        | Some (f, target, _, _, _) ->
            notation_fail
              "called %s: [called] takes a labelled copy f@lbl (the \
               arguments of %s's whole graph are every argument tuple: write \
               [true])"
              (display_name f target) f
        | None -> assert false)
    | Pexp_apply (fe, args) when Option.is_none (direct_application ctx e) -> (
        let args = unlabelled "an operator application" args in
        let cmp mk a b =
          notation_atom ctx pol (fun hoisted ->
              Formula.mk_atom
                (mk (notation_term ctx hoisted a) (notation_term ctx hoisted b)))
        in
        match (operator_of fe, args) with
        | Some ("&&" | "&"), [ a; b ] ->
            Formula.mk_and (notation_formula ctx pol a) (notation_formula ctx pol b)
        | Some ("||" | "or"), [ a; b ] ->
            Formula.mk_or (notation_formula ctx pol a) (notation_formula ctx pol b)
        | Some "not", [ a ] -> Formula.mk_neg (notation_formula ctx (flip pol) a)
        | Some "<=>", [ a; b ] ->
            Formula.mk_iff (notation_formula ctx Both a) (notation_formula ctx Both b)
        | Some ":=", [ a; b ] ->
            Formula.mk_imply
              (notation_formula ctx (flip pol) a)
              (notation_formula ctx pol b)
        | Some "=", [ a; b ] -> (
            match (direct_application ctx a, direct_application ctx b) with
            | Some (f, target, _, sargs, sret, fargs), _ ->
                graph_claim f target sargs sret fargs b
            | None, Some (f, target, _, sargs, sret, fargs) ->
                graph_claim f target sargs sret fargs a
            | None, None -> cmp T_bool.mk_eq a b)
        | Some "<>", [ a; b ] ->
            (* [f a~ <> t] is [not (f a~ = t)] *)
            if
              Option.is_some (direct_application ctx a)
              || Option.is_some (direct_application ctx b)
            then
              Formula.mk_neg
                (notation_formula ctx (flip pol)
                   (Ast_helper.Exp.apply
                      (Ast_helper.Exp.ident
                         (Location.mknoloc (Longident.Lident "=")))
                      [ (Asttypes.Nolabel, a); (Asttypes.Nolabel, b) ]))
            else cmp T_bool.mk_neq a b
        | Some "<", [ a; b ] -> cmp T_num.mk_nlt a b
        | Some "<=", [ a; b ] -> cmp T_num.mk_nleq a b
        | Some ">", [ a; b ] -> cmp T_num.mk_ngt a b
        | Some ">=", [ a; b ] -> cmp T_num.mk_ngeq a b
        | _ ->
            notation_atom ctx pol (fun hoisted ->
                Formula.eq (notation_term ctx hoisted e) (T_bool.mk_true ())))
    | Pexp_apply _ -> (
        (* a Boolean application [f a~] is the equation [f a~ = true] *)
        match direct_application ctx e with
        | Some (f, target, _, sargs, sret, fargs) ->
            graph_claim f target sargs sret fargs
              (Ast_helper.Exp.construct
                 (Location.mknoloc (Longident.Lident "true"))
                 None)
        | None -> assert false)
    | _ ->
        notation_atom ctx pol (fun hoisted ->
            Formula.eq (notation_term ctx hoisted e) (T_bool.mk_true ()))

  (* [formula_of_notation ~is_property renv s]: the formula of the notation
     [s], its atoms named by [graph_placeholder_prefix] or
     [arguments_placeholder_prefix] and the name they denote, its free
     variables universal; [Error] says why it cannot be read *)
  let formula_of_notation ?(preds = []) ~is_property renv s =
    try
      let declared, body = split_notation s in
      (* Auxiliary predicates belong only to a block and its lemmas. An
         explicitly declared variable shadows an auxiliary predicate of the
         same name, including when that variable is Boolean. *)
      let preds =
        match declared with
        | None -> preds
        | Some vars ->
            List.filter preds ~f:(fun (p, _) ->
                not (List.mem vars p ~equal:String.equal))
      in
      let ctx =
        {
          nt_renv = renv;
          nt_declared = declared;
          nt_vars = Hashtbl.create (module String);
          nt_is_property = is_property;
          nt_preds = preds;
        }
      in
      let expr =
        try Parse.expression (Lexing.from_string body)
        with e when not (Timer.is_async e) ->
          notation_fail "cannot parse %S as an OCaml expression" body
      in
      Ok (notation_formula ctx Pos expr)
    with Notation_error why -> Error why

  (* ---- [[@@@chc "..."]]: Horn clauses over the file's functions ----

     A block of Horn clauses, each ended by a [.] followed by white space or
     the end of the block:
       [p a1 ... an :- body.]   a definite clause of an auxiliary predicate [p]
       [p a1 ... an.]           a fact (the body [true])
       [?- body.]               a query
     A body is a formula of the application notation of [[@@@property]] (the
     file's top-level functions applied to their arguments, copy names,
     [called] atoms) in which an application [p a~] of an auxiliary predicate
     -- a name heading a clause of the block -- is the atom [p(a~)]; a head's
     arguments are terms without applications of functions.  Every variable
     of a clause is universal in that clause.  An auxiliary predicate must
     not be named like a top-level function, keeps one number of arguments,
     and is used only as an atom of a body; its argument sorts are inferred
     from the whole block (integers when nothing else constrains them).

     Semantics.  The auxiliary predicates are the least ones satisfying their
     clauses, given the functions' graphs, and the answer is [sat] iff no
     query body holds for them, i.e. iff the clauses together with the goals
     [body => false] have a solution: a query is a property whose premises
     may also be atoms of the defined predicates.  Since a definition's
     atoms are positive only in its own head and the functions' graphs occur
     only in bodies, the generated problem is a set of Horn clauses in which
     the auxiliary predicates are ordinary unknowns of the solver. *)

  (* [split_chc_clauses s]: the clauses of a block, without their final [.] *)
  let split_chc_clauses s =
    let n = String.length s in
    let rec go start i acc =
      if i >= n then
        let last = String.strip (String.sub s ~pos:start ~len:(n - start)) in
        if String.is_empty last then List.rev acc
        else notation_fail "the clause %S is not ended by a '.'" last
      else if
        Char.equal s.[i] '.'
        && (i + 1 >= n || Char.is_whitespace s.[i + 1])
      then
        let c = String.strip (String.sub s ~pos:start ~len:(i - start)) in
        go (i + 1) (i + 1) (if String.is_empty c then acc else c :: acc)
      else go start (i + 1) acc
    in
    go 0 0 []

  (* [formulas_of_chc renv s]: the formulas of the block [s] (a definite
     clause [body => p(a~)], a query [body => false]), typed together, their
     variables renamed apart and universal, their function applications
     placeholders as in [formula_of_notation]; with the auxiliary predicates'
     names; or why the block cannot be read *)
  let formulas_of_chc renv s =
    try
      let parse what text =
        try Parse.expression (Lexing.from_string text)
        with e when not (Timer.is_async e) ->
          notation_fail "cannot parse the %s %S as an OCaml expression" what
            text
      in
      let clauses =
        List.map (split_chc_clauses s) ~f:(fun c ->
            match String.chop_prefix c ~prefix:"?-" with
            | Some body -> (None, String.strip body)
            | None -> (
                match String.substr_index c ~pattern:":-" with
                | Some k ->
                    ( Some (String.strip (String.prefix c k)),
                      String.strip (String.drop_prefix c (k + 2)) )
                | None -> (Some c, "true")))
      in
      if List.is_empty clauses then notation_fail "the block has no clause";
      if List.for_all clauses ~f:(fun (h, _) -> Option.is_some h) then
        notation_fail "the block has no query [?- ...]";
      let ctx0 =
        {
          nt_renv = renv;
          nt_declared = None;
          nt_vars = Hashtbl.create (module String);
          nt_is_property = true;
          nt_preds = [];
        }
      in
      (* each head: its predicate and argument expressions *)
      let heads =
        List.map clauses ~f:(fun (h, body) ->
            ( Option.map h ~f:(fun h ->
                  let e = parse "head" h in
                  match e.pexp_desc with
                  | Pexp_ident { txt = Longident.Lident p; _ } -> (p, [])
                  | Pexp_apply
                      ({ pexp_desc = Pexp_ident { txt = Longident.Lident p; _ }; _ }, args)
                    ->
                      (p, unlabelled ("the head " ^ h) args)
                  | _ -> notation_fail "the head %S is not a predicate atom" h),
              body ))
      in
      let preds =
        List.fold heads ~init:[] ~f:(fun acc (h, _) ->
            match h with
            | None -> acc
            | Some (p, args) -> (
                if not (is_identifier p) then
                  notation_fail "%S cannot name a predicate" p;
                if Option.is_some (notation_function ctx0 p) then
                  notation_fail
                    "the predicate %s is named like a function defined at the \
                     top level of the file"
                    p;
                match List.Assoc.find acc p ~equal:String.equal with
                | Some n when n <> List.length args ->
                    notation_fail
                      "the predicate %s heads clauses with %d and %d arguments"
                      p n (List.length args)
                | Some _ -> acc
                | None -> (p, List.length args) :: acc))
      in
      let preds =
        List.rev_map preds ~f:(fun (p, n) ->
            (p, List.init n ~f:(fun _ -> Sort.mk_fresh_svar ())))
      in
      let phis =
        List.mapi heads ~f:(fun k (h, body) ->
            let ctx =
              {
                ctx0 with
                nt_vars = Hashtbl.create (module String);
                nt_preds = preds;
              }
            in
            let declared, body = split_notation body in
            if Option.is_some declared then
              notation_fail "a clause takes no [forall] prefix (its variables \
                             are universal)";
            let body = notation_formula ctx Neg (parse "body" body) in
            let head =
              match h with
              | None -> Formula.mk_false ()
              | Some (p, args) ->
                  let hoisted = ref [] in
                  let args = List.map args ~f:(notation_term ctx hoisted) in
                  if not (List.is_empty !hoisted) then
                    notation_fail
                      "the head of a clause of %s applies a function (state \
                       the application in the body)"
                      p;
                  Formula.mk_atom
                  @@ Atom.mk_pvar_app (chc_pred_pvar p)
                       (List.Assoc.find_exn preds p ~equal:String.equal)
                       args
            in
            (* the clause's variables renamed apart from the other clauses' *)
            let ren =
              Map.Poly.of_alist_exn
              @@ List.map (Hashtbl.keys ctx.nt_vars) ~f:(fun x ->
                  ( Ident.Tvar x,
                    Ident.mk_fresh_tvar ~prefix:(Some (sprintf "%s_c%d" x k)) () ))
            in
            Formula.rename ren (Formula.mk_imply body head))
      in
      let phis =
        try Typeinf.typeinf ~print:Debug.print ~default:(Some T_int.SInt) phis
        with e when not (Timer.is_async e) ->
          notation_fail "cannot type the block (%s)" (Exn.to_string e)
      in
      (* each predicate with the sorts the typing gave it *)
      let typed =
        Set.to_list @@ Set.concat_map (Set.Poly.of_list phis) ~f:Formula.pred_sort_env_of
      in
      let preds =
        List.map preds ~f:(fun (p, sorts) ->
            ( p,
              Option.value ~default:sorts
              @@ List.find_map typed ~f:(fun (q, sorts) ->
                  if Stdlib.( = ) q (chc_pred_pvar p) then Some sorts else None)
            ))
      in
      Ok (phis, preds)
    with Notation_error why -> Error why

  (* the placeholders of a read notation: [(placeholder, kind, f, target,
     number of the predicate's arguments)], each once *)
  let placeholders_of phi =
    List.dedup_and_sort ~compare:Stdlib.compare
    @@ Set.to_list
    @@ Set.Poly.filter_map (Formula.pred_sort_env_of phi)
         ~f:(fun (Ident.Pvar n, sorts) ->
           Option.map (parse_placeholder n) ~f:(fun (kind, f, target) ->
               (n, kind, f, target, List.length sorts)))

  (* The labelled calls of the file being read (reset per file): each label
     to the function its call applies and the top-level binding the call
     stands in, or to the reason the label is refused. *)
  let copy_label_sites :
      (string, (string * string option, string) Result.t) Hashtbl.t =
    Hashtbl.create (module String)

  (* The whole-graph instance of each function, [f] to the renaming its
     instantiation made (set by [graph_instances] for the problem being
     built; reset per problem). *)
  type graph_map = (string, (Ident.pvar * Ident.pvar) list) Map.Poly.t

  let renamed ren name =
    List.find_map ren ~f:(fun (Ident.Pvar a, Ident.Pvar b) ->
        if String.equal a name then Some b else None)

  (* the predicates of [penv] that are [c] or a later copy of it *)
  let copies_of penv c nsorts =
    List.filter penv ~f:(fun (Ident.Pvar n, sorts) ->
        (String.equal n c || String.is_prefix n ~prefix:(c ^ "@"))
        && List.length sorts = nsorts)

  (* [resolve_placeholder penv gmap (kind, f, target, nsorts)]: the
     predicates of the generated problem (whose predicates are [penv]) the
     name denotes, with their argument sorts -- at least one, else the
     reason.  [kind] is [`Result] for a graph atom ([f[:n]], [nsorts = n+1])
     and [`Args] for an argument atom ([f[:n-1]], [nsorts = n]). *)
  let resolve_placeholder penv (gmap : graph_map) (kind, f, target, nsorts) =
    let pos = match kind with `Result -> nsorts - 1 | `Args -> nsorts - 1 in
    let base = f ^ Rtype.position_of "" pos in
    let whole = Option.bind (Map.Poly.find gmap f) ~f:(fun ren -> renamed ren base) in
    match target with
    | Graph -> (
        match copies_of penv base nsorts with
        | [] ->
            Error
              (sprintf
                 "the problem has no predicate %s (or a copy of it): %s's \
                  graph is not part of the problem (no call of %s is reached)"
                 base f f)
        | copies ->
            (* the whole-graph instance first: a lemma's first instance is
               then its claim about the graph, which the later ones may use *)
            let is_whole (Ident.Pvar n, _) =
              Option.value_map whole ~default:false ~f:(String.equal n)
            in
            let w, others = List.partition_tf copies ~f:is_whole in
            Ok (w @ others))
    | Def -> (
        match whole with
        | None ->
            Error
              (sprintf
                 "%s@def: no whole-graph instance of %s is part of this problem \
                  (%s's refinement is not generalised)"
                 f f f)
        | Some c -> (
            match
              List.filter penv ~f:(fun (Ident.Pvar n, sorts) ->
                  String.equal n c && List.length sorts = nsorts)
            with
            | [] ->
                Error
                  (sprintf "%s@def: its predicate %s is not in the problem" f c)
            | ps -> Ok ps))
    | Label l -> (
        let name = f ^ "@" ^ l in
        match Hashtbl.find copy_label_sites l with
        | None ->
            Error
              (sprintf "%s: unknown label %s (no call carries [@copy %s])" name
                 l l)
        | Some (Error why) ->
            Error (sprintf "%s: the label %s is refused (%s)" name l why)
        | Some (Ok (g, _)) when not (String.equal f g) ->
            Error
              (sprintf "%s: the call labelled %s applies %s, not %s" name l g f)
        | Some (Ok _) -> (
            let cs =
              List.dedup_and_sort ~compare:String.compare
              @@ List.filter_map (Hashtbl.find_multi copy_label_copies l)
                   ~f:(fun ren -> renamed ren base)
            in
            if List.is_empty cs then
              Error
                (sprintf
                   "%s: the call labelled %s makes no copy of %s's refinement \
                    (a call inside %s's own definition uses its own \
                    predicates)"
                   name l f f)
            else
              match List.concat_map cs ~f:(fun c -> copies_of penv c nsorts) with
              | [] ->
                  Error
                    (sprintf
                       "%s: no copy of the call labelled %s is part of this \
                        problem (the code containing the call is not reached \
                        from it)"
                       name l)
              | ps -> Ok ps))

  (* the most instances one lemma or property may expand into *)
  let max_notation_instances = 64

  (* [instances_of_notation ~is_property envs penv gmap content]: the formula
     of the notation [content] (a lemma or a property) as the list of its
     instances over the generated problem's predicates ([penv]), one per
     choice of a predicate for each name it uses (the same one at every
     occurrence of the name), each a formula whose free variables are
     universal, the instance choosing each name's first predicate first; or
     the reason it cannot be read. *)
  let rec instances_of_notation ?(preds = []) ~is_property envs penv gmap content =
    Rtype.renv_ref := envs.renv;
    set_dtenv envs.dtenv;
    match formula_of_notation ~preds ~is_property envs.renv content with
    | Error why -> Error why
    | Ok phi -> instances_of_formula penv gmap phi

  (* [instances_of_formula penv gmap phi]: the instances of a read notation
     [phi], as [instances_of_notation] says *)
  and instances_of_formula penv gmap phi =
        let resolved =
          List.map (placeholders_of phi) ~f:(fun (n, kind, f, target, nsorts) ->
              Result.map
                (resolve_placeholder penv gmap (kind, f, target, nsorts))
                ~f:(fun copies -> (n, copies)))
        in
        match Result.combine_errors resolved with
        | Error whys -> Error (String.concat ~sep:"; " whys)
        | Ok choices ->
            let count =
              List.fold choices ~init:1 ~f:(fun acc (_, cs) ->
                  if acc > max_notation_instances then acc
                  else acc * List.length cs)
            in
            if count > max_notation_instances then
              Error
                (sprintf
                   "more than %d instances over the copies of its functions' \
                    graphs"
                   max_notation_instances)
            else
              let assignments =
                List.fold_right choices ~init:[ [] ] ~f:(fun (n, cs) acc ->
                    List.concat_map cs ~f:(fun c ->
                        List.map acc ~f:(fun rest -> (n, c) :: rest)))
              in
              let instance assignment =
                Typeinf.typeinf_formula ~print:Debug.print
                  ~default:(Some T_int.SInt)
                @@ Formula.map_atom phi ~f:(fun atm ->
                    match atm with
                    | Atom.App (Predicate.Var (Ident.Pvar n, _), args, _) -> (
                        match
                          List.Assoc.find assignment ~equal:String.equal n
                        with
                        | Some (pvar, sorts) ->
                            Formula.mk_atom @@ Atom.mk_pvar_app pvar sorts args
                        | None -> Formula.mk_atom atm)
                    | _ -> Formula.mk_atom atm)
              in
              try Ok (List.map assignments ~f:instance)
              with e when not (Timer.is_async e) ->
                Error (sprintf "cannot type it (%s)" (Exn.to_string e))

  (* [graph_functions ~is_property envs content]: the functions whose whole
     graph the notation [content] speaks about ([f] and [f@def]) and the
     top-level bindings containing the labelled calls it names; [] when it
     cannot be read (its refusal is reported where it is resolved) *)
  let rec graph_functions ?(preds = []) ~is_property envs content =
    Rtype.renv_ref := envs.renv;
    set_dtenv envs.dtenv;
    match formula_of_notation ~preds ~is_property envs.renv content with
    | Error _ -> ([], [])
    | Ok phi -> graph_functions_of_formula phi

  and graph_functions_of_formula phi =
        let ps = placeholders_of phi in
        ( List.filter_map ps ~f:(fun (_, _, f, target, _) ->
              match target with Graph | Def -> Some f | Label _ -> None),
          List.filter_map ps ~f:(fun (_, _, _, target, _) ->
              match target with
              | Label l -> (
                  match Hashtbl.find copy_label_sites l with
                  | Some (Ok (_, encl)) -> encl
                  | _ -> None)
              | Graph | Def -> None) )

  (* The lemmas' predicates are proved and used by MuCyc's relational search
     in the order given, each with the ones proved before it.  For each
     function [f] with a whole-graph instance [W] (in [gmap]) and each other
     copy [K] of [f]'s result predicate in the problem, the conjecture
     [K(x~, r) => W(x~, r)] comes first: a copy's graph is [f]'s graph
     restricted to the arguments the copy serves, so it holds, and once proved
     it carries a lemma proved of [W] -- a claim about [f]'s graph -- to the
     copies the goals speak about.  Then each lemma's instances, the
     whole-graph one first. *)
  let containment_conjectures penv (gmap : graph_map) =
    List.concat_map (Map.Poly.to_alist gmap) ~f:(fun (f, ren) ->
        (* [f]'s result predicate is its template's last position *)
        let positions =
          List.filter_map ren ~f:(fun (Ident.Pvar a, _) ->
              Option.bind (String.chop_prefix a ~prefix:(f ^ "[:"))
                ~f:(fun rest ->
                  Option.bind (String.chop_suffix rest ~suffix:"]")
                    ~f:Int.of_string_opt))
        in
        match List.max_elt positions ~compare:Int.compare with
        | None -> []
        | Some n -> (
            let base = f ^ Rtype.position_of "" n in
            match renamed ren base with
            | None -> []
            | Some w -> (
                match
                  List.find penv ~f:(fun (Ident.Pvar m, _) -> String.equal m w)
                with
                | None -> []
                | Some (wp, sorts) ->
                    List.filter_map (copies_of penv base (List.length sorts))
                      ~f:(fun (kp, _) ->
                        if Stdlib.( = ) kp wp then None
                        else
                          let xs =
                            List.map sorts ~f:(fun s ->
                                Term.mk_var (Ident.mk_fresh_tvar ()) s)
                          in
                          Some
                            (Formula.mk_imply
                               (Formula.mk_atom @@ Atom.mk_pvar_app kp sorts xs)
                               (Formula.mk_atom @@ Atom.mk_pvar_app wp sorts xs))))))

  (* The lemmas of the file's [[@@@lemma]] annotations over the generated
     problem [pcsp], in file order, preceded by the containment conjectures
     of the whole-graph instances in [gmap]; a lemma that does not resolve is
     reported on stderr and left out, never kept unresolved. *)
  let lemmas_of_annotations ?(preds = []) ~config envs gmap pcsp =
    if List.is_empty !lemma_annotations then []
    else
      let penv =
        Set.to_list
        @@ Set.concat_map (PCSP.Problem.old_formulas_of pcsp)
             ~f:(fun phi -> Formula.pred_sort_env_of phi)
      in
      let lemmas =
        List.concat_map !lemma_annotations ~f:(fun content ->
            Rtype.cgen_config := config;
            match
              instances_of_notation ~preds ~is_property:false envs penv gmap content
            with
            | Ok phis ->
                Debug.print
                @@ lazy
                     (sprintf "[lemma] %s\n  read as %s" content
                        (String.concat_map_list ~sep:"\n  and " phis
                           ~f:Formula.str_of));
                phis
            | Error why ->
                Out_channel.eprintf "[RCaml] lemma %S refused: %s\n%!" content
                  why;
                [])
      in
      if List.is_empty lemmas then []
      else
        let containments = containment_conjectures penv gmap in
        if not (List.is_empty containments) then
          Debug.print
          @@ lazy
             (sprintf "[lemma] copy-in-graph conjectures:\n  %s"
                (String.concat_map_list ~sep:"\n  " containments
                   ~f:Formula.str_of));
        containments @ lemmas

  (* [graph_instances ~config envs funs]: each function of [funs]
     instantiated at its simple type with every refinement [true] -- an
     assertion [type_of(f) <: T] that checks nothing -- which brings its
     definition's constraints into the problem on fresh predicates whose
     argument refinements admit every argument, so that its result
     predicate is [f]'s whole graph.  Returns those constraints, the kind map
     extended with the instances' kinds, and each function's renaming; a
     name with no definition is the [Error].  With [definite_only], only the
     constraints that define a predicate (have a predicate atom in a positive
     position) are kept: an instance made only so that a lemma can speak
     about the graph must not add the goals of the function's own
     assertions, which are asked for every argument there, whereas the
     program asks them only for the arguments it passes (a function that
     asserts its precondition would otherwise make a safe program look
     unsafe).  Dropping goals leaves the least model of the instance's
     predicates unchanged. *)
  let graph_instances ?(definite_only = false) ~config envs funs =
    List.fold_result funs ~init:(Set.Poly.empty, envs.kind_map, Map.Poly.empty)
      ~f:(fun (constrs, kind_map, gmap) f ->
        if Map.Poly.mem gmap f then Ok (constrs, kind_map, gmap)
        else
          match Rtype.Env.look_up envs.renv (Ident.Tvar f) with
          | None -> Error (sprintf "no function %s is defined before it" f)
          | Some rty_def0 ->
              let rty =
                Rtype.simple_val_of_sort ~config
                  (match Rtype.sort_of_val rty_def0 with
                  | Sort.SPoly (_, s) -> s
                  | s -> s)
              in
              let dom = Rtype.Env.dep_args_of envs.renv in
              let recorder = ref [] in
              Rtype.recorded_renamings := Some recorder;
              let rty_def, constrs_def, kind_map_def =
                Exn.protect
                  ~finally:(fun () -> Rtype.recorded_renamings := None)
                  ~f:(fun () ->
                    Rtype.instantiate_val ~print:Debug.print ~config dom
                      kind_map
                      (Map.Poly.empty, Map.Poly.empty)
                      (rty_def0, Rtype.sort_of_val rty))
              in
              let kind_map_def =
                adm_kinds_at_instance envs.mode ~xty0:rty_def0 ~xty:rty_def
                  kind_map_def
              in
              let defines phi =
                Set.exists (fst (Formula.atoms_of ~nrec:true phi))
                  ~f:Atom.is_pvar_app
              in
              let constrs_inst =
                Set.union constrs_def
                  (cgen_subtype_val ~config envs.renv rty_def rty)
              in
              Ok
                ( Set.union constrs
                    (if definite_only then Set.filter constrs_inst ~f:defines
                     else constrs_inst),
                  Map.force_merge kind_map kind_map_def,
                  Map.Poly.set gmap ~key:f ~data:!recorder ))

  (* The whole-graph instances the file's lemmas need: of every function a
     lemma names unlabelled or as [f@def].  None without lemmas; a function
     that cannot be instantiated is left out (the lemma is then resolved
     against the copies alone, as [f@def] is refused). *)
  let lemma_graph_instances ~config envs =
    if List.is_empty !lemma_annotations then
      (Set.Poly.empty, envs.kind_map, Map.Poly.empty)
    else
      let funs =
        List.dedup_and_sort ~compare:String.compare
        @@ List.concat_map !lemma_annotations ~f:(fun content ->
            fst (graph_functions ~is_property:false envs content))
      in
      List.fold funs ~init:(Set.Poly.empty, envs.kind_map, Map.Poly.empty)
        ~f:(fun (constrs, kind_map, gmap) f ->
          match
            graph_instances ~definite_only:true ~config { envs with kind_map }
              [ f ]
          with
          | Ok (constrs', kind_map, gmap') ->
              ( Set.union constrs constrs',
                kind_map,
                Map.force_merge gmap gmap' )
          | Error _ -> (constrs, kind_map, gmap))

  let rec top_level_aux ?(functor_ctx = None) ~config envs = function
    | [] ->
        Debug.print
        @@ lazy
             "======================== Constraints Generated \
              ========================";
        (* [check_main_asserts]: a file that states its property only by
           [assert] expressions in [main] (the input form of Horn-entailment
           benchmarks, which carry no [[@@@assert]]) is checked as if it said
           [[@@@assert "typeof(main) <: T"]], [T] main's simple type with every
           refinement [true]: the assertion holds iff no [assert] in [main] or
           what it calls can fail.  Only at the end of the top-level file, only
           when the file has no assertion of its own and binds [main]. *)
        if
          Config.config.check_main_asserts && (not !has_assertion)
          && Option.is_none functor_ctx
        then
          match Rtype.Env.look_up envs.renv (Ident.Tvar "main") with
          | Some rty_main ->
              has_assertion := true;
              problems_of_check ~functor_ctx ~config envs
                [
                  ( Ident.Tvar "main",
                    Rtype.Assertion.Type
                      (Rtype.simple_val_of_sort ~config
                         (* a polymorphic [main] is asserted at its body
                            type, its type variables left free: a type
                            scheme [forall a. T] on the right of [<:] is
                            not supported *)
                         (match Rtype.sort_of_val rty_main with
                         | Sort.SPoly (_, s) -> s
                         | s -> s)) );
                ]
          | None -> []
        else []
    | { str_desc = Tstr_modtype mtd; _ } :: tl ->
        print_load_info "module type";
        let name, info = modtype_of_decl mtd in
        modtypes := Map.Poly.set !modtypes ~key:name ~data:info;
        top_level_aux ~functor_ctx ~config envs tl
    | ({ str_desc = Tstr_module mb; _ } as _item) :: tl -> (
        print_load_info "module";
        match (functor_ctx, mb.mb_expr.mod_desc) with
        | ( None,
            Tmod_functor
              ( Named (Some id, _, { mty_desc = Tmty_ident (path, _); _ }),
                { mod_desc = Tmod_structure body; _ } ) ) ->
            let x = Path.name (Path.Pident id) in
            let mt =
              match Map.Poly.find !modtypes (Path.name path) with
              | Some mt -> mt
              | None ->
                  failwith
                  @@ sprintf "module type %s not declared in this file"
                       (Path.name path)
            in
            let ctx, renv = dq_of_functor ~config envs x mt in
            let fname =
              Option.value ~default:"_" mb.mb_name.txt
            in
            let problems =
              in_functor_body := true;
              Exn.protect
                ~finally:(fun () -> in_functor_body := false)
                ~f:(fun () ->
                  top_level_aux ~functor_ctx:(Some ctx) ~config
                    { envs with renv } body.str_items)
            in
            List.map problems ~f:(fun (info, p) -> (fname ^ ": " ^ info, p))
            @ top_level_aux ~functor_ctx ~config envs tl
        | _ ->
            failwith
              "module not supported: only a top-level functor of one \
               parameter, typed by a module type declared in the file, whose \
               body is a structure")
    | { str_desc = Tstr_attribute attr; _ } :: tl
      when String.equal attr.Parsetree.attr_name.txt "property" ->
        print_load_info "attribute";
        if Option.is_some functor_ctx then
          failwith "[@@@property] inside a functor body is not supported";
        has_assertion := true;
        problems_of_property ~config envs (attr_string_content attr)
        @ top_level_aux ~functor_ctx ~config envs tl
    | { str_desc = Tstr_attribute attr; _ } :: tl
      when String.equal attr.Parsetree.attr_name.txt "chc" ->
        print_load_info "attribute";
        if Option.is_some functor_ctx then
          failwith "[@@@chc] inside a functor body is not supported";
        has_assertion := true;
        problems_of_chc ~config envs (attr_string_content attr)
        @ top_level_aux ~functor_ctx ~config envs tl
    | item :: tl -> (
        match of_struct_item ~config envs item with
        | envs, Skip -> top_level_aux ~functor_ctx ~config envs tl
        | envs, Check asserts ->
            has_assertion := true;
            problems_of_check ~functor_ctx ~config envs asserts
            @ top_level_aux ~functor_ctx ~config envs tl
        | _, Infer _ when Option.is_some functor_ctx ->
            failwith "[@@@infer] inside a functor body is not supported"
        | _, Infer _ when !eff_scheme_instances_made ->
            Common.Refusal.refuse
              "[@@@infer] is not supported in a program typed with effect \
               polymorphism of top-level bindings: each use of such a \
               binding is a copy of it, and the copies would be optimised \
               separately"
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
                  let fronts = cgen_fronts ~renv:envs.renv ~is_up:false rty in
                  let priority =
                    if List.is_empty sorted_dir_map then
                      CHCOpt.Problem.topological_sort (Map.Poly.keys dir_map) []
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
            :: top_level_aux ~functor_ctx ~config envs tl)

  (* The problems of the assertions of one [[@@@assert]] (or of the implicit
     one of [check_main_asserts]): each [type_of(x) <: rty] becomes the
     subtyping constraint between [x]'s definition, instantiated, and [rty]. *)
  and problems_of_check ~functor_ctx ~config envs asserts =
    List.map asserts ~f:(function
      | tvar, Rtype.Assertion.Type rty ->
          let rty =
            match functor_ctx with
            | None -> rty
            | Some ctx -> Rtype.subst_sorts_val ~config ctx.fc_svmap rty
          in
          let rty_def, constrs_def, kind_map_def =
            match Rtype.Env.look_up envs.renv tvar with
            | Some rty_def ->
                let dom = Rtype.Env.dep_args_of envs.renv in
                let rty_def0 = rty_def in
                let rty_def, constrs_def, kind_map_def =
                  Rtype.instantiate_val ~print:Debug.print ~config dom
                    envs.kind_map
                    (Map.Poly.empty, Map.Poly.empty)
                    (rty_def0, Rtype.sort_of_val rty)
                in
                (* An assertion is a use of the generalised value too:
                   only this instance may reveal its answer sort. *)
                ( rty_def,
                  constrs_def,
                  adm_kinds_at_instance envs.mode ~xty0:rty_def0
                    ~xty:rty_def kind_map_def )
            | None ->
                failwith @@ Ident.name_of_tvar tvar ^ " not defined"
          in
          let envs =
            {
              envs with
              kind_map = Map.force_merge envs.kind_map kind_map_def;
            }
          in
          let constrs =
            Set.union constrs_def
            @@ cgen_subtype_val ~config envs.renv rty_def rty
          in
          (* the whole-graph instances the lemmas speak about *)
          let gconstrs, kind_map, gmap =
            match functor_ctx with
            | None -> lemma_graph_instances ~config envs
            | Some _ -> (Set.Poly.empty, envs.kind_map, Map.Poly.empty)
          in
          let envs = { envs with kind_map } in
          let constrs = Set.union constrs gconstrs in
          let pcsp =
            match (functor_ctx, !pp_universals) with
            | None, [] -> pcsp_of envs constrs
            | None, unis -> pp_pcsp_of envs unis constrs
            | Some ctx, _ ->
                let bpvs =
                  Set.Poly.of_list
                  @@ Map.Poly.(keys !mu_preds @ keys !nu_preds)
                in
                let constrs, dep_map =
                  dq_constraints ctx bpvs (Set.union envs.constrs constrs)
                in
                (* a positive existential with an unknown in scope
                   becomes a functional predicate (an FN unknown, as on
                   the [infer] path) rather than a Skolem function:
                   the dump can state the former and not the latter *)
                pcsp_of ~skolem_pred:true
                  ~dq:(Some (ctx.fc_sorts, ctx.fc_unis, dep_map))
                  { envs with constrs = Set.Poly.empty }
                  constrs
          in
          Debug.print @@ lazy "\n*** constraints generated:\n";
          ( sprintf "type_of(%s) <: %s" (name_of_tvar tvar)
              (Rtype.str_of_val ~config rty),
            Problem.PAssertion
              ( !mu_preds,
                !nu_preds,
                pcsp,
                lemmas_of_annotations ~config envs gmap pcsp ) )
      | tvar, Rtype.Assertion.FinEff eff ->
          Debug.print
          @@ lazy
               (sprintf "fin_eff_of(%s) <: %s" (name_of_tvar tvar)
                  (Grammar.RegWordExp.str_of Fn.id eff));
          assert false
      | tvar, Rtype.Assertion.InfEff eff ->
          Debug.print
          @@ lazy
               (sprintf "inf_eff_of(%s) <: %s" (name_of_tvar tvar)
                  (Grammar.RegWordExp.str_of Fn.id eff));
          assert false)

  (* The problem of a [[@@@property "..."]] (the application notation): each
     function the property names is instantiated at its simple type with
     every refinement [true] -- an assertion [type_of(f) <: T] that checks
     nothing -- which brings its definition's constraints, and so its graph
     predicate, into the problem; the property's instances over the copies of
     those predicates are added as goal clauses (the notation refuses a
     property that claims an application returns a value, so every graph atom
     of a property is a premise).  The answer is [sat] iff every instance
     holds in a solution, i.e. the property holds of the copies' graphs; a
     copy's graph is contained in the function's, and the copy made here has
     the whole graph (its argument refinements are [true]), so the property
     holds of the functions' graphs iff the answer can be [sat].  The
     functions containing the labelled calls the property or a lemma names
     are instantiated the same way, so that the labelled copies are part of
     the problem (in a property, every graph and argument atom is a premise,
     and a labelled copy's graph is contained in the function's graph too).
     A property that cannot be read stops the translation, since it is the
     file's question. *)
  and problems_of_property ~config envs content =
    Rtype.cgen_config := config;
    Rtype.renv_ref := envs.renv;
    set_dtenv envs.dtenv;
    let fail why =
      failwith (sprintf "[@@@property %S] refused: %s" content why)
    in
    match formula_of_notation ~is_property:true envs.renv content with
    | Error why -> fail why
    | Ok phi ->
        problems_of_goals ~config envs ~notation_preds:[]
          ~refusal:(sprintf "[@@@property %S] refused: %s" content)
          ~info:("property " ^ content) ~aux_preds:[] [ phi ]

  (* The problem of a [[@@@chc "..."]] block: as a property's, its clauses'
     function applications resolved the same way, each definite clause
     instantiated over the copies like a goal and added to the problem as the
     definition of its auxiliary predicate, and each query a goal. *)
  and problems_of_chc ~config envs content =
    Rtype.cgen_config := config;
    Rtype.renv_ref := envs.renv;
    set_dtenv envs.dtenv;
    let fail why = failwith (sprintf "[@@@chc %S] refused: %s" content why) in
    match formulas_of_chc envs.renv content with
    | Error why -> fail why
    | Ok (phis, preds) ->
        problems_of_goals ~config envs ~notation_preds:preds
          ~refusal:(sprintf "[@@@chc %S] refused: %s" content)
          ~info:("chc " ^ content) ~aux_preds:(List.map preds ~f:fst) phis

  (* [problems_of_goals ~config envs ~refusal ~info ~aux_preds phis]: the
     problem whose goals are the instances of the read notations [phis] over
     the copies of the graphs they name (with the whole-graph instance of
     each function they name and of each function containing a labelled call
     they or a lemma name); [aux_preds] are the auxiliary predicates of a
     [[@@@chc]] block, refused when a predicate of the generated problem has
     the name one of them takes. [notation_preds] are visible only while
     resolving this problem's lemmas, never to an independent property or
     assertion. A refusal raises [Failure (refusal why)]. *)
  and problems_of_goals ~config envs ~notation_preds ~refusal ~info ~aux_preds phis =
    let fail why = failwith (refusal why) in
    (* the functions the goals and the lemmas speak about, and those
       containing the labelled calls they name, each instantiated with its
       whole graph *)
    let funs, enclosing =
      let fs, es = List.unzip (List.map phis ~f:graph_functions_of_formula) in
      (List.concat fs, List.concat es)
    in
    let lemma_funs, lemma_enclosing =
      List.unzip
      @@ List.map !lemma_annotations
           ~f:(graph_functions ~preds:notation_preds ~is_property:false envs)
    in
    let funs = List.dedup_and_sort ~compare:String.compare funs in
    let others =
      List.filter ~f:(Fn.non (List.mem funs ~equal:String.equal))
      @@ List.dedup_and_sort ~compare:String.compare
      @@ enclosing @ List.concat lemma_funs @ List.concat lemma_enclosing
    in
    (* the property's own functions with their assertions' goals, as the
       property asks them too; the others for their graphs only *)
    let constrs, kind_map, gmap =
      match
        Result.bind (graph_instances ~config envs funs)
          ~f:(fun (constrs, kind_map, gmap) ->
            Result.map
              (graph_instances ~definite_only:true ~config
                 { envs with kind_map } others)
              ~f:(fun (constrs', kind_map, gmap') ->
                ( Set.union constrs constrs',
                  kind_map,
                  Map.force_merge gmap gmap' )))
      with
      | Ok r -> r
      | Error why -> fail why
    in
    let envs = { envs with kind_map } in
    let penv =
      Set.to_list
      @@ Set.concat_map (Set.union envs.constrs constrs) ~f:(fun phi ->
          Formula.pred_sort_env_of phi)
    in
    List.iter aux_preds ~f:(fun p ->
        let (Ident.Pvar n) = chc_pred_pvar p in
        if List.exists penv ~f:(fun (Ident.Pvar m, _) -> String.equal m n) then
          fail
            (sprintf
               "the predicate %s would be %s, a predicate the program's \
                translation already has"
               p n));
    match
      Result.combine_errors
        (List.map phis ~f:(instances_of_formula penv gmap))
    with
    | Error whys -> fail (String.concat ~sep:"; " whys)
    | Ok goals ->
        let goals = List.concat goals in
        let constrs = Set.union constrs (Set.Poly.of_list goals) in
        let pcsp =
          match !pp_universals with
          | [] -> pcsp_of envs constrs
          | unis -> pp_pcsp_of envs unis constrs
        in
        [
          ( info,
            Problem.PAssertion
              ( !mu_preds,
                !nu_preds,
                pcsp,
                lemmas_of_annotations ~preds:notation_preds ~config envs gmap pcsp ) );
        ]

  (* [collect_copy_labels ts]: the labels of the file's calls
     [(f a1 ... an [@copy lbl])] into [copy_label_sites], each refused label
     named on stderr with the reason: a payload that is not one identifier, a
     label not on an application of a function bound at the top level of the
     file, the reserved label [def], and a label written on more than one
     call (a label names one call's copy). *)
  (* The check of [[@@@mode "hfl_prop_as_probability"]] and
     [[@@@mode "hfl_prop_as_liberal_probability"]] (named by [mode_name] in
     the refusal): refuses a file
     that is not a sub-probability term, i.e. one in which some answer value
     ([prop], an OCaml [float] at the result of a function) can exceed 1 or
     fall below 0 when every continuation answers within [0, 1].

     Contract.  Assumes [ts] is the file's typed tree.  Raises
     [Common.Refusal.Refused] naming the line of the first offending answer
     expression; returns unit otherwise, and then every [float]-valued body
     of a function in the file is built, at answer positions, only from
     - constants in [0, 1] (float literals, names bound by [let] to a
       constant expression, and [+.], [-.], [*.], [/.], [~-.] of those);
     - weighted sums [c1 *. e1 +. ... +. cn *. en] with constants [ci >= 0]
       and [c1 + ... + cn <= 1], a constant term [c] counting as [c *. 1];
     - products [e1 *. e2] of two such expressions, [min], [max];
     - applications of a function bound in the file or of a parameter (a
       continuation or a recursive call: their answers are in [0, 1] by
       induction, since every function body in the file is checked), and of
       the external [unif] (an integral against a probability measure);
     - [if], [match], [let], [;] whose answer branches are such expressions,
       and names [let]-bound to one.
     These are exactly the operators that map [0, 1] into [0, 1] and are
     monotone and continuous for both increasing and decreasing chains, so the
     term is a lambda-HFL term over [0, 1] in either order: in the usual order
     its least fixed point is its least fixed point over [0, infinity] and the
     expectation mode's typing rules apply unchanged; in the opposite order
     the same rules apply with the template admissible there.  Deliberately refused although they can stay within
     [0, 1]: [1.0 -. e] for an answer [e] (antitone, so not an operator of a
     fixed-point model), a weight that is not a constant (such as a value
     sampled by [unif]), and a [float] parameter used as an answer (the
     check cannot tell a probability argument from a data argument).  The
     check reads every function whose result is a [float]: in this mode a
     function computing a [float] datum rather than an answer is refused
     unless its body happens to satisfy the rules, and so is a function
     whose result is a tuple with a [float] component (an answer of the
     cost-moment or conditional readings). *)
  let probability_prescan ~mode_name (ts : Typedtree.structure) =
    (* keyed by the compiler's identifiers, which are unique per binding
       (structural equality on them is identity of the binding) *)
    let defs = Hashtbl.Poly.create () in
    let externals = Hash_set.Poly.create () in
    let key id = id in
    let name_of id = Path.name (Path.Pident id) in
    let mem_visiting visiting k = List.mem visiting k ~equal:Stdlib.( = ) in
    let record_binding (vb : Typedtree.value_binding) =
      match vb.vb_pat.pat_desc with
      | Tpat_var (id, _, _) -> Hashtbl.set defs ~key:(key id) ~data:vb.vb_expr
      | _ -> ()
    in
    let collector =
      {
        Tast_iterator.default_iterator with
        value_binding =
          (fun self vb ->
            record_binding vb;
            Tast_iterator.default_iterator.value_binding self vb);
        structure_item =
          (fun self item ->
            (match item.str_desc with
            | Tstr_primitive vd -> Hash_set.add externals (key vd.val_id)
            | _ -> ());
            Tast_iterator.default_iterator.structure_item self item);
      }
    in
    collector.structure collector ts;
    let is_float_type env ty =
      match Types.get_desc (Ctype.expand_head env ty) with
      | Tconstr (p, [], _) -> Path.same p Predef.path_float
      | _ -> false
    in
    let is_float (e : Typedtree.expression) = is_float_type e.exp_env e.exp_type in
    (* a tuple with a [float] component: the answer type of the cost-moment
       and conditional readings, not a probability *)
    let is_float_tuple (e : Typedtree.expression) =
      match Types.get_desc (Ctype.expand_head e.exp_env e.exp_type) with
      | Ttuple tys -> List.exists tys ~f:(fun (_, ty) -> is_float_type e.exp_env ty)
      | _ -> false
    in
    let positional args =
      List.filter_map args ~f:(function
        | Asttypes.Nolabel, Typedtree.Arg e -> Some e
        | _ -> None)
    in
    (* [Some (name, args)] when [e] applies a [Stdlib] value *)
    let stdlib_app (e : Typedtree.expression) =
      match e.exp_desc with
      | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, args) -> (
          match String.chop_prefix (Path.name path) ~prefix:"Stdlib." with
          | Some name -> Some (name, positional args)
          | None -> None)
      | _ -> None
    in
    let line (e : Typedtree.expression) = e.exp_loc.loc_start.pos_lnum in
    (* the value of a constant expression; [visiting] guards against a
       definition reached again through itself *)
    let rec const_of visiting (e : Typedtree.expression) =
      match e.exp_desc with
      | Texp_constant (Const_float r) -> Some (Q.of_string r)
      | Texp_ident (Pident id, _, _) -> (
          let k = key id in
          if mem_visiting visiting k then None
          else
            match Hashtbl.find defs k with
            | Some d -> const_of (k :: visiting) d
            | None -> None)
      | _ -> (
          match stdlib_app e with
          | Some ("~-.", [ a ]) -> Option.map (const_of visiting a) ~f:Q.neg
          | Some (op, [ a; b ]) -> (
              match (const_of visiting a, const_of visiting b) with
              | Some x, Some y -> (
                  match op with
                  | "+." -> Some Q.(x + y)
                  | "-." -> Some Q.(x - y)
                  | "*." -> Some Q.(x * y)
                  | "/." when not (Q.equal y Q.zero) -> Some Q.(x / y)
                  | _ -> None)
              | _ -> None)
          | _ -> None)
    in
    let const_of = const_of [] in
    let ( let* ) r f = Result.bind r ~f in
    let all = Result.all_unit in
    (* the weights of [e] read as a weighted sum of answers *)
    let rec weights visiting (e : Typedtree.expression) =
      match const_of e with
      | Some c ->
          if Q.(c < zero) then
            Error (sprintf "line %d: a negative constant answer" (line e))
          else Ok [ c ]
      | None -> (
          let scale c es =
            if Q.(c < zero) then
              Error (sprintf "line %d: a negative weight" (line e))
            else
              let* ws = weights visiting es in
              Ok (List.map ws ~f:(Q.mul c))
          in
          match stdlib_app e with
          | Some ("+.", [ a; b ]) ->
              let* wa = weights visiting a in
              let* wb = weights visiting b in
              Ok (wa @ wb)
          | Some ("*.", [ a; b ]) -> (
              match (const_of a, const_of b) with
              | Some c, _ -> scale c b
              | _, Some c -> scale c a
              | None, None ->
                  let* () = bounded visiting a in
                  let* () = bounded visiting b in
                  Ok [ Q.one ])
          | Some ("/.", [ a; b ]) -> (
              match const_of b with
              | Some c when Q.(c > zero) -> scale (Q.inv c) a
              | _ ->
                  Error
                    (sprintf "line %d: a division by a non-constant" (line e)))
          | _ ->
              let* () = atom visiting e in
              Ok [ Q.one ])
    (* [e] is an answer in [0, 1] *)
    and bounded visiting e =
      let* ws = weights visiting e in
      let total = List.fold ws ~init:Q.zero ~f:Q.add in
      if Q.(total <= one) then Ok ()
      else
        Error
          (sprintf
             "line %d: the weights of this answer sum to %s > 1 (a cost added, \
              or not a sub-probability combination)"
             (line e) (Q.to_string total))
    (* [e] is an answer in [0, 1] that is not a sum or a product *)
    and atom visiting (e : Typedtree.expression) =
      match e.exp_desc with
      | Texp_ifthenelse (_, a, Some b) ->
          let* () = bounded visiting a in
          bounded visiting b
      | Texp_let (_, _, body) | Texp_sequence (_, body) -> bounded visiting body
      | Texp_match (_, comp_cases, val_cases, _) ->
          let* () =
            all
              (List.map comp_cases ~f:(fun c -> bounded visiting c.c_rhs))
          in
          all (List.map val_cases ~f:(fun c -> bounded visiting c.c_rhs))
      | Texp_ident (Pident id, _, _) -> (
          let k = key id in
          match Hashtbl.find defs k with
          | Some d when not (mem_visiting visiting k) ->
              bounded (k :: visiting) d
          | _ ->
              Error
                (sprintf
                   "line %d: %s is used as an answer, but it is a parameter or \
                    a recursive name whose value is not known to lie in [0, 1]"
                   (line e) (name_of id)))
      | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, args) -> (
          match (path, String.chop_prefix (Path.name path) ~prefix:"Stdlib.") with
          | _, Some ("min" | "max") ->
              all (List.map (positional args) ~f:(bounded visiting))
          | _, Some "-." ->
              Error
                (sprintf
                   "line %d: a difference of answers (even 1 -. e, which stays \
                    in [0, 1], is antitone and not an operator of a \
                    fixed-point model)"
                   (line e))
          | _, Some name ->
              Error
                (sprintf "line %d: Stdlib.%s is applied at an answer position"
                   (line e) name)
          | Pident id, None
            when Hash_set.mem externals (key id)
                 && not (String.equal (name_of id) "unif") ->
              Error
                (sprintf
                   "line %d: the external %s is applied at an answer position"
                   (line e) (name_of id))
          | _ -> Ok ())
      | _ ->
          Error
            (sprintf "line %d: an answer expression of a shape this mode does \
                      not read"
               (line e))
    in
    let check_body (body : Typedtree.expression) =
      if is_float_tuple body then
        Common.Refusal.refuse
          "[hfl] refused in [@@@mode \"%s\"]: line %d: a function answers a \
           tuple of floats; the probability mode reads one probability per \
           answer (tuples are the cost-moment and conditional readings)"
          mode_name (line body)
      else if is_float body then
        match bounded [] body with
        | Ok () -> ()
        | Error why ->
            Common.Refusal.refuse "[hfl] refused in [@@@mode \"%s\"]: %s"
              mode_name why
    in
    let checker =
      {
        Tast_iterator.default_iterator with
        expr =
          (fun self (e : Typedtree.expression) ->
            (match e.exp_desc with
            | Texp_function (_, Tfunction_body body) -> check_body body
            | Texp_function (_, Tfunction_cases { cases; _ }) ->
                List.iter cases ~f:(fun c -> check_body c.c_rhs)
            | _ -> ());
            Tast_iterator.default_iterator.expr self e);
      }
    in
    checker.structure checker ts

  (* Reads the file's [[@@@mode]] and every binding's [[@@fix]] before
     translation, and refuses what the Boolean mode cannot read soundly:
     - in the probability mode, a term that is not a sub-probability term
       ([probability_prescan]);
     - a [[@@fix]] in a file not in the Boolean HFL mode (the ordinary mode's
       partial-correctness rule for [let rec] is unsound for a fixed point);
     - both kinds of fixed point in one file (alternation: one lambda-HFL
       model has one fixpoint kind);
     - [exists_int] applied inside the body of a greatest fixed point, or
       [forall_int] inside a least one (other than in the definitions of the
       quantifiers themselves): such a quantifier over an infinite domain is
       not Scott-continuous in that order, the Kleene limit the typing rule
       reasons about can then differ from the fixed point, and no sound rule
       is known.
     Sets the sort of [prop] in refinement types: [bool] in the Boolean mode,
     the reals otherwise. *)
  let hfl_prescan (ts : Typedtree.structure) =
    Hashtbl.clear hfl_fix_is_nu;
    let mode_of_file =
      List.find_map ts.str_items ~f:(function
        | { str_desc = Tstr_attribute attr; _ }
          when String.equal attr.Parsetree.attr_name.txt "mode" ->
            Some (attr_string_content attr)
        | _ -> None)
    in
    let is_bool_mode =
      Option.equal String.equal mode_of_file (Some "hfl_prop_as_bool")
    in
    Typeinf.prop_sort := if is_bool_mode then T_bool.SBool else T_real.SReal;
    (match mode_of_file with
    | Some
        (("hfl_prop_as_probability" | "hfl_prop_as_liberal_probability") as
         mode_name) ->
        probability_prescan ~mode_name ts
    | _ -> ());
    let fix_of (vb : Typedtree.value_binding) =
      List.find_map vb.vb_attributes ~f:(fun a ->
          if String.equal a.Parsetree.attr_name.txt "fix" then
            Some (attr_string_content a)
          else None)
    in
    let name_of (vb : Typedtree.value_binding) =
      match vb.vb_pat.pat_desc with
      | Tpat_var (_, name, _) -> Some name.txt
      | _ -> None
    in
    let applies_quantifier q (e : Typedtree.expression) =
      let found = ref false in
      let it =
        {
          Tast_iterator.default_iterator with
          expr =
            (fun sub e ->
              (match e.exp_desc with
              | Texp_ident (path, _, _)
                when String.equal (Path.last path) q ->
                  found := true
              | _ -> ());
              Tast_iterator.default_iterator.expr sub e);
        }
      in
      it.expr it e;
      !found
    in
    let quantifier_definitions =
      [ "forall_int"; "exists_int"; "forall_int_from"; "exists_int_from" ]
    in
    let kinds = ref [] in
    List.iter ts.str_items ~f:(function
      | { str_desc = Tstr_value (is_rec, vbs); _ } ->
          List.iter vbs ~f:(fun vb ->
              let is_nu =
                match fix_of vb with
                | None when is_bool_mode && Poly.(is_rec = Asttypes.Recursive)
                  ->
                    Some true
                | None -> None
                | Some k ->
                    if not is_bool_mode then
                      Common.Refusal.refuse "%s"
                        "[hfl] a binding carries [@@fix] but the file is not \
                         in [@@@mode \"hfl_prop_as_bool\"]: RCaml's ordinary \
                         reading of let rec is unsound for a fixed point";
                    Some
                      (match k with
                      | "nu" -> true
                      | "mu" -> false
                      | _ ->
                          Common.Refusal.refuse "[hfl] [@@fix %S]: expected nu or mu"
                            k)
              in
              match (is_nu, name_of vb) with
              | Some is_nu, Some n ->
                  Hashtbl.set hfl_fix_is_nu ~key:n ~data:is_nu;
                  if not (List.mem quantifier_definitions n ~equal:String.equal)
                  then (
                    kinds := is_nu :: !kinds;
                    let bad = if is_nu then "exists_int" else "forall_int" in
                    if applies_quantifier bad vb.vb_expr then
                      Common.Refusal.refuse
                        "[hfl] refused: %s inside the %s fixed point %s (the \
                         quantifier is not continuous in that order, so no \
                         sound typing rule covers it)"
                        bad
                        (if is_nu then "greatest" else "least")
                        n)
              | _ -> ())
      | _ -> ());
    if
      List.exists !kinds ~f:Fn.id && List.exists !kinds ~f:not
    then
      Common.Refusal.refuse "%s"
        "[hfl] refused: greatest and least fixed points in one file \
         (alternation)"

  let collect_copy_labels (ts : Typedtree.structure) =
    Hashtbl.clear copy_label_sites;
    let refuse lbl why =
      Out_channel.eprintf "[RCaml] label [@copy %s] refused: %s\n%!" lbl why
    in
    let tops =
      List.concat_map ts.str_items ~f:(fun item ->
          match item.str_desc with
          | Tstr_value (_, vbs) ->
              List.filter_map vbs ~f:(fun vb ->
                  match vb.vb_pat.pat_desc with
                  | Tpat_var (id, name, _) -> Some (Path.Pident id, name.txt)
                  | _ -> None)
          | _ -> [])
    in
    let seen = Hashtbl.create (module String) in
    let site enclosing (expr : Typedtree.expression) =
      List.iter expr.exp_attributes ~f:(fun attr ->
          if String.equal attr.Parsetree.attr_name.txt "copy" then
            match MBcgen.copy_label_of_attrs [ attr ] with
            | None ->
                Out_channel.eprintf
                  "[RCaml] attribute [@copy] refused: its payload must be one \
                   label, a lowercase identifier\n%!"
            | Some lbl ->
                let result =
                  if String.equal lbl label_reserved then
                    Error
                      (sprintf "%s is reserved (f@%s names f's whole graph)"
                         label_reserved label_reserved)
                  else
                    match expr.exp_desc with
                    | Texp_apply ({ exp_desc = Texp_ident (path, _, _); _ }, _)
                      -> (
                        match
                          List.find tops ~f:(fun (p, _) -> Path.same p path)
                        with
                        | Some (_, f) -> Ok (f, enclosing)
                        | None ->
                            Error
                              (sprintf
                                 "it is on a call of %s, which is not a \
                                  function bound at the top level of the file"
                                 (Path.name path)))
                    | _ ->
                        Error
                          "it is not on a call (a label names the copy of a \
                           function's refinement that one call makes)"
                in
                Hashtbl.update seen lbl ~f:(fun n -> 1 + Option.value n ~default:0);
                let result =
                  match Hashtbl.find copy_label_sites lbl with
                  | None -> result
                  | Some _ ->
                      Error
                        (sprintf "it is written on %d calls; a label names one"
                           (Hashtbl.find_exn seen lbl))
                in
                Hashtbl.set copy_label_sites ~key:lbl ~data:result)
    in
    List.iter ts.str_items ~f:(fun item ->
        let enclosing =
          match item.str_desc with
          | Tstr_value (_, [ { vb_pat = { pat_desc = Tpat_var (_, name, _); _ }; _ } ])
            ->
              Some name.txt
          | _ -> None
        in
        let iterator =
          {
            Tast_iterator.default_iterator with
            expr =
              (fun self expr ->
                site enclosing expr;
                Tast_iterator.default_iterator.expr self expr);
          }
        in
        iterator.structure_item iterator item);
    Hashtbl.iteri copy_label_sites ~f:(fun ~key ~data ->
        match data with Error why -> refuse key why | Ok _ -> ())

  let top_level ~config ps =
    try
      let ts, _, _, _, _ =
        Typemod.type_structure (Compmisc.initial_env ()) ps
      in
      (* the module [MBcgen] here is the functor instance; the alias rewrite
         is a function of the typed tree alone, outside the functor *)
      let ts = RCaml__MBcgen.desugar_case_aliases ts in
      (*Debug.print @@ lazy (sprintf "typedtree structure:\n%s"
                             (MBcgen.str_of_typedtree_structure ts));*)
      init_dtenv ();
      init_fenv ();
      init_dummy_term_senv ();
      mu_preds := Map.Poly.empty;
      nu_preds := Map.Poly.empty;
      modtypes := Map.Poly.empty;
      pp_universals := [];
      pp_deps := Map.Poly.empty;
      has_assertion := false;
      Hash_set.clear noticed_attributes;
      pending_copy_label := None;
      eff_scheme_instances_made := false;
      Hashtbl.clear copy_label_copies;
      collect_copy_labels ts;
      hfl_prescan ts;
      (* Check the file-level cardinality independently of traversal order
         and of whether a block declares any auxiliary predicates. *)
      if
        List.count ts.str_items ~f:(function
          | { str_desc = Tstr_attribute attr; _ } ->
              String.equal attr.Parsetree.attr_name.txt "chc"
          | _ -> false)
        > 1
      then failwith "[@@@chc] refused: a file states at most one [@@@chc] block";
      lemma_annotations :=
        List.filter_map ts.str_items ~f:(function
          | { str_desc = Tstr_attribute attr; _ }
            when String.equal attr.Parsetree.attr_name.txt "lemma" ->
              Some (attr_string_content attr)
          | _ -> None);
      (* installed here rather than when the functor is applied, so that the
         copies go to the definitions of the instance generating now *)
      Rtype.instantiate_fixpoint_preds := instantiate_fixpoint_preds;
      inst_pvs_dtrenv := Set.Poly.empty;
      dtrenv := Map.Poly.empty;
      update_dtrenv_with_dts ~config (Map.data @@ get_dtenv ());
      MBcgen.ref_id := Map.Poly.empty;
      (* which operations are answer-type polymorphic is decided once per
         file, before its first item *)
      MBcgen.set_atp_operations ts;
      Rtype.cgen_config := config;
      Rtype.renv_ref := Rtype.Env.mk_empty ();
      let envs =
        {
          mode = OCaml;
          constrs = Set.Poly.empty;
          exi_senv = Map.Poly.empty;
          kind_map = Map.Poly.empty;
          fenv = get_fenv ();
          lifted_universals = Map.Poly.empty;
          dtenv = get_dtenv ();
          renv = !Rtype.renv_ref;
          eff_schemes = Map.Poly.empty;
        }
      in
      Result.return @@ top_level_aux ~config envs ts.str_items
    with
    | Typemod.Error (loc, env, err) ->
        failwith @@ "Typemod.Error:\n"
        ^ MBcgen.str_of_stdbuf ~f:Location.print_report
        @@ Typemod.report_error ~loc env err
    | Env.Error _err ->
        failwith
        @@ "Env.Error:" (*^ MBcgen.str_of_stdbuf ~f:Env.report_error err*)
    | Typecore.Error (loc, env, err) ->
        failwith @@ "Typecore.Error:\n"
        ^ MBcgen.str_of_stdbuf ~f:Location.print_report
        @@ Typecore.report_error ~loc env err

  (* Translates a parsed structure (a file's or a string's).  With [toplevel_effects = Fail_on_escape] (RCaml's
     configuration), an operation or
     exception that escapes a top-level item is a failure, as in OCaml: the
     file is translated as is, and each time [of_struct_item] meets an item
     that performs an operation at the top level, that item is wrapped by
     [ToplevelHandler.wrap] in a handler whose every clause fails and the file
     is translated again.  Contract: an item that is pure in the unwrapped
     translation is never wrapped, so a file with no such item is translated
     exactly as with [Refuse]; each pass wraps one more item, so there are at
     most as many passes as items; an item that cannot be wrapped, or is still
     impure once wrapped, is refused with the message [Refuse] gives, followed
     by the reason. *)
  let of_parsed_structure config res =
    let ps =
      GuardSyntax.desugar @@ EffectSyntax.desugar ~print:Debug.print res
    in
    match Config.config.toplevel_effects with
    | ToplevelHandler.Refuse -> top_level ~config ps
    | ToplevelHandler.Fail_on_escape ->
        let rec pass wrapped =
          (* A pooled Z3 context keeps the datatypes an earlier pass declared,
             and the rewritten program redeclares [eff] and [exn] with the
             parameters [ToplevelHandler.wrap] gives their parameterless
             constructors: a re-read starts from contexts that declare
             nothing. *)
          if not (List.is_empty wrapped) then
            Z3Smt.Z3interface.clear_instance_pool ();
          let ps' =
            match ToplevelHandler.wrap wrapped ps with
            | Ok ps' -> ps'
            | Error why ->
                (* [pass] wraps only items [wrap] accepted alone *)
                failwith ("[from_ml_file] " ^ why)
          in
          match
            Exn.protect
              ~finally:(fun () -> wrap_impure_toplevel := false)
              ~f:(fun () ->
                wrap_impure_toplevel := true;
                top_level ~config ps')
          with
          | res -> res
          | exception Impure_toplevel (loc, msg) -> (
              let same_loc (si : Parsetree.structure_item) =
                (not loc.Location.loc_ghost)
                && Stdlib.( = ) si.pstr_loc.loc_start loc.loc_start
                && Stdlib.( = ) si.pstr_loc.loc_end loc.loc_end
              in
              match List.findi ps ~f:(fun _ si -> same_loc si) with
              | None ->
                  Common.Refusal.refuse
                    "%s (not an item of the file's own structure)" msg
              | Some (i, _) when List.mem wrapped i ~equal:Int.equal ->
                  Common.Refusal.refuse
                    "%s (it stays impure inside a handler that fails on every \
                     operation: its effect is a change of answer type or a \
                     temporal effect, or an exception of OCaml's built-in exn \
                     type)"
                    msg
              | Some (i, _) -> (
                  match ToplevelHandler.wrap [ i ] ps with
                  | Ok _ ->
                      Debug.print
                      @@ lazy
                           (sprintf
                              "item %d performs an operation at the top level: \
                               read under a handler that fails on every \
                               operation"
                              i);
                      pass (i :: wrapped)
                  | Error why -> Common.Refusal.refuse "%s (%s)" msg why))
        in
        pass []

  let from_ml_file config filename =
    In_channel.with_file filename ~f:(fun ic ->
        let lexbuf = Lexing.from_channel ic in
        Lexing.set_filename lexbuf filename;
        try Parse.implementation lexbuf
        with e ->
          LexingHelper.print_error_information lexbuf;
          raise e)
    |> of_parsed_structure config

  (* [from_ml_file] on a structure given as text; [filename] names it in
     messages.  The front ends that print an OCaml representation (the HFL
     solvers) use it, so that no temporary file is written. *)
  let from_ml_string config ~filename text =
    let lexbuf = Lexing.from_string text in
    Lexing.set_filename lexbuf filename;
    (try Parse.implementation lexbuf
     with e ->
       LexingHelper.print_error_information lexbuf;
       raise e)
    |> of_parsed_structure config
end
