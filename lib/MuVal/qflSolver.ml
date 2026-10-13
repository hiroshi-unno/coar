open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld

(* The QFL / supermartingale half of what used to be one 3,433-line functor in
   [MuVal.Solver].  Of that file's nineteen muCLP-side
   definitions this half referenced exactly one, the ten-line [pcsp_solver]
   helper, which is duplicated below rather than threaded through -- the coupling
   cost more than the ten lines.  [MuVal.Solver] re-exports [solve_qfl], so no
   caller changes. *)
module Make (Cfg : Config.ConfigType) = struct
  let config = Cfg.config

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let pcsp_solver ~primal (* ToDo *) =
    let open Or_error in
    ExtFile.unwrap
      (if primal then config.pcsp_solver_primal else config.pcsp_solver_dual)
    >>= fun cfg ->
    PCSPSolver.Solver.(
      Ok
        (module Make (struct
          let config = cfg
        end) : SolverType))

  (** validity checking for Quantitative Fixpoint Logic *)

  let underapprox_of (pred : QFL.Pred.t) =
    let cond, template =
      Templ.underapprox_of
        ~cond_degree:config.quant_underapprox_templ_cond_degree
        ~term_degree:config.quant_underapprox_templ_term_degree pred.args
        pred.body
    in
    ( cond,
      template.templ_params,
      template.templ_constrs,
      { pred with body = template.quant_pred } )

  let delta_of (preds : QFL.Pred.t list) =
    let zero =
      Map.Poly.of_alist_exn
        (List.map preds ~f:(fun pred ->
             (pred.name, (pred.args, T_real.rzero ()))))
    in
    List.map preds ~f:(fun pred ->
        QFL.Pred.simplify
          {
            pred with
            body =
              (let rec aux = function
                 | Term.FunApp (T_bool.IfThenElse, [ cond; t1; t2 ], _) ->
                     T_bool.mk_if_then_else cond (aux t1) (aux t2)
                 | Term.FunApp
                     ( FVar ((Ident.Tvar ("min" | "max") as fvar), sargs, sret),
                       args,
                       _ ) ->
                     Term.mk_fvar_app fvar sargs sret (List.map args ~f:aux)
                 | t ->
                     Normalizer.normalize_term
                     @@ T_real.mk_rsub t (Term.subst_funcs zero t)
               in
               aux pred.body);
          })

  let str_of_sol (name, (args, quant_pred)) =
    sprintf "%s %s |-> %s" (Ident.name_of_tvar name)
      (str_of_sort_env_list Term.str_of_sort args)
      (Term.str_of quant_pred)

  let str_of_templ templ = String.concat_map_list ~sep:", " ~f:str_of_sol templ

  let print_templ templ =
    List.iter templ ~f:(fun (name, (args, quant_pred)) ->
        Debug.print @@ lazy (str_of_sol (name, (args, quant_pred))))

  let str_of_inv_sol (name, (args, pred)) =
    sprintf "%s %s |-> %s" (Ident.name_of_tvar name)
      (str_of_sort_env_list Term.str_of_sort args)
      (Formula.str_of pred)

  let print_inv_templ templ =
    List.iter templ ~f:(fun (name, (args, pred)) ->
        Debug.print @@ lazy (str_of_inv_sol (name, (args, pred))))

  (* Template coefficients, weights and epsilons below are prefixed fresh
     names ([r], [p], [eps], [r_], [q_]) placed in constraints that also
     mention the program's variables.  A prefixed name is the prefix followed
     by a global counter and is not fresh against a name the input spells, so
     a program variable [r1] -- quantified over every state -- would be
     identified with a parameter chosen once.  These are the names such a
     parameter must avoid: every predicate, its arguments and the variables of
     its body. *)
  let names_of_preds (preds : QFL.Pred.t list) =
    Set.Poly.union_list
    @@ List.map preds ~f:(fun (pred : QFL.Pred.t) ->
        Set.add
          (Set.union
             (Set.Poly.of_list (List.map pred.args ~f:fst))
             (Term.tvs_of pred.body))
          pred.name)

  (* [names_of_preds] of the problem's predicates together with the problem's
     parameters, as a membership test built once. *)
  let taken_in_problem (qfl : QFL.Problem.t) param_senv =
    let names =
      lazy
        (Set.union (names_of_preds qfl.preds)
           (Set.Poly.of_list (List.map param_senv ~f:fst)))
    in
    fun v -> Set.mem (Lazy.force names) v

  let gen_cache_constr for_prefp (preds : QFL.Pred.t list) fsub pareto_cache =
    let rel =
      match for_prefp with First _ -> Formula.geq | Second _ -> Formula.leq
    in
    let pc_templ_params = ref Map.Poly.empty in
    let pc_constrs =
      List.concat_map preds ~f:(fun pred ->
          match Ident.name_of_tvar pred.name with
          | "Inv" ->
              let lookup name =
                List.find_exn ~f:(fun pred ->
                    String.(Ident.name_of_tvar (fst pred) = name))
                >> snd
              in
              let post =
                let post =
                  lookup "Post"
                    (List.map preds ~f:(fun pred ->
                         (pred.name, (pred.args, pred.body)))
                    @ Map.Poly.to_alist fsub)
                in
                Term.rename
                  (ren_of_sort_env_list (fst post) pred.args)
                  (snd post)
              in
              let post_inv_list =
                List.filter_map pareto_cache ~f:(function
                  | None -> None
                  | Some sol ->
                      let post = lookup "Post" sol in
                      let inv = lookup "Inv" sol in
                      Some
                        ( Term.rename
                            (ren_of_sort_env_list (fst post) pred.args)
                            (snd post),
                          Term.rename
                            (ren_of_sort_env_list (fst inv) pred.args)
                            (snd inv) ))
              in
              Debug.print ~id:None
              @@ lazy
                   (sprintf
                      "finding an inductive invariant for the new \
                       postcondition [%s] using the pareto cache:\n\
                      \  %s"
                      (Term.str_of post)
                      (String.concat ~sep:"\n  "
                         (List.map post_inv_list ~f:(fun (post, inv) ->
                              sprintf "Post |-> %s, Inv |-> %s"
                                (Term.str_of post) (Term.str_of inv)))));
              let posts, invs = List.unzip post_inv_list in
              let atoms =
                Set.concat_map ~f:(function
                  | Atom.App (Psym T_bool.(Eq | Neq), [ t1; t2 ], _) ->
                      Set.Poly.of_list
                        [ T_real.mk_rlt t1 t2; T_real.mk_rgt t1 t2 ]
                  | atm -> Set.Poly.singleton atm)
                @@ Set.Poly.union_list
                @@ Tuple2.uncurry Set.union (Term.atoms_of post)
                   :: List.map posts
                        ~f:(Term.atoms_of >> Tuple2.uncurry Set.union)
              in
              if false then
                Debug.print ~id:None
                @@ lazy
                     (sprintf "atoms involved in pareto cache:\n%s"
                     @@ String.concat_map_set ~sep:", " ~f:Atom.str_of atoms);
              let taken =
                let names =
                  lazy
                    (Set.Poly.union_list
                       (names_of_preds preds :: Term.tvs_of post
                       :: List.map (posts @ invs) ~f:Term.tvs_of))
                in
                fun v -> Set.mem (Lazy.force names) v
              in
              let r =
                if config.pareto_cache_zero_reward then T_real.rzero ()
                else
                  Term.mk_var
                    (Ident.mk_fresh_tvar_avoiding ~prefix:"r" ~taken ())
                    T_real.SReal
              in
              let ps, ws, wss, w_constrs =
                if true (*ToDo*) then (
                  (* assume that all the postconditions are piecewise constant and have the same brancing structure *)
                  let rec get_leaf_consts = function
                    | Term.FunApp (T_bool.IfThenElse, [ _; t1; t2 ], _) ->
                        get_leaf_consts t1 @ get_leaf_consts t2
                    | t -> [ t ]
                  in
                  (*let rec replace_leaf_consts ts = function
                          | Term.FunApp
                              (T_bool.IfThenElse, [ cond; t1; t2 ], info) ->
                              let t1, ts = replace_leaf_consts ts t1 in
                              let t2, ts = replace_leaf_consts ts t2 in
                              ( Term.FunApp
                                  (T_bool.IfThenElse, [ cond; t1; t2 ], info),
                                ts )
                          | _ -> (List.hd_exn ts, List.tl_exn ts)
                        in*)
                  let ws = get_leaf_consts post in
                  Debug.print ~id:None
                  @@ lazy
                       (sprintf "leaf constants in [%s]:\n  %s"
                          (Term.str_of post)
                       @@ String.concat_map_list ~sep:", " ~f:Term.str_of ws);
                  let ps =
                    List.map ws ~f:(fun _ ->
                        Term.mk_var
                          (Ident.mk_fresh_tvar_avoiding ~prefix:"p" ~taken ())
                          T_real.SReal)
                  in
                  let wss =
                    List.map posts ~f:(fun post ->
                        let ws = get_leaf_consts post in
                        Debug.print ~id:None
                        @@ lazy
                             (sprintf "leaf constants in [%s]:\n  %s"
                                (Term.str_of post)
                             @@ String.concat_map_list ~sep:", " ~f:Term.str_of
                                  ws);
                        ws)
                  in
                  (ps, ws, wss, []))
                else
                  let ps, ws =
                    List.unzip
                    @@ List.init (config.pareto_cache_num_conds + 1)
                         ~f:(fun _i ->
                           let p =
                             Term.mk_var
                               (Ident.mk_fresh_tvar ~prefix:(Some "p") ())
                               T_real.SReal
                           in
                           let w = Ident.mk_fresh_tvar ~prefix:(Some "w") () in
                           pc_templ_params :=
                             Map.add_exn !pc_templ_params ~key:w
                               ~data:T_real.SReal;
                           (p, Term.mk_var w T_real.SReal))
                  in
                  let wss =
                    List.map posts ~f:(fun _ ->
                        List.init (config.pareto_cache_num_conds + 1)
                          ~f:(fun _i ->
                            let w = Ident.mk_fresh_tvar ~prefix:(Some "w") () in
                            pc_templ_params :=
                              Map.add_exn !pc_templ_params ~key:w
                                ~data:T_real.SReal;
                            Term.mk_var w T_real.SReal))
                  in
                  let w_constrs =
                    let conds =
                      List.init (config.pareto_cache_num_conds + 1)
                        ~f:(fun _i ->
                          let templ =
                            Templ.mk_affine
                            @@ Templ.terms_of config.pareto_cache_cond_degree
                                 pred.args
                          in
                          pc_templ_params :=
                            Map.force_merge !pc_templ_params templ.templ_params;
                          templ.quant_pred)
                    in
                    let w = Templ.gen_quant_pc_template conds ws in
                    Debug.print ~id:None
                    @@ lazy
                         (sprintf "generated weight template for [%s]:\n%s"
                            (Term.str_of post) (Term.str_of w));
                    rel w post
                    :: List.map2_exn wss posts ~f:(fun ws post ->
                        let w = Templ.gen_quant_pc_template conds ws in
                        Debug.print ~id:None
                        @@ lazy
                             (sprintf "generated weight template for [%s]:\n%s"
                                (Term.str_of post) (Term.str_of w));
                        rel post w)
                  in
                  (ps, ws, wss, w_constrs)
              in
              let pres =
                (if config.pareto_cache_zero_reward then []
                 else [ Formula.geq r (T_real.rzero ()) ])
                @ Formula.leq
                    (T_real.mk_rsum (T_real.rzero ()) ps)
                    (T_real.rone ())
                  :: List.map ps ~f:(fun p -> Formula.geq p (T_real.rzero ()))
              in
              w_constrs
              @ List.map
                  ~f:
                    (Formula.subst_funcs
                       (match for_prefp with
                       | First prefp_sub -> prefp_sub
                       | Second
                           ( _prefp_templ_preds,
                             _rank_templ_preds,
                             postfp_templ_preds,
                             _ua_preds_delta ) ->
                           Map.Poly.of_alist_exn postfp_templ_preds))
              @@
              if false then (
                let param_inv = Ident.mk_fresh_tvar ~prefix:(Some "inv") () in
                let param_invs =
                  List.map invs ~f:(fun _ ->
                      Ident.mk_fresh_tvar ~prefix:(Some "inv") ())
                in
                pc_templ_params :=
                  Map.force_merge !pc_templ_params
                    (Map.Poly.of_alist_exn
                    @@ (param_inv, T_real.SReal)
                       :: List.map param_invs ~f:(fun p -> (p, T_real.SReal)));
                (Formula.mk_imply
                   (Formula.and_of @@ pres
                   @ List.map2_exn param_invs wss ~f:(fun param_inv ws ->
                       rel
                         (Term.mk_var param_inv T_real.SReal)
                         (T_real.mk_rsum r
                            (List.map2_exn ps ws ~f:T_real.mk_rmul))))
                @@ rel
                     (Term.mk_var param_inv T_real.SReal)
                     (T_real.mk_rsum r @@ List.map2_exn ps ws ~f:T_real.mk_rmul)
                )
                :: rel
                     (Term.fvar_app_of_senv pred.name pred.args T_real.SReal)
                     (Term.mk_var param_inv T_real.SReal)
                :: List.map2_exn param_invs invs ~f:(fun param_inv inv ->
                    rel (Term.mk_var param_inv T_real.SReal) inv))
              else
                [
                  Formula.mk_imply
                    (Formula.and_of @@ pres
                    @ List.map2_exn invs wss ~f:(fun inv ws ->
                        rel inv
                          (T_real.mk_rsum r
                          @@ List.map2_exn ps ws ~f:T_real.mk_rmul)))
                  @@ rel
                       (Term.fvar_app_of_senv pred.name pred.args T_real.SReal)
                       (T_real.mk_rsum r
                       @@ List.map2_exn ps ws ~f:T_real.mk_rmul);
                ]
          | "Post" -> []
          | _ -> (
              match for_prefp with
              | First prefp_sub ->
                  List.map ~f:(Formula.subst_funcs prefp_sub)
                  @@ List.map (Term.elim_min_max_list pred.body) ~f:(fun body ->
                      rel
                        (Term.fvar_app_of_senv pred.name pred.args T_real.SReal)
                        body)
              | Second
                  ( prefp_templ_preds,
                    rank_templ_preds,
                    postfp_templ_preds,
                    (ua_preds_delta : QFL.Pred.t list) ) ->
                  let postfp_args, postfp_body =
                    List.Assoc.find_exn ~equal:Stdlib.( = ) postfp_templ_preds
                      pred.name
                  in
                  let prefp_args, prefp_body =
                    List.Assoc.find_exn ~equal:Stdlib.( = ) prefp_templ_preds
                      pred.name
                  in
                  let rank_args, rank_body =
                    List.Assoc.find_exn ~equal:Stdlib.( = ) rank_templ_preds
                      pred.name
                  in
                  let ua_pred_delta =
                    List.find_exn ua_preds_delta ~f:(fun pred' ->
                        Stdlib.( = ) pred'.name pred.name)
                  in
                  let rank_sub = Map.Poly.of_alist_exn rank_templ_preds in
                  Formula.leq postfp_body
                    (Term.rename
                       (LogicOld.ren_of_sort_env_list prefp_args postfp_args)
                       prefp_body)
                  :: (List.map
                        ~f:
                          (Formula.subst_funcs
                             (Map.Poly.of_alist_exn postfp_templ_preds))
                     @@ List.map (Term.elim_min_max_list pred.body)
                          ~f:(fun body ->
                            Formula.geq body
                              (Term.fvar_app_of_senv pred.name pred.args
                                 T_real.SReal)))
                  @ List.map
                      ~f:
                        (Formula.subst_funcs
                           (Map.Poly.of_alist_exn prefp_templ_preds))
                  @@ List.map (Term.elim_min_max_list pred.body) ~f:(fun body ->
                      Formula.geq
                        (Term.fvar_app_of_senv pred.name pred.args T_real.SReal)
                        body)
                  @ List.map
                      (Term.elim_min_max_list
                      @@ Term.subst_funcs rank_sub ua_pred_delta.body)
                      ~f:(fun body ->
                        Formula.leq
                          (T_real.mk_radd
                             (Term.rename
                                (LogicOld.ren_of_sort_env_list
                                   ua_pred_delta.args rank_args)
                                body)
                             (Term.rename
                                (LogicOld.ren_of_sort_env_list prefp_args
                                   rank_args)
                                prefp_body))
                          rank_body)))
    in
    (pc_constrs, !pc_templ_params)

  let cgen_pqes_lb (qfl : QFL.Problem.t) ?accel_problem ~preds_for_fsub_domain
      query_fml fsub pareto_cache =
    let query_fml = Formula.elim_min_max_list query_fml in
    let qfl_preds_for_templates =
      match accel_problem with
      | Some accel_problem when config.enable_geometric_pla ->
          let active_names = QFL.Accel.active_pred_names accel_problem in
          List.filter qfl.preds ~f:(fun pred -> Set.mem active_names pred.name)
      | _ -> qfl.preds
    in
    let conds, templ_paramss, templ_constrss, ua_preds =
      List.unzip4 @@ List.map qfl_preds_for_templates ~f:underapprox_of
    in
    Debug.print ~id:None
    @@ lazy
         (sprintf "\nunderapproximated:\n%s\n" @@ QFL.Pred.str_of_list ua_preds);
    let strengthen_guard gen =
      List.unzip
      @@ List.map2_exn qfl_preds_for_templates conds ~f:(fun pred cond ->
          let template : Templ.templ_quant_pred =
            gen pred.args pred.body pred.annots
          in
          let templ_params, quant_pred =
            match cond with
            | None -> (template.templ_params, template.quant_pred)
            | Some cond ->
                let templ_params, quant_pred =
                  if false then
                    let templ =
                      Templ.mk_affine
                      @@ Templ.terms_of
                           config.quant_prefp_templ_term_degree (*ToDo*)
                           pred.args
                    in
                    (templ.templ_params, templ.quant_pred)
                  else (Map.Poly.empty, T_real.rzero ())
                in
                ( Map.force_merge template.templ_params templ_params,
                  T_bool.mk_if_then_else
                    (T_bool.of_formula @@ Formula.geq cond (T_real.rzero ()))
                    template.quant_pred quant_pred )
          in
          (templ_params, (pred.name, (pred.args, quant_pred))))
    in
    let prefp_templ_paramss, prefp_templ_preds =
      strengthen_guard
        (Templ.gen_quant_template ~num_conds:config.quant_prefp_templ_num_conds
           ~use_orig_ite:config.quant_prefp_templ_use_orig_ite
           ~cond_degree:config.quant_prefp_templ_cond_degree
           ~term_degree:config.quant_prefp_templ_term_degree)
    in
    let rank_templ_paramss, rank_templ_preds =
      strengthen_guard
        (Templ.gen_quant_template ~num_conds:config.quant_rank_templ_num_conds
           ~use_orig_ite:config.quant_rank_templ_use_orig_ite
           ~cond_degree:config.quant_rank_templ_cond_degree
           ~term_degree:config.quant_rank_templ_term_degree)
    in
    let coeffs = ref [] in
    let postfp_templ_paramss, postfp_templ_preds =
      strengthen_guard
        (Templ.gen_quant_template ~coeffs:(Some coeffs)
           ~num_conds:config.quant_postfp_templ_num_conds
           ~use_orig_ite:config.quant_postfp_templ_use_orig_ite
           ~cond_degree:config.quant_postfp_templ_cond_degree
           ~term_degree:config.quant_postfp_templ_term_degree)
    in
    if not @@ List.is_empty prefp_templ_preds then
      Debug.print @@ lazy "[6. Template]";
    if not @@ List.is_empty prefp_templ_preds then (
      Debug.print @@ lazy "templates for prefixpoint:";
      print_templ prefp_templ_preds);
    if not @@ List.is_empty rank_templ_preds then (
      Debug.print @@ lazy "\ntemplates for ranking supermartingales:";
      print_templ rank_templ_preds);
    if not @@ List.is_empty postfp_templ_preds then (
      Debug.print @@ lazy "\ntemplates for postfixpoint:";
      print_templ postfp_templ_preds);
    let prefp_sub = Map.Poly.of_alist_exn prefp_templ_preds in
    let rank_sub = Map.Poly.of_alist_exn rank_templ_preds in
    let postfp_sub = Map.Poly.of_alist_exn postfp_templ_preds in
    let templ_params =
      Map.force_merge_list @@ templ_paramss @ prefp_templ_paramss
      @ postfp_templ_paramss @ rank_templ_paramss
    in
    let unfolded_nonnegative_constrs =
      QFL.Problem.nonnegative_formulas_of_fsub_with_preds preds_for_fsub_domain
        fsub prefp_sub
    in
    let original_postfixpoint_constrs =
      List.map ~f:(Formula.subst_funcs postfp_sub)
      @@ List.concat_map ua_preds ~f:(fun pred ->
          List.map (Term.elim_min_max_list pred.body) ~f:(fun body ->
              Formula.geq body
                (Term.fvar_app_of_senv pred.name pred.args T_real.SReal)))
    in
    let original_prefixpoint_constrs =
      List.map ~f:(Formula.subst_funcs prefp_sub)
      @@ List.concat_map ua_preds ~f:(fun pred ->
          List.map (Term.elim_min_max_list pred.body) ~f:(fun body ->
              Formula.geq
                (Term.fvar_app_of_senv pred.name pred.args T_real.SReal)
                body))
    in
    let ua_preds_delta = delta_of ua_preds in
    Debug.print ~id:None
    @@ lazy (sprintf "\ndelta:\n%s\n" @@ QFL.Pred.str_of_list ua_preds_delta);
    let is_zero_term term =
      let normalize =
        Evaluator.simplify_term @@ Normalizer.normalize_term term
      in
      String.(Term.str_of normalize = Term.str_of (T_real.rzero ()))
    in
    let rank_delta_is_trivial =
      List.for_all ua_preds_delta ~f:(fun pred -> is_zero_term pred.body)
    in
    let original_rank_constrs =
      List.concat_map rank_templ_preds ~f:(fun (name, (rank_args, rank_body)) ->
          let ua_pred_delta =
            List.find_exn ua_preds_delta ~f:(fun pred ->
                Stdlib.( = ) pred.name name)
          in
          let prefp_args, prefp_body =
            List.Assoc.find_exn ~equal:Stdlib.( = ) prefp_templ_preds name
          in
          List.map
            (Term.elim_min_max_list
            @@ Term.subst_funcs rank_sub ua_pred_delta.body)
            ~f:(fun body ->
              Formula.leq
                (T_real.mk_radd
                   (Term.rename
                      (LogicOld.ren_of_sort_env_list ua_pred_delta.args
                         rank_args)
                      body)
                   (Term.rename
                      (LogicOld.ren_of_sort_env_list prefp_args rank_args)
                      prefp_body))
                rank_body))
    in
    let accelerated_rank_constrs =
      match accel_problem with
      | Some accel_problem when config.enable_geometric_pla ->
          let active_names = QFL.Accel.active_pred_names accel_problem in
          let rank_template_env =
            QFL.Accel.template_env_of_prefp_templates templ_params
              rank_templ_preds
          in
          let prefp_template_env =
            QFL.Accel.template_env_of_prefp_templates templ_params
              prefp_templ_preds
          in
          let constrs, report =
            QFL.Accel.constraints_of_accel_problem_rank
              ~active_pred_names:active_names ~fsub rank_template_env
              prefp_template_env accel_problem
          in
          Debug.print ~id:None
          @@ lazy
               (sprintf
                  "geometric PLA lower-bound ranking acceleration check\n%s\n"
                  report);
          if List.is_empty constrs then None else Some constrs
      | _ -> None
    in
    let ranking_constrs =
      match
        (accel_problem, config.enable_geometric_pla, accelerated_rank_constrs)
      with
      | Some _, true, Some constrs -> constrs
      | Some _, true, None when rank_delta_is_trivial -> [ Formula.mk_false () ]
      | _ -> original_rank_constrs
    in
    let prefixpoint_constrs =
      match accel_problem with
      | Some accel_problem when config.enable_geometric_pla ->
          let active_names = QFL.Accel.active_pred_names accel_problem in
          let accel_template_env =
            QFL.Accel.template_env_of_prefp_templates templ_params
              prefp_templ_preds
          in
          let accel_prefixpoint_constrs, accel_report =
            QFL.Accel.constraints_of_accel_problem
              ~active_pred_names:active_names ~fsub accel_template_env
              accel_problem
          in
          Debug.print ~id:None
          @@ lazy
               (sprintf
                  "geometric PLA lower-bound prefixpoint acceleration enabled\n\
                   accelerated prefixpoint constraint selection:\n\
                   %s\n"
                  accel_report);
          accel_prefixpoint_constrs
      | _ -> original_prefixpoint_constrs
    in
    let postfixpoint_constrs =
      match accel_problem with
      | Some accel_problem
        when config.enable_geometric_pla
             && ((not rank_delta_is_trivial)
                || Option.is_some accelerated_rank_constrs) ->
          let active_names = QFL.Accel.active_pred_names accel_problem in
          let accel_template_env =
            QFL.Accel.template_env_of_prefp_templates templ_params
              postfp_templ_preds
          in
          let accel_postfixpoint_constrs, accel_report =
            QFL.Accel.constraints_of_accel_problem_lower
              ~active_pred_names:active_names ~fsub accel_template_env
              accel_problem
          in
          Debug.print ~id:None
          @@ lazy
               (sprintf
                  "geometric PLA lower-bound acceleration enabled\n\
                   accelerated postfixpoint constraint selection:\n\
                   %s\n"
                  accel_report);
          accel_postfixpoint_constrs
      | Some _ when config.enable_geometric_pla ->
          Debug.print ~id:None
          @@ lazy
               "geometric PLA lower-bound acceleration not used for \
                postfixpoint constraints\n\
                reason: ranking delta is trivial; non-trivial accelerated \
                ranking constraint is not generated\n\
                fallback: reject unsupported accelerated lower-bound path";
          [ Formula.mk_false () ]
      | _ ->
          Debug.print ~id:None
          @@ lazy
               "geometric PLA lower-bound acceleration not used for \
                postfixpoint constraints";
          original_postfixpoint_constrs
    in
    let template_nonnegative_constrs templ_preds =
      List.concat_map templ_preds ~f:(fun (name, (_, quant_pred)) ->
          let pred =
            List.find_exn qfl_preds_for_templates ~f:(fun pred ->
                Stdlib.( = ) pred.name name)
          in
          QFL.Accel.template_nonnegative_formulas quant_pred
          |> List.concat_map ~f:(QFL.Problem.imply_antecedents pred.arg_constrs))
    in
    let constrs =
      List.concat templ_constrss
      @ (if config.quant_postfp_force_non_const then
           [
             Formula.or_of
               (List.map !coeffs ~f:(fun c -> Formula.neq c (T_real.rzero ())));
           ]
         else [])
      @ template_nonnegative_constrs
          (prefp_templ_preds @ rank_templ_preds @ postfp_templ_preds)
      @ unfolded_nonnegative_constrs
      @ List.map postfp_templ_preds
          ~f:(fun (name, (postfp_args, postfp_body)) ->
            let prefp_args, prefp_body =
              List.Assoc.find_exn ~equal:Stdlib.( = ) prefp_templ_preds name
            in
            Formula.leq postfp_body
              (Term.rename
                 (LogicOld.ren_of_sort_env_list prefp_args postfp_args)
                 prefp_body))
      @ List.map ~f:(Formula.subst_funcs postfp_sub) query_fml
      @ postfixpoint_constrs @ prefixpoint_constrs @ ranking_constrs
    in
    let main, backup =
      match config.enable_pareto_caching with
      | Some thr when List.length pareto_cache >= thr ->
          let pc_constrs, pc_templ_params =
            gen_cache_constr
              (Second
                 ( prefp_templ_preds,
                   rank_templ_preds,
                   postfp_templ_preds,
                   ua_preds_delta ))
              ua_preds fsub pareto_cache
          in
          let pc_constrs =
            List.concat templ_constrss
            @ List.concat_map (prefp_templ_preds @ rank_templ_preds)
                ~f:(fun (name, (_, quant_pred)) ->
                  if String.(Ident.name_of_tvar name <> "Inv") then
                    let pred =
                      List.find_exn qfl_preds_for_templates ~f:(fun pred ->
                          Stdlib.( = ) pred.name name)
                    in
                    QFL.Accel.template_nonnegative_formulas quant_pred
                    |> List.concat_map
                         ~f:(QFL.Problem.imply_antecedents pred.arg_constrs)
                  else [])
            @ template_nonnegative_constrs postfp_templ_preds
            @ unfolded_nonnegative_constrs
            @ List.map ~f:(Formula.subst_funcs postfp_sub) query_fml
            @ pc_constrs
          in
          ( ( ( Some ua_preds,
                prefp_templ_preds,
                rank_templ_preds,
                postfp_templ_preds ),
              PCSP.Problem.make ~prefix:(Some "q") pc_constrs
              @@ SMT.Problem.
                   {
                     decl_reading = SMT.Problem.Synthesize;
                     candidates = Map.Poly.empty;
                     uni_sort = Set.Poly.empty;
                     uni_senv = Map.Poly.empty;
                     exi_senv = Map.force_merge templ_params pc_templ_params;
                     dep_map = Map.Poly.empty;
                     kind_map = Map.Poly.empty (*ToDo*);
                     fenv = Map.Poly.empty;
                     dtenv = Map.Poly.empty;
                   } ),
            Some
              ( ( Some ua_preds,
                  prefp_templ_preds,
                  rank_templ_preds,
                  postfp_templ_preds ),
                PCSP.Problem.make ~prefix:(Some "q") constrs
                @@ SMT.Problem.
                     {
                       decl_reading = SMT.Problem.Synthesize;
                       candidates = Map.Poly.empty;
                       uni_sort = Set.Poly.empty;
                       uni_senv = Map.Poly.empty;
                       exi_senv = templ_params;
                       dep_map = Map.Poly.empty;
                       kind_map = Map.Poly.empty (*ToDo*);
                       fenv = Map.Poly.empty;
                       dtenv = Map.Poly.empty;
                     } ) )
      | _ ->
          ( ( ( Some ua_preds,
                prefp_templ_preds,
                rank_templ_preds,
                postfp_templ_preds ),
              PCSP.Problem.make ~prefix:(Some "q") constrs
              @@ SMT.Problem.
                   {
                     decl_reading = SMT.Problem.Synthesize;
                     candidates = Map.Poly.empty;
                     uni_sort = Set.Poly.empty;
                     uni_senv = Map.Poly.empty;
                     exi_senv = templ_params;
                     dep_map = Map.Poly.empty;
                     kind_map = Map.Poly.empty (*ToDo*);
                     fenv = Map.Poly.empty;
                     dtenv = Map.Poly.empty;
                   } ),
            None )
    in
    (main, backup)

  let cgen_pqes_ub (qfl : QFL.Problem.t) accel_problem query_fml fsub
      pareto_cache =
    let query_fml = Formula.elim_min_max_list query_fml in
    let qfl_preds_for_templates =
      if config.enable_geometric_pla then
        let active_names = QFL.Accel.active_pred_names accel_problem in
        List.filter qfl.preds ~f:(fun pred -> Set.mem active_names pred.name)
      else qfl.preds
    in
    let prefp_templ_paramss, prefp_templ_preds =
      List.unzip
      @@ List.map qfl_preds_for_templates ~f:(fun pred ->
          let template =
            Templ.gen_quant_template
              ~num_conds:config.quant_prefp_templ_num_conds
              ~use_orig_ite:config.quant_prefp_templ_use_orig_ite
              ~cond_degree:config.quant_prefp_templ_cond_degree
              ~term_degree:config.quant_prefp_templ_term_degree pred.args
              pred.body pred.annots
          in
          (template.templ_params, (pred.name, (pred.args, template.quant_pred))))
    in
    if not @@ List.is_empty prefp_templ_preds then
      Debug.print @@ lazy "[6. Template]";
    if not @@ List.is_empty prefp_templ_preds then (
      Debug.print @@ lazy "templates for prefixpoint:";
      print_templ prefp_templ_preds);
    let prefp_sub = Map.Poly.of_alist_exn prefp_templ_preds in
    let templ_params = Map.force_merge_list prefp_templ_paramss in
    let unfolded_nonnegative_constrs =
      QFL.Problem.nonnegative_formulas_of_fsub_with_preds
        accel_problem.original_problem.preds fsub prefp_sub
    in
    let active_pred_names =
      Set.Poly.of_list
      @@ List.map qfl_preds_for_templates ~f:(fun pred -> pred.name)
    in
    let pla_body_nonnegative_constrs =
      if config.enable_geometric_pla then
        QFL.Accel.body_nonnegative_formulas ~active_pred_names ~fsub
          accel_problem
      else []
    in
    let original_prefixpoint_constrs =
      List.map ~f:(Formula.subst_funcs prefp_sub)
      @@ List.concat_map qfl_preds_for_templates ~f:(fun pred ->
          List.map (Term.elim_min_max_list pred.body) ~f:(fun body ->
              Formula.geq
                (Term.fvar_app_of_senv pred.name pred.args T_real.SReal)
                body))
    in
    let prefixpoint_constrs =
      if config.enable_geometric_pla then (
        let accel_template_env =
          QFL.Accel.template_env_of_prefp_templates templ_params
            prefp_templ_preds
        in
        let accel_prefixpoint_constrs, accel_report =
          QFL.Accel.constraints_of_accel_problem ~active_pred_names ~fsub
            accel_template_env accel_problem
        in
        Debug.print ~id:None
        @@ lazy
             (sprintf
                "geometric PLA acceleration enabled\n\
                 accelerated prefixpoint constraint selection:\n\
                 %s\n"
                accel_report);
        accel_prefixpoint_constrs)
      else (
        Debug.print ~id:None
        @@ lazy
             (sprintf
                "geometric PLA acceleration disabled\n\
                 accelerated constraints are not generated\n\
                 %s\n"
             @@ QFL.Accel.str_of_disabled_report accel_problem);
        original_prefixpoint_constrs)
    in
    let constrs =
      List.concat_map qfl_preds_for_templates ~f:(fun pred ->
          let _, quant_pred = Map.Poly.find_exn prefp_sub pred.name in
          QFL.Accel.template_nonnegative_formulas quant_pred
          |> List.concat_map ~f:(QFL.Problem.imply_antecedents pred.arg_constrs))
      @ unfolded_nonnegative_constrs @ pla_body_nonnegative_constrs
      @ List.map ~f:(Formula.subst_funcs prefp_sub) query_fml
      @ prefixpoint_constrs
    in
    let main, backup =
      match config.enable_pareto_caching with
      | Some thr when List.length pareto_cache >= thr ->
          let pc_constrs, pc_templ_params =
            gen_cache_constr (First prefp_sub) qfl.preds fsub pareto_cache
          in
          let pc_constrs =
            List.concat_map qfl_preds_for_templates ~f:(fun pred ->
                let _, quant_pred = Map.Poly.find_exn prefp_sub pred.name in
                QFL.Accel.template_nonnegative_formulas quant_pred
                |> List.concat_map
                     ~f:(QFL.Problem.imply_antecedents pred.arg_constrs))
            @ unfolded_nonnegative_constrs @ pla_body_nonnegative_constrs
            @ List.map ~f:(Formula.subst_funcs prefp_sub) query_fml
            @ pc_constrs
          in
          ( ( (None, prefp_templ_preds, [], []),
              PCSP.Problem.make pc_constrs
              @@ SMT.Problem.
                   {
                     decl_reading = SMT.Problem.Synthesize;
                     candidates = Map.Poly.empty;
                     uni_sort = Set.Poly.empty;
                     uni_senv = Map.Poly.empty;
                     exi_senv = Map.force_merge templ_params pc_templ_params;
                     dep_map = Map.Poly.empty;
                     kind_map = Map.Poly.empty (*ToDo*);
                     fenv = Map.Poly.empty;
                     dtenv = Map.Poly.empty;
                   } ),
            Some
              ( (None, prefp_templ_preds, [], []),
                PCSP.Problem.make constrs
                @@ SMT.Problem.
                     {
                       decl_reading = SMT.Problem.Synthesize;
                       candidates = Map.Poly.empty;
                       uni_sort = Set.Poly.empty;
                       uni_senv = Map.Poly.empty;
                       exi_senv = templ_params;
                       dep_map = Map.Poly.empty;
                       kind_map = Map.Poly.empty (*ToDo*);
                       fenv = Map.Poly.empty;
                       dtenv = Map.Poly.empty;
                     } ) )
      | _ ->
          ( ( (None, prefp_templ_preds, [], []),
              PCSP.Problem.make constrs
              @@ SMT.Problem.
                   {
                     decl_reading = SMT.Problem.Synthesize;
                     candidates = Map.Poly.empty;
                     uni_sort = Set.Poly.empty;
                     uni_senv = Map.Poly.empty;
                     exi_senv = templ_params;
                     dep_map = Map.Poly.empty;
                     kind_map = Map.Poly.empty (*ToDo*);
                     fenv = Map.Poly.empty;
                     dtenv = Map.Poly.empty;
                   } ),
            None )
    in
    (main, backup)

  let div_ceil n d = if n % d = 0 then n / d else (n / d) + 1

  let solve_constrs templ_params constrs =
    let pqes =
      PCSP.Problem.make ~prefix:(Some "q") constrs
      @@ SMT.Problem.
           {
             decl_reading = SMT.Problem.Synthesize;
             candidates = Map.Poly.empty;
             uni_sort = Set.Poly.empty;
             uni_senv = Map.Poly.empty;
             exi_senv = templ_params;
             dep_map = Map.Poly.empty;
             kind_map = Map.Poly.empty (*ToDo*);
             fenv = Map.Poly.empty;
             dtenv = Map.Poly.empty;
           }
    in
    Debug.print ~id:None
    @@ lazy (sprintf "******* Generated PQEs:\n%s" @@ PCSP.Problem.str_of pqes);
    let open Or_error.Monad_infix in
    pcsp_solver ~primal:true >>= fun (module PCSPSolver) ->
    PCSPSolver.solve pqes >>= function
    | PCSP.Problem.Sat model, _ ->
        Ok
          (Some
             (Map.Poly.mapi templ_params ~f:(fun ~key ~data:_ ->
                  match Map.Poly.find model key with
                  | Some t -> t
                  | None -> Logic.RealTerm.rzero () (*ToDo*))))
    | Unsat _, _ ->
        Debug.print @@ lazy "the templates used may not be expressive enough";
        Ok None
    | Unknown, _ ->
        Debug.print
        @@ lazy
             "the backend PQE solver failed or the templates used may not be \
              expressive enough";
        Ok None
    | OutSpace _, _ ->
        Debug.print @@ lazy "out of space" (* TODO *);
        Ok None
    | Timeout, _ ->
        Debug.print @@ lazy "timeout";
        Ok None

  let conv tsub param_senv constrs =
    if List.is_empty param_senv then Set.Poly.empty
    else
      let param_constrs' =
        Set.Poly.map (Set.Poly.of_list constrs)
          ~f:
            (Formula.subst
               (Map.Poly.filter_keys tsub
                  ~f:(List.Assoc.mem ~equal:Stdlib.( = ) param_senv >> not))
            >> Normalizer.normalize >> Evaluator.simplify)
      in
      Debug.print @@ lazy "begin qelim";
      let param_constrs' =
        Set.concat_map param_constrs' ~f:(fun phi ->
            Set.concat_map (Formula.conjuncts_of phi) ~f:(fun phi ->
                let senv, phi =
                  Formula.rm_quant
                  @@ Z3Smt.Z3interface.qelim ~id:None
                       ~fenv:(LogicOld.get_fenv ())
                  @@ Formula.forall
                       (Set.to_list
                       @@ Set.filter
                            (Formula.term_sort_env_of phi)
                            ~f:
                              (fst
                              >> List.Assoc.mem ~equal:Stdlib.( = ) param_senv
                              >> not))
                       phi
                in
                Set.Poly.map
                  (Formula.to_cnf ~process_pure:true phi)
                  ~f:(Formula.forall (Set.to_list senv))))
      in
      Debug.print @@ lazy "end qelim";
      assert (
        Set.for_all param_constrs' ~f:(fun phi ->
            Set.is_subset (Formula.fvs_of phi)
              ~of_:(Set.Poly.of_list @@ List.map ~f:fst param_senv)));
      Debug.print
      @@ lazy
           (sprintf "parameter constraints: %s |-> %s"
              (str_of_sort_env_list Term.str_of_sort param_senv)
              (Formula.str_of @@ Formula.and_of @@ Set.to_list param_constrs'));
      param_constrs'

  let simul_inv_syn = true

  let rec gen_inv_cnstr inv_sub conds = function
    | Term.FunApp (T_bool.IfThenElse, [ cond; t1; t2 ], _) ->
        Set.Poly.union_list
        @@ List.map
             (Formula.disjuncts_list_of @@ Evaluator.simplify
            @@ Formula.of_bool_term cond)
             ~f:(fun cond -> gen_inv_cnstr inv_sub (Set.add conds cond) t1)
        @ List.map
            (Formula.disjuncts_list_of @@ Evaluator.simplify
            @@ Formula.of_neg_bool_term cond)
            ~f:(fun cond -> gen_inv_cnstr inv_sub (Set.add conds cond) t2)
    | Term.FunApp (T_real.RAdd, [ t1; t2 ], _) ->
        Set.union
          (gen_inv_cnstr inv_sub conds t1)
          (gen_inv_cnstr inv_sub conds t2)
    | Term.FunApp (T_real.RMul, [ t1; t2 ], _) ->
        Set.union
          (gen_inv_cnstr inv_sub conds t1)
          (gen_inv_cnstr inv_sub conds t2)
    | Term.FunApp (FVar (Ident.Tvar ("min" | "max"), _, _), args, _) ->
        Set.Poly.union_list @@ List.map ~f:(gen_inv_cnstr inv_sub conds) args
    | Term.FunApp (FVar (fvar, _, _), args, _) -> (
        match Map.Poly.find inv_sub fvar with
        | Some (senv, phi) ->
            let sub =
              Map.Poly.of_alist_exn
              @@ List.map2_exn senv args ~f:(fun (x, _) t -> (x, t))
            in
            Set.Poly.map
              (Formula.to_cnf ~process_pure:true @@ Formula.subst sub phi)
              ~f:(fun conc -> (conds, conc))
        | None -> Set.Poly.empty (*ToDo*))
    | _ (*ToDo*) -> Set.Poly.empty

  let gen_inv_constrs init inv_sub invmap (preds : QFL.Pred.t list) =
    match init with
    | None -> []
    | Some (init_name, init_args) ->
        Set.to_list
        @@ Set.Poly.union_list
             ((let inv_args, inv_body = Map.find_exn inv_sub init_name in
               Formula.to_cnf ~process_pure:true
               @@ Formula.subst
                    (Map.Poly.of_alist_exn
                    @@ List.map2_exn inv_args init_args ~f:(fun (x, _) t ->
                        (x, t)))
                    inv_body)
             :: List.map preds ~f:(fun pred ->
                 let constrs =
                   let cond' =
                     let inv_args, inv_body = Map.find_exn inv_sub pred.name in
                     Formula.rename
                       (LogicOld.ren_of_sort_env_list inv_args pred.args)
                       inv_body
                   in
                   let cond' =
                     if true then cond'
                     else
                       match Map.Poly.find invmap pred.name with
                       | None -> cond'
                       | Some (inv_args, inv_body) ->
                           Formula.mk_and cond'
                             (Formula.rename
                                (LogicOld.ren_of_sort_env_list inv_args
                                   pred.args)
                                inv_body)
                   in
                   Set.concat_map (Formula.disjuncts_of cond') ~f:(fun cond' ->
                       Set.Poly.filter_map ~f:(fun (conds, conc) ->
                           let c =
                             Evaluator.simplify @@ Formula.and_of @@ Set.to_list
                             @@ Set.add conds cond'
                           in
                           if Formula.is_true c then Some conc
                           else if Formula.is_false c then None
                           else Some (Formula.mk_imply c conc))
                       @@ gen_inv_cnstr inv_sub Set.Poly.empty pred.body)
                 in
                 if false then
                   Set.iter constrs ~f:(fun c ->
                       Debug.print @@ lazy ("c: " ^ Formula.str_of c));
                 constrs))

  let gen_inv_templ init param_senv (preds : QFL.Pred.t list) =
    match init with
    | None -> ([], [])
    | Some _ ->
        let inv_templ_paramss, inv_templ_preds =
          List.unzip
          @@ List.map preds ~f:(fun pred ->
              let template =
                Templ.gen_dnf ~print:Debug.print ~eq_atom:false ~real_coeff:true
                  ~ignore_hole:true ~br_bools:false ~only_bools:false
                  {
                    consts = [];
                    terms = [];
                    quals = [];
                    shp = config.quant_omega_regular_inv_shape;
                    ubc = None;
                    ubd = None;
                    s = Set.Poly.empty;
                  }
                  { bec = None } (param_senv @ pred.args)
              in
              (template.templ_params, (pred.name, (pred.args, template.pred))))
        in
        if not @@ List.is_empty inv_templ_preds then (
          Debug.print @@ lazy "templates for invariants:";
          print_inv_templ inv_templ_preds);
        (inv_templ_paramss, inv_templ_preds)

  let gen_rank_templ param_senv (preds : QFL.Pred.t list) =
    let rank_templ_paramss, rank_templ_preds =
      List.unzip
      @@ List.map preds ~f:(fun pred ->
          let template =
            Templ.gen_quant_template
              ~num_conds:config.quant_rank_templ_num_conds
              ~use_orig_ite:config.quant_rank_templ_use_orig_ite
              ~cond_degree:config.quant_rank_templ_cond_degree
              ~term_degree:config.quant_rank_templ_term_degree
              (param_senv @ pred.args) pred.body pred.annots
          in
          (template.templ_params, (pred.name, (pred.args, template.quant_pred))))
    in
    if not @@ List.is_empty rank_templ_preds then (
      Debug.print @@ lazy "templates for ranking supermartingales:";
      print_templ rank_templ_preds);
    (rank_templ_paramss, rank_templ_preds)

  let gen_rank_constrs inv_sub invmap pred_eps_set rank_sub rank_templ_preds =
    List.concat_map rank_templ_preds ~f:(fun (name, (args, quant_pred)) ->
        List.map
          (match
             Map.Poly.find (if simul_inv_syn then inv_sub else invmap) name
           with
          | None -> [ Fn.id ]
          | Some (inv_args, inv) ->
              let inv =
                Formula.rename (LogicOld.ren_of_sort_env_list inv_args args) inv
              in
              List.map (Formula.disjuncts_list_of inv) ~f:Formula.mk_imply)
          ~f:(fun f -> f @@ Formula.geq quant_pred (T_real.rzero ())))
    @ List.concat_map (Set.to_list pred_eps_set)
        ~f:(fun ((pred : QFL.Pred.t), eps) ->
          let rank_args, rank_body = Map.find_exn rank_sub pred.name in
          List.map
            (match
               Map.Poly.find
                 (if simul_inv_syn then inv_sub else invmap)
                 pred.name
             with
            | None -> [ Fn.id ]
            | Some (inv_args, inv) ->
                let inv =
                  Formula.rename
                    (LogicOld.ren_of_sort_env_list inv_args pred.args)
                    inv
                in
                List.map (Formula.disjuncts_list_of inv) ~f:Formula.mk_imply)
            ~f:(fun f ->
              f
              @@ Formula.geq
                   (Term.rename
                      (LogicOld.ren_of_sort_env_list rank_args pred.args)
                      rank_body)
                   (T_real.mk_radd (Term.mk_var eps T_real.SReal)
                   @@ Term.subst_funcs rank_sub pred.body)))

  let synthesize_ssm (qfl : QFL.Problem.t)
      (init, invmap, param_senv, param_constrs) =
    let d_div_2 = div_ceil (QFL.Problem.depth_of qfl) 2 in
    let rec loop param_constrs lexmap j =
      if j <= d_div_2 then (
        let preds = Set.Poly.of_list qfl.preds in
        Debug.print ~id:None
        @@ lazy
             (sprintf "\n***synthesizing ranking supermartingales at level %d\n"
                j);
        let inv_templ_paramss, inv_templ_preds =
          gen_inv_templ init param_senv qfl.preds
        in
        let inv_sub = Map.Poly.of_alist_exn inv_templ_preds in
        let rank_templ_paramss, rank_templ_preds =
          gen_rank_templ param_senv qfl.preds
        in
        let rank_sub = Map.Poly.of_alist_exn rank_templ_preds in
        let eps_taken = taken_in_problem qfl param_senv in
        let pred_eps_set =
          Set.Poly.map preds ~f:(fun pred ->
              let eps =
                Ident.mk_fresh_tvar_avoiding ~prefix:"eps" ~taken:eps_taken ()
              in
              Debug.print
              @@ lazy
                   (sprintf "%s |-> %s"
                      (Ident.name_of_tvar pred.name)
                      (Ident.name_of_tvar eps));
              (pred, eps))
        in
        let constrs_inv = gen_inv_constrs init inv_sub invmap qfl.preds in
        let constrs_rank =
          (Set.to_list
          @@ Set.Poly.map pred_eps_set ~f:(fun (pred, eps) ->
              if QFL.Problem.level_of qfl pred.name = (2 * j) - 1 then
                Formula.eq (Term.mk_var eps T_real.SReal) (T_real.rone ())
              else if QFL.Problem.level_of qfl pred.name < (2 * j) - 1 then
                Formula.lt (Term.mk_var eps T_real.SReal) (T_real.rzero ())
              else Formula.eq (Term.mk_var eps T_real.SReal) (T_real.rzero ()))
          )
          @ gen_rank_constrs inv_sub invmap pred_eps_set rank_sub
              rank_templ_preds
        in
        let constrs = Set.to_list param_constrs @ constrs_inv @ constrs_rank in
        let templ_params =
          Map.force_merge_list
          @@ Map.Poly.of_alist_exn param_senv
             :: (Map.of_set_exn
                @@ Set.Poly.map pred_eps_set ~f:(fun (_, eps) ->
                    (eps, T_real.SReal)))
             :: rank_templ_paramss
          @ List.map ~f:Logic.to_old_sort_env_map inv_templ_paramss
        in
        match solve_constrs templ_params constrs with
        | Ok (Some model) ->
            let tsub =
              Logic.ExtTerm.to_old_subst Map.Poly.empty Map.Poly.empty model
            in
            let param_constrs' = conv tsub param_senv constrs in
            Debug.print @@ lazy "*************************************";
            List.iter inv_templ_preds ~f:(fun (name, (args, pred)) ->
                let inv = Evaluator.simplify @@ Formula.subst tsub pred in
                Debug.print
                @@ lazy
                     (sprintf "synthesized invariant for %s: %s |-> %s"
                        (Ident.name_of_tvar name)
                        (str_of_sort_env_list Term.str_of_sort args)
                        (Formula.str_of inv)));
            Debug.print @@ lazy "*************************************";
            let lexmap' =
              let ranks =
                List.map rank_templ_preds ~f:(fun (name, (args, quant_pred)) ->
                    ( name,
                      ( args,
                        Evaluator.simplify_term @@ Term.subst tsub quant_pred )
                    ))
              in
              List.fold ~init:lexmap qfl.preds ~f:(fun lexmap pred ->
                  let rank_args, rank_body =
                    List.Assoc.find_exn ~equal:Stdlib.( = ) ranks pred.name
                  in
                  let rank =
                    Term.rename
                      (LogicOld.ren_of_sort_env_list rank_args pred.args)
                      rank_body
                  in
                  Debug.print
                  @@ lazy
                       (sprintf
                          "synthesized ranking supermartingale for (%s, %d, \
                           %d): %s |-> %s"
                          (Ident.name_of_tvar pred.name)
                          j 0
                          (str_of_sort_env_list Term.str_of_sort pred.args)
                          (Term.str_of rank));
                  Map.Poly.add_exn lexmap ~key:(pred.name, j, 0) ~data:rank)
            in
            Debug.print @@ lazy "*************************************";
            loop param_constrs' lexmap' (j + 1)
        | Ok None -> None
        | Error err -> failwith (Error.to_string_hum err))
      else Some lexmap
    in
    loop param_constrs Map.Poly.empty 1

  let synthesize_gssm (qfl : QFL.Problem.t)
      (init, invmap, param_senv, param_constrs) =
    let d_div_2 = div_ceil (QFL.Problem.depth_of qfl) 2 in
    let rec loop param_constrs lexmap j =
      if j <= d_div_2 then (
        let preds =
          Set.filter (Set.Poly.of_list qfl.preds) ~f:(fun pred ->
              QFL.Problem.level_of qfl pred.name >= (2 * j) - 1)
        in
        Debug.print ~id:None
        @@ lazy
             (sprintf "\n***synthesizing ranking supermartingales at level %d\n"
                j);
        let inv_templ_paramss, inv_templ_preds =
          gen_inv_templ init param_senv qfl.preds
        in
        let inv_sub = Map.Poly.of_alist_exn inv_templ_preds in
        let rank_templ_paramss, rank_templ_preds =
          gen_rank_templ param_senv qfl.preds
        in
        let rank_sub = Map.Poly.of_alist_exn rank_templ_preds in
        let eps_taken = taken_in_problem qfl param_senv in
        let pred_eps_set =
          Set.Poly.map preds ~f:(fun pred ->
              let eps =
                Ident.mk_fresh_tvar_avoiding ~prefix:"eps" ~taken:eps_taken ()
              in
              Debug.print
              @@ lazy
                   (sprintf "%s |-> %s"
                      (Ident.name_of_tvar pred.name)
                      (Ident.name_of_tvar eps));
              (pred, eps))
        in
        let constrs_inv = gen_inv_constrs init inv_sub invmap qfl.preds in
        let constrs_rank =
          (Set.to_list
          @@ Set.Poly.map pred_eps_set ~f:(fun (pred, eps) ->
              if QFL.Problem.level_of qfl pred.name = (2 * j) - 1 then
                Formula.eq (Term.mk_var eps T_real.SReal) (T_real.rone ())
              else Formula.eq (Term.mk_var eps T_real.SReal) (T_real.rzero ()))
          )
          @ gen_rank_constrs inv_sub invmap pred_eps_set rank_sub
              rank_templ_preds
        in
        let constrs = Set.to_list param_constrs @ constrs_inv @ constrs_rank in
        let templ_params =
          Map.force_merge_list
          @@ Map.Poly.of_alist_exn param_senv
             :: (Map.of_set_exn
                @@ Set.Poly.map pred_eps_set ~f:(fun (_, eps) ->
                    (eps, T_real.SReal)))
             :: rank_templ_paramss
          @ List.map ~f:Logic.to_old_sort_env_map inv_templ_paramss
        in
        match solve_constrs templ_params constrs with
        | Ok (Some model) ->
            let tsub =
              Logic.ExtTerm.to_old_subst Map.Poly.empty Map.Poly.empty model
            in
            let param_constrs' = conv tsub param_senv constrs in
            Debug.print @@ lazy "*************************************";
            List.iter inv_templ_preds ~f:(fun (name, (args, pred)) ->
                let inv = Evaluator.simplify @@ Formula.subst tsub pred in
                Debug.print
                @@ lazy
                     (sprintf "synthesized invariant for %s: %s |-> %s"
                        (Ident.name_of_tvar name)
                        (str_of_sort_env_list Term.str_of_sort args)
                        (Formula.str_of inv)));
            Debug.print @@ lazy "*************************************";
            let lexmap' =
              let ranks =
                List.map rank_templ_preds ~f:(fun (name, (args, quant_pred)) ->
                    ( name,
                      ( args,
                        Evaluator.simplify_term @@ Term.subst tsub quant_pred )
                    ))
              in
              List.fold ~init:lexmap qfl.preds ~f:(fun lexmap pred ->
                  let rank_args, rank_body =
                    List.Assoc.find_exn ~equal:Stdlib.( = ) ranks pred.name
                  in
                  let rank =
                    Term.rename
                      (LogicOld.ren_of_sort_env_list rank_args pred.args)
                      rank_body
                  in
                  Debug.print
                  @@ lazy
                       (sprintf
                          "synthesized ranking supermartingale for (%s, %d, \
                           %d): %s |-> %s"
                          (Ident.name_of_tvar pred.name)
                          j 0
                          (str_of_sort_env_list Term.str_of_sort pred.args)
                          (Term.str_of rank));
                  Map.Poly.add_exn lexmap ~key:(pred.name, j, 0) ~data:rank)
            in
            Debug.print @@ lazy "*************************************";
            loop param_constrs' lexmap' (j + 1)
        | Ok None -> None
        | Error err -> failwith (Error.to_string_hum err))
      else Some lexmap
    in
    loop param_constrs Map.Poly.empty 1

  let synthesize_lexgssm (qfl : QFL.Problem.t)
      (init, invmap, param_senv, param_constrs) =
    let d_div_2 = div_ceil (QFL.Problem.depth_of qfl) 2 in
    let rec loop param_constrs lexmap j =
      if j <= d_div_2 then (
        let preds =
          Set.filter (Set.Poly.of_list qfl.preds) ~f:(fun pred ->
              QFL.Problem.level_of qfl pred.name >= (2 * j) - 1)
        in
        Debug.print ~id:None
        @@ lazy
             (sprintf "\n***synthesizing ranking supermartingales at level %d\n"
                j);
        let rec inner param_constrs lexmap (preds : QFL.Pred.t Set.Poly.t) k =
          let param_constrs', lexmap', elimed =
            let inv_templ_paramss, inv_templ_preds =
              gen_inv_templ init param_senv qfl.preds
            in
            let inv_sub = Map.Poly.of_alist_exn inv_templ_preds in
            let rank_templ_paramss, rank_templ_preds =
              gen_rank_templ param_senv qfl.preds
            in
            let rank_sub = Map.Poly.of_alist_exn rank_templ_preds in
            let eps_taken = taken_in_problem qfl param_senv in
            let pred_eps_set =
              Set.Poly.map preds ~f:(fun pred ->
                  let eps =
                    Ident.mk_fresh_tvar_avoiding ~prefix:"eps" ~taken:eps_taken ()
                  in
                  Debug.print
                  @@ lazy
                       (sprintf "%s |-> %s"
                          (Ident.name_of_tvar pred.name)
                          (Ident.name_of_tvar eps));
                  (pred, eps))
            in
            let constrs_inv = gen_inv_constrs init inv_sub invmap qfl.preds in
            let constrs_rank =
              Formula.geq
                (T_real.mk_rsum (T_real.rzero ())
                @@ Set.to_list
                @@ Set.Poly.map pred_eps_set ~f:(fun (_, eps) ->
                    Term.mk_var eps T_real.SReal))
                (T_real.rone ())
              :: (Set.to_list
                 @@ Set.concat_map pred_eps_set ~f:(fun (_, eps) ->
                     Set.Poly.of_list
                     @@ Formula.mk_range_real
                          (Term.mk_var eps T_real.SReal)
                          Q.zero Q.one))
              @ gen_rank_constrs inv_sub invmap pred_eps_set rank_sub
                  rank_templ_preds
            in
            let constrs =
              Set.to_list param_constrs @ constrs_inv @ constrs_rank
            in
            let templ_params =
              Map.force_merge_list
              @@ Map.Poly.of_alist_exn param_senv
                 :: (Map.of_set_exn
                    @@ Set.Poly.map pred_eps_set ~f:(fun (_, eps) ->
                        (eps, T_real.SReal)))
                 :: rank_templ_paramss
              @ List.map ~f:Logic.to_old_sort_env_map inv_templ_paramss
            in
            match solve_constrs templ_params constrs with
            | Ok (Some model) ->
                let tsub =
                  Logic.ExtTerm.to_old_subst Map.Poly.empty Map.Poly.empty model
                in
                let param_constrs' = conv tsub param_senv constrs in
                Debug.print @@ lazy "*************************************";
                List.iter inv_templ_preds ~f:(fun (name, (args, pred)) ->
                    let inv = Evaluator.simplify @@ Formula.subst tsub pred in
                    Debug.print
                    @@ lazy
                         (sprintf "synthesized invariant for %s: %s |-> %s"
                            (Ident.name_of_tvar name)
                            (str_of_sort_env_list Term.str_of_sort args)
                            (Formula.str_of inv)));
                Debug.print @@ lazy "*************************************";
                let lexmap', elimed =
                  let ranks =
                    List.map rank_templ_preds
                      ~f:(fun (name, (args, quant_pred)) ->
                        ( name,
                          ( args,
                            Evaluator.simplify_term
                            @@ Term.subst tsub quant_pred ) ))
                  in
                  List.fold ~init:(lexmap, Set.Poly.empty) qfl.preds
                    ~f:(fun (lexmap, elimed) pred ->
                      let rank, elimed =
                        let rank_args, rank_body =
                          List.Assoc.find_exn ~equal:Stdlib.( = ) ranks
                            pred.name
                        in
                        let rank =
                          Term.rename
                            (LogicOld.ren_of_sort_env_list rank_args pred.args)
                            rank_body
                        in
                        match
                          Set.find pred_eps_set ~f:(fun (p, _) ->
                              Stdlib.( = ) p pred)
                        with
                        | None -> (rank, elimed)
                        | Some (_, eps) ->
                            let eps =
                              T_real.let_real
                              @@ Term.subst tsub (Term.mk_var eps T_real.SReal)
                            in
                            if Q.gt eps Q.zero then
                              let rank =
                                Evaluator.simplify_term
                                @@ Normalizer.normalize_term
                                @@ T_real.mk_rmul
                                     (T_real.mk_real Q.(one / eps))
                                     rank
                              in
                              (rank, Set.add elimed pred.name)
                            else (rank, elimed)
                      in
                      Debug.print
                      @@ lazy
                           (sprintf
                              "synthesized ranking supermartingale for (%s, \
                               %d, %d): %s |-> %s"
                              (Ident.name_of_tvar pred.name)
                              j k
                              (str_of_sort_env_list Term.str_of_sort pred.args)
                              (Term.str_of rank));
                      ( Map.Poly.add_exn lexmap ~key:(pred.name, j, k) ~data:rank,
                        elimed ))
                in
                Debug.print @@ lazy "*************************************";
                (param_constrs', lexmap', elimed)
            | Ok None ->
                ( param_constrs,
                  List.fold ~init:lexmap qfl.preds ~f:(fun lexmap pred ->
                      let rank = T_real.rzero () in
                      Debug.print
                      @@ lazy
                           (sprintf
                              "synthesized ranking supermartingale for (%s, \
                               %d, %d): %s |-> %s"
                              (Ident.name_of_tvar pred.name)
                              j k
                              (str_of_sort_env_list Term.str_of_sort pred.args)
                              (Term.str_of rank));
                      Map.Poly.add_exn lexmap ~key:(pred.name, j, k) ~data:rank),
                  Set.Poly.empty )
            | Error err -> failwith (Error.to_string_hum err)
          in
          if Set.is_empty elimed then (param_constrs', lexmap', preds)
          else
            let preds' =
              Set.filter preds ~f:(fun pred -> not @@ Set.mem elimed pred.name)
            in
            inner param_constrs' lexmap' preds' (k + 1)
        in
        let param_constrs, lexmap, preds = inner param_constrs lexmap preds 0 in
        if
          Set.exists preds ~f:(fun pred ->
              QFL.Problem.level_of qfl pred.name = (2 * j) - 1)
        then None
        else loop param_constrs lexmap (j + 1))
      else Some lexmap
    in
    loop param_constrs Map.Poly.empty 1

  let synthesize_pmsm (qfl : QFL.Problem.t)
      (init, invmap, param_senv, param_constrs) =
    let d_div_2 = div_ceil (QFL.Problem.depth_of qfl) 2 in
    let rec loop param_constrs lexmap (preds : QFL.Pred.t Set.Poly.t) j =
      if j <= d_div_2 then (
        let preds =
          Set.filter preds ~f:(fun pred ->
              QFL.Problem.level_of qfl pred.name >= (2 * j) - 1)
        in
        Debug.print ~id:None
        @@ lazy
             (sprintf "\n***synthesizing ranking supermartingales at level %d\n"
                j);
        let inv_templ_paramss, inv_templ_preds =
          gen_inv_templ init param_senv qfl.preds
        in
        let inv_sub = Map.Poly.of_alist_exn inv_templ_preds in
        let rank_templ_paramss, rank_templ_preds =
          gen_rank_templ param_senv qfl.preds
        in
        let rank_sub = Map.Poly.of_alist_exn rank_templ_preds in
        let eps_taken = taken_in_problem qfl param_senv in
        let pred_eps_set =
          Set.Poly.map preds ~f:(fun pred ->
              let eps =
                Ident.mk_fresh_tvar_avoiding ~prefix:"eps" ~taken:eps_taken ()
              in
              Debug.print
              @@ lazy
                   (sprintf "%s |-> %s"
                      (Ident.name_of_tvar pred.name)
                      (Ident.name_of_tvar eps));
              (pred, eps))
        in
        let constrs_inv = gen_inv_constrs init inv_sub invmap qfl.preds in
        let constrs_rank =
          (Set.to_list
          @@ Set.concat_map pred_eps_set ~f:(fun (pred, eps) ->
              if QFL.Problem.level_of qfl pred.name = (2 * j) - 1 then
                Set.Poly.singleton
                @@ Formula.eq (Term.mk_var eps T_real.SReal) (T_real.rone ())
              else
                Set.Poly.of_list
                @@ Formula.mk_range_real
                     (Term.mk_var eps T_real.SReal)
                     Q.zero Q.one))
          @ gen_rank_constrs inv_sub invmap pred_eps_set rank_sub
              rank_templ_preds
        in
        let constrs = Set.to_list param_constrs @ constrs_inv @ constrs_rank in
        let templ_params =
          Map.force_merge_list
          @@ Map.Poly.of_alist_exn param_senv
             :: (Map.of_set_exn
                @@ Set.Poly.map pred_eps_set ~f:(fun (_, eps) ->
                    (eps, T_real.SReal)))
             :: rank_templ_paramss
          @ List.map ~f:Logic.to_old_sort_env_map inv_templ_paramss
        in
        match solve_constrs templ_params constrs with
        | Ok (Some model) ->
            let tsub =
              Logic.ExtTerm.to_old_subst Map.Poly.empty Map.Poly.empty model
            in
            let param_constrs' = conv tsub param_senv constrs in
            Debug.print @@ lazy "*************************************";
            List.iter inv_templ_preds ~f:(fun (name, (args, pred)) ->
                let inv = Evaluator.simplify @@ Formula.subst tsub pred in
                Debug.print
                @@ lazy
                     (sprintf "synthesized invariant for %s: %s |-> %s"
                        (Ident.name_of_tvar name)
                        (str_of_sort_env_list Term.str_of_sort args)
                        (Formula.str_of inv)));
            Debug.print @@ lazy "*************************************";
            let lexmap', elimed =
              let ranks =
                List.map rank_templ_preds ~f:(fun (name, (args, quant_pred)) ->
                    ( name,
                      ( args,
                        Evaluator.simplify_term @@ Term.subst tsub quant_pred )
                    ))
              in
              List.fold ~init:(lexmap, Set.Poly.empty) qfl.preds
                ~f:(fun (lexmap, elimed) pred ->
                  let rank, elimed =
                    let rank_args, rank_body =
                      List.Assoc.find_exn ~equal:Stdlib.( = ) ranks pred.name
                    in
                    let rank =
                      Term.rename
                        (LogicOld.ren_of_sort_env_list rank_args pred.args)
                        rank_body
                    in
                    match
                      Set.find pred_eps_set ~f:(fun (p, _) ->
                          Stdlib.( = ) p pred)
                    with
                    | None -> (rank, elimed)
                    | Some (_, eps) ->
                        let eps =
                          T_real.let_real
                          @@ Term.subst tsub (Term.mk_var eps T_real.SReal)
                        in
                        if Q.gt eps Q.zero then
                          let rank =
                            Evaluator.simplify_term @@ Normalizer.normalize_term
                            @@ T_real.mk_rmul
                                 (T_real.mk_real Q.(one / eps))
                                 rank
                          in
                          (rank, Set.add elimed pred.name)
                        else (rank, elimed)
                  in
                  Debug.print
                  @@ lazy
                       (sprintf
                          "synthesized ranking supermartingale for (%s, %d, \
                           %d): %s |-> %s"
                          (Ident.name_of_tvar pred.name)
                          j 0
                          (str_of_sort_env_list Term.str_of_sort pred.args)
                          (Term.str_of rank));
                  ( Map.Poly.add_exn lexmap ~key:(pred.name, j, 0) ~data:rank,
                    elimed ))
            in
            Debug.print @@ lazy "*************************************";
            let preds' =
              Set.filter preds ~f:(fun pred -> not @@ Set.mem elimed pred.name)
            in
            loop param_constrs' lexmap' preds' (j + 1)
        | Ok None -> None
        | Error err -> failwith (Error.to_string_hum err))
      else Some lexmap
    in
    loop param_constrs Map.Poly.empty (Set.Poly.of_list qfl.preds) 1

  let synthesize_lexpmsm (qfl : QFL.Problem.t)
      (init, invmap, param_senv, param_constrs) =
    let d_div_2 = div_ceil (QFL.Problem.depth_of qfl) 2 in
    let rec loop param_constrs lexmap (preds : QFL.Pred.t Set.Poly.t) j =
      if j <= d_div_2 then (
        let preds =
          Set.filter preds ~f:(fun pred ->
              QFL.Problem.level_of qfl pred.name >= (2 * j) - 1)
        in
        Debug.print ~id:None
        @@ lazy
             (sprintf "\n***synthesizing ranking supermartingales at level %d\n"
                j);
        let rec inner param_constrs lexmap (preds : QFL.Pred.t Set.Poly.t) k =
          let param_constrs', lexmap', elimed =
            let inv_templ_paramss, inv_templ_preds =
              gen_inv_templ init param_senv qfl.preds
            in
            let inv_sub = Map.Poly.of_alist_exn inv_templ_preds in
            let rank_templ_paramss, rank_templ_preds =
              gen_rank_templ param_senv qfl.preds
            in
            let rank_sub = Map.Poly.of_alist_exn rank_templ_preds in
            let eps_taken = taken_in_problem qfl param_senv in
            let pred_eps_set =
              Set.Poly.map preds ~f:(fun pred ->
                  let eps =
                    Ident.mk_fresh_tvar_avoiding ~prefix:"eps" ~taken:eps_taken ()
                  in
                  Debug.print
                  @@ lazy
                       (sprintf "%s |-> %s"
                          (Ident.name_of_tvar pred.name)
                          (Ident.name_of_tvar eps));
                  (pred, eps))
            in
            let constrs_inv = gen_inv_constrs init inv_sub invmap qfl.preds in
            let constrs_rank =
              Formula.geq
                (T_real.mk_rsum (T_real.rzero ())
                @@ Set.to_list
                @@ Set.Poly.map pred_eps_set ~f:(fun (_, eps) ->
                    Term.mk_var eps T_real.SReal))
                (T_real.rone ())
              :: (Set.to_list
                 @@ Set.concat_map pred_eps_set ~f:(fun (_, eps) ->
                     Set.Poly.of_list
                     @@ Formula.mk_range_real
                          (Term.mk_var eps T_real.SReal)
                          Q.zero Q.one))
              @ gen_rank_constrs inv_sub invmap pred_eps_set rank_sub
                  rank_templ_preds
            in
            let constrs =
              Set.to_list param_constrs @ constrs_inv @ constrs_rank
            in
            let templ_params =
              Map.force_merge_list
              @@ Map.Poly.of_alist_exn param_senv
                 :: (Map.of_set_exn
                    @@ Set.Poly.map pred_eps_set ~f:(fun (_, eps) ->
                        (eps, T_real.SReal)))
                 :: rank_templ_paramss
              @ List.map ~f:Logic.to_old_sort_env_map inv_templ_paramss
            in
            match solve_constrs templ_params constrs with
            | Ok (Some model) ->
                let tsub =
                  Logic.ExtTerm.to_old_subst Map.Poly.empty Map.Poly.empty model
                in
                let param_constrs' = conv tsub param_senv constrs in
                Debug.print @@ lazy "*************************************";
                List.iter inv_templ_preds ~f:(fun (name, (args, pred)) ->
                    let inv = Evaluator.simplify @@ Formula.subst tsub pred in
                    Debug.print
                    @@ lazy
                         (sprintf "synthesized invariant for %s: %s |-> %s"
                            (Ident.name_of_tvar name)
                            (str_of_sort_env_list Term.str_of_sort args)
                            (Formula.str_of inv)));
                Debug.print @@ lazy "*************************************";
                let lexmap', elimed =
                  let ranks =
                    List.map rank_templ_preds
                      ~f:(fun (name, (args, quant_pred)) ->
                        ( name,
                          ( args,
                            Evaluator.simplify_term
                            @@ Term.subst tsub quant_pred ) ))
                  in
                  List.fold ~init:(lexmap, Set.Poly.empty) qfl.preds
                    ~f:(fun (lexmap, elimed) pred ->
                      let rank, elimed =
                        let rank_args, rank_body =
                          List.Assoc.find_exn ~equal:Stdlib.( = ) ranks
                            pred.name
                        in
                        let rank =
                          Term.rename
                            (LogicOld.ren_of_sort_env_list rank_args pred.args)
                            rank_body
                        in
                        match
                          Set.find pred_eps_set ~f:(fun (p, _) ->
                              Stdlib.( = ) p pred)
                        with
                        | None -> (rank, elimed)
                        | Some (_, eps) ->
                            let eps =
                              T_real.let_real
                              @@ Term.subst tsub (Term.mk_var eps T_real.SReal)
                            in
                            if Q.gt eps Q.zero then
                              let rank =
                                Evaluator.simplify_term
                                @@ Normalizer.normalize_term
                                @@ T_real.mk_rmul
                                     (T_real.mk_real Q.(one / eps))
                                     rank
                              in
                              (rank, Set.add elimed pred.name)
                            else (rank, elimed)
                      in
                      Debug.print
                      @@ lazy
                           (sprintf
                              "synthesized ranking supermartingale for (%s, \
                               %d, %d): %s |-> %s"
                              (Ident.name_of_tvar pred.name)
                              j k
                              (str_of_sort_env_list Term.str_of_sort pred.args)
                              (Term.str_of rank));
                      ( Map.Poly.add_exn lexmap ~key:(pred.name, j, k) ~data:rank,
                        elimed ))
                in
                Debug.print @@ lazy "*************************************";
                (param_constrs', lexmap', elimed)
            | Ok None ->
                ( param_constrs,
                  List.fold ~init:lexmap qfl.preds ~f:(fun lexmap pred ->
                      let rank = T_real.rzero () in
                      Debug.print
                      @@ lazy
                           (sprintf
                              "synthesized ranking supermartingale for (%s, \
                               %d, %d): %s |-> %s"
                              (Ident.name_of_tvar pred.name)
                              j k
                              (str_of_sort_env_list Term.str_of_sort pred.args)
                              (Term.str_of rank));
                      Map.Poly.add_exn lexmap ~key:(pred.name, j, k) ~data:rank),
                  Set.Poly.empty )
            | Error err -> failwith (Error.to_string_hum err)
          in
          if Set.is_empty elimed then (param_constrs', lexmap', preds)
          else
            let preds' =
              Set.filter preds ~f:(fun pred -> not @@ Set.mem elimed pred.name)
            in
            inner param_constrs' lexmap' preds' (k + 1)
        in
        let param_constrs, lexmap, preds = inner param_constrs lexmap preds 0 in
        if
          Set.exists preds ~f:(fun pred ->
              QFL.Problem.level_of qfl pred.name = (2 * j) - 1)
        then None
        else loop param_constrs lexmap preds (j + 1))
      else Some lexmap
    in
    loop param_constrs Map.Poly.empty (Set.Poly.of_list qfl.preds) 1

  let synthesize_invs (qfl : QFL.Problem.t) (init, param_senv, param_constrs) =
    match init with
    | None -> (init, Map.Poly.empty, param_senv, param_constrs)
    | Some _ ->
        let inv_templ_paramss, inv_templ_preds =
          gen_inv_templ init param_senv qfl.preds
        in
        let inv_sub = Map.Poly.of_alist_exn inv_templ_preds in
        let r_taken = taken_in_problem qfl param_senv in
        let rec loop cnt invmap freshness_constrs param_constrs =
          let constrs_inv = gen_inv_constrs init inv_sub invmap qfl.preds in
          let constrs =
            Set.to_list param_constrs
            @ Set.to_list freshness_constrs
            @ constrs_inv
          in
          let templ_params =
            Map.force_merge_list
            @@ Map.Poly.of_alist_exn param_senv
               :: List.map ~f:Logic.to_old_sort_env_map inv_templ_paramss
          in
          match solve_constrs templ_params constrs with
          | Ok (Some model) ->
              let tsub =
                Logic.ExtTerm.to_old_subst Map.Poly.empty Map.Poly.empty model
              in
              if false then print_endline @@ TermSubst.str_of tsub;
              let rat =
                List.map inv_templ_paramss ~f:(fun m ->
                    ( m,
                      Term.mk_var
                        (Ident.mk_fresh_tvar_avoiding ~prefix:"r_"
                           ~taken:(fun v ->
                             r_taken v || Map.Poly.mem model v
                             || List.exists inv_templ_paramss ~f:(fun m ->
                                 Map.Poly.mem m v))
                           ())
                        T_real.SReal ))
              in
              let freshness_constrs' =
                Set.add freshness_constrs
                  (Formula.mk_imply
                     (Formula.and_of
                        (Map.Poly.fold model
                           ~init:
                             (List.map rat ~f:(fun (_, r) ->
                                  Formula.mk_atom
                                  @@ T_real.mk_rgt r (T_real.rzero ())))
                           ~f:(fun ~key ~data eqs ->
                             if
                               List.Assoc.mem ~equal:Stdlib.( = ) param_senv key
                             then eqs
                             else
                               let _, r =
                                 List.find_exn rat ~f:(fun (m, _) ->
                                     Map.Poly.mem m key)
                               in
                               Formula.eq
                                 (Term.mk_var key T_real.SReal)
                                 (T_real.mk_rmul
                                    (Logic.ExtTerm.to_old_trm Map.Poly.empty
                                       Map.Poly.empty data)
                                    r)
                               :: eqs)))
                     (Formula.mk_false ()))
              in
              let param_constrs' = conv tsub param_senv constrs in
              Debug.print @@ lazy "*************************************";
              let invmap' =
                List.fold ~init:invmap inv_templ_preds
                  ~f:(fun invmap (name, (args, pred)) ->
                    let inv = Evaluator.simplify @@ Formula.subst tsub pred in
                    match Map.Poly.find invmap name with
                    | None ->
                        Debug.print
                        @@ lazy
                             (sprintf "synthesized invariant for %s: %s |-> %s"
                                (Ident.name_of_tvar name)
                                (str_of_sort_env_list Term.str_of_sort args)
                                (Formula.str_of inv));
                        if Formula.is_true inv then invmap
                        else Map.Poly.add_exn invmap ~key:name ~data:(args, inv)
                    | Some (args', inv') ->
                        let inv'' =
                          Evaluator.simplify
                          @@ Formula.and_of
                               [
                                 inv';
                                 Formula.rename
                                   (LogicOld.ren_of_sort_env_list args args')
                                   inv;
                               ]
                        in
                        Debug.print
                        @@ lazy
                             (sprintf "synthesized invariant for %s: %s |-> %s"
                                (Ident.name_of_tvar name)
                                (str_of_sort_env_list Term.str_of_sort args)
                                (Formula.str_of inv''));
                        Map.Poly.set invmap ~key:name ~data:(args', inv''))
              in
              Debug.print @@ lazy "*************************************";
              if cnt <= 4 (*ToDo*) then
                loop (cnt + 1) invmap' freshness_constrs' param_constrs'
              else (init, invmap', param_senv, param_constrs')
          | Ok None -> (init, invmap, param_senv, param_constrs)
          | Error err -> failwith (Error.to_string_hum err)
        in
        let freshness_constrs =
          Set.Poly.singleton
          @@ Formula.mk_imply
               (Formula.and_of
                  (Set.to_list
                  @@ Set.Poly.map
                       (Set.Poly.union_list
                       @@ List.map ~f:Map.Poly.key_set inv_templ_paramss)
                       ~f:(fun x ->
                         Formula.eq
                           (Term.mk_var x T_real.SReal)
                           (T_real.rzero ()))))
               (Formula.mk_false ())
        in
        loop 0 Map.Poly.empty freshness_constrs param_constrs

  let synthesize_omega_regular_supermartingale qfl
      (init, param_senv, param_constrs) =
    (match config.quant_omega_regular_supermartingale with
      | SSM -> synthesize_ssm qfl
      | GSSM -> synthesize_gssm qfl
      | LexGSSM -> synthesize_lexgssm qfl
      | PMSM -> synthesize_pmsm qfl
      | LexPMSM -> synthesize_lexpmsm qfl)
    @@
    if simul_inv_syn then (init, Map.Poly.empty, param_senv, param_constrs)
    else synthesize_invs qfl (None, param_senv, param_constrs)

  let check_almost_sure_satisfaction_of_omega_regular_properties
      ?(print_sol = false) (qfl : QFL.Problem.t)
      (init, param_senv, param_constrs) =
    match
      synthesize_omega_regular_supermartingale qfl
        (init, param_senv, param_constrs)
    with
    | None ->
        if print_sol then print_endline @@ sprintf "unknown";
        Or_error.return ([], [])
    | Some _ ->
        if print_sol then print_endline @@ sprintf "sat";
        Or_error.return ([], [])

  (* A query the backend could not settle used to be returned as
     [Or_error.error_string], which [main.ml]'s [ok_exn] printed as an OCaml
     backtrace -- the most common ending of this path, 69 of 246 QFL files and
     18 of 48 SGCL files.  "The backend did not settle this bound" is an
     ordinary answer, not a failure of the tool, so it is reported as one and
     the file's remaining queries are still run: the query that failed may have
     failed for a reason belonging to the backend rather than to the problem,
     and losing the whole file to that is out of proportion.

     Two things the reader has to be told, because neither is visible in a
     verdict on its own.  A query that runs after one with no answer looks at a
     pareto cache with a hole in it, so whatever bound it proves is weaker than
     the one it would have proved -- its line is marked.  And a run that ends
     with any query unsettled says so in one summary line, because otherwise
     the only way to know is to read every line of a three-minute log. *)
  let is_settled = function Verdict.Valid -> true | _ -> false
  let weakened_by_earlier sols = List.exists sols ~f:(Fn.non is_settled)

  (* what the run has answered so far, for the summary: the fold's accumulator
     cannot serve, because the other two query kinds return an empty one and a
     file may mix them *)
  let verdicts_printed : Verdict.t list ref = ref []

  (* [check_bounds] serves two callers: the fold over a file's queries, and
     [check_dist_bounds]'s CEGAR loop, which probes candidate bounds and passes
     [-1] for the index.  Only the first kind is a query of the file, so only
     those are counted in the summary and only those can be weakened by an
     earlier gap; a probe's verdict is printed, as it always has been, but it is
     not part of the file's tally. *)
  let print_query_verdict ~print_sol ~top_level ~weakened ?(info = None)
      ?(witness = None) sol time =
    if top_level then verdicts_printed := !verdicts_printed @ [ sol ];
    if print_sol then
      print_endline @@ String.concat ~sep:", "
      @@ MuCLP.Problem.(
           if config.output_yes_no then lts_str_of_solution else str_of_solution)
           sol
         ::
         (match info with
         | Some n when config.output_iteration -> [ sprintf "%d" n ]
         | _ -> [])
      @ (if config.output_time then [ time ] else [])
      @ (match witness with
        | Some w when config.output_witness -> [ w ]
        | _ -> [])
      @ if weakened then [ "weakened by an earlier unsettled query" ] else []

  let print_run_summary ~print_sol =
    let sols = !verdicts_printed in
    if print_sol && List.length sols > 1 then
      let n_of f = List.count sols ~f in
      print_endline
      @@ sprintf "%d queries: %d settled, %d unsettled (%s)" (List.length sols)
           (n_of is_settled)
           (n_of (Fn.non is_settled))
           (String.concat ~sep:", "
           @@ List.filter_map
                MuCLP.Problem.[ Invalid; Unknown; Timeout ]
                ~f:(fun v ->
                  let n = n_of (Stdlib.( = ) v) in
                  if n = 0 then None
                  else Some (sprintf "%d %s" n (Verdict.str_of v))))

  let check_bounds ~print_sol (i, sols, pareto_cache) qfl
      (query : QFL.Problem.check) =
    Timer.start ();
    (* a refusal of the input, not an internal error: the bound checking below
       is built for least fixpoints only *)
    if not @@ QFL.Problem.has_only_mu qfl then
      Common.Refusal.refuse
        "the QFL bound checker handles least fixpoints (=mu) only, and this \
         problem defines a greatest fixpoint (=nu)";
    let qfl_before_unfold = qfl in
    let accel_problem = QFL.Accel.accelerate_applicable qfl_before_unfold in
    let fsub, qfl = QFL.Problem.unfold qfl_before_unfold in
    Debug.print ~id:None
    @@ lazy (sprintf "inlined: %s\n" @@ QFL.Problem.str_of ~fsub:(Some fsub) qfl);
    let ((ua_preds, prefp, rank, postfp), pqes), backup =
      let query_fml =
        Formula.subst_funcs fsub @@ QFL.Problem.formula_of_query (Check query)
      in
      match query.kind with
      | LB -> (
          match
            if config.enable_geometric_pla then
              QFL.Accel.accelerated_problem_to_qfl_if_exact accel_problem
            else None
          with
          | Some accel_qfl ->
              let preds_for_fsub_domain = accel_qfl.preds in
              let fsub, qfl = QFL.Problem.unfold accel_qfl in
              Debug.print ~id:None
              @@ lazy
                   (sprintf
                      "geometric PLA lower-bound acceleration used\n\
                       exact accelerated problem:\n\
                       %s\n"
                      (QFL.Problem.str_of ~fsub:(Some fsub) qfl));
              let query_fml =
                Formula.subst_funcs fsub
                @@ QFL.Problem.formula_of_query (Check query)
              in
              cgen_pqes_lb qfl ~preds_for_fsub_domain query_fml fsub
                pareto_cache
          | None ->
              Debug.print ~id:None
              @@ lazy
                   (if config.enable_geometric_pla then
                      "geometric PLA lower-bound acceleration fallback: exact \
                       accelerated QFL body not available"
                    else "geometric PLA lower-bound acceleration disabled");
              cgen_pqes_lb qfl
                ?accel_problem:
                  (if config.enable_geometric_pla then Some accel_problem
                   else None)
                ~preds_for_fsub_domain:qfl_before_unfold.preds query_fml fsub
                pareto_cache)
      | UB -> cgen_pqes_ub qfl accel_problem query_fml fsub pareto_cache
    in
    let timeout =
      match backup with None -> None | Some _ -> config.pareto_cache_timeout
    in
    Debug.print ~id:None
    @@ lazy
         (sprintf "[7. Generated PQE constraints]\n******* Generated PQEs:\n%s"
         @@ PCSP.Problem.str_of pqes);
    let open Or_error.Monad_infix in
    pcsp_solver ~primal:true >>= fun (module PCSPSolver) ->
    pcsp_solver ~primal:false >>= fun (module PCSPSolverPC) ->
    ( (match backup with
      | None -> PCSPSolver.solve
      | Some _ -> PCSPSolverPC.solve)
        ~timeout pqes
    >>= function
      | PCSP.Problem.Sat model, info ->
          Debug.print ~id:None @@ lazy "[8. Solver result]\nresult: valid";
          let tsub =
            Logic.ExtTerm.to_old_subst Map.Poly.empty Map.Poly.empty model
          in
          let prefp =
            List.map prefp ~f:(fun (name, (args, quant_pred)) ->
                ( name,
                  (args, Evaluator.simplify_term @@ Term.subst tsub quant_pred)
                ))
          in
          let rank =
            List.map rank ~f:(fun (name, (args, quant_pred)) ->
                ( name,
                  (args, Evaluator.simplify_term @@ Term.subst tsub quant_pred)
                ))
          in
          let postfp =
            List.map postfp ~f:(fun (name, (args, quant_pred)) ->
                ( name,
                  (args, Evaluator.simplify_term @@ Term.subst tsub quant_pred)
                ))
          in
          (match ua_preds with
          | None -> ()
          | Some ua_preds ->
              let ua_preds =
                List.map ua_preds ~f:(fun pred ->
                    { pred with body = Term.subst tsub pred.body })
              in
              Debug.print ~id:None
              @@ lazy
                   (sprintf "\nunderapproximated:\n%s"
                   @@ QFL.Pred.str_of_list ua_preds));
          if not @@ List.is_empty prefp then (
            Debug.print @@ lazy "\nsynthesized prefixpoint:";
            print_templ prefp);
          if not @@ List.is_empty rank then (
            Debug.print @@ lazy "\nsynthesized ranking supermartingales:";
            print_templ rank);
          if not @@ List.is_empty postfp then (
            Debug.print @@ lazy "\nsynthesized postfixpoint:";
            print_templ postfp);
          Ok
            ( Verdict.Valid,
              Some (match query.kind with LB -> postfp | UB -> prefp),
              info )
      | Unsat _, info ->
          Debug.print ~id:None
          @@ lazy
               "[8. Solver result]\nresult: unknown\nreason: unsat/no witness";
          Debug.print @@ lazy "the templates used may not be expressive enough";
          Ok (Unknown, None, info)
      | Unknown, info ->
          Debug.print ~id:None @@ lazy "[8. Solver result]\nresult: unknown";
          Debug.print
          @@ lazy
               "the backend PQE solver failed or the templates used may not be \
                expressive enough";
          Ok (Unknown, None, info)
      | OutSpace _, _ -> failwith "out of space" (* TODO *)
      | Timeout, info ->
          Debug.print ~id:None @@ lazy "[8. Solver result]\nresult: timeout";
          Ok (Timeout, None, info) )
    >>= function
    | (Verdict.Valid as sol), Some fp, info ->
        let time = Timer.stop () in
        Debug.print @@ lazy "=========================";
        let fp =
          fp
          @ List.map (Map.Poly.to_alist fsub)
              ~f:(fun (name, (args, quant_pred)) ->
                ( name,
                  (args, Term.subst_funcs (Map.Poly.of_alist_exn fp) quant_pred)
                ))
        in
        print_query_verdict ~print_sol ~top_level:(i >= 0)
          ~weakened:(weakened_by_earlier sols) ~info:(Some info)
          ~witness:(Some (str_of_templ fp))
          sol
          (match backup with
          | Some _ -> sprintf "%fs (cache)" time
          | None -> sprintf "%fs" time);
        Or_error.return
          ( sols @ [ sol ],
            pareto_cache
            @ [ (match backup with None -> Some fp | Some _ -> None) ] )
    | sol0, _, _ -> (
        match backup with
        | None ->
            let time = Timer.stop () in
            Debug.print
            @@ lazy
                 (sprintf "Problem %d was not settled by the backend" (i + 1));
            print_query_verdict ~print_sol ~top_level:(i >= 0)
              ~weakened:(weakened_by_earlier sols) sol0 (sprintf "%fs" time);
            Or_error.return (sols @ [ sol0 ], pareto_cache @ [ None ])
        | Some ((ua_preds, prefp, rank, postfp), pqes) -> (
            Debug.print @@ lazy "\npareto cache did not help, try backup";
            Debug.print ~id:None
            @@ lazy
                 (sprintf "******* Generated PQEs:\n%s"
                 @@ PCSP.Problem.str_of pqes);
            let open Or_error.Monad_infix in
            pcsp_solver ~primal:true >>= fun (module PCSPSolver) ->
            ( PCSPSolver.solve pqes >>= function
              | PCSP.Problem.Sat model, info ->
                  let tsub =
                    Logic.ExtTerm.to_old_subst Map.Poly.empty Map.Poly.empty
                      model
                  in
                  let prefp =
                    List.map prefp ~f:(fun (name, (args, quant_pred)) ->
                        ( name,
                          ( args,
                            Evaluator.simplify_term
                            @@ Term.subst tsub quant_pred ) ))
                  in
                  let rank =
                    List.map rank ~f:(fun (name, (args, quant_pred)) ->
                        ( name,
                          ( args,
                            Evaluator.simplify_term
                            @@ Term.subst tsub quant_pred ) ))
                  in
                  let postfp =
                    List.map postfp ~f:(fun (name, (args, quant_pred)) ->
                        ( name,
                          ( args,
                            Evaluator.simplify_term
                            @@ Term.subst tsub quant_pred ) ))
                  in
                  (match ua_preds with
                  | None -> ()
                  | Some ua_preds ->
                      let ua_preds =
                        List.map ua_preds ~f:(fun (pred : QFL.Pred.t) ->
                            { pred with body = Term.subst tsub pred.body })
                      in
                      Debug.print ~id:None
                      @@ lazy
                           (sprintf "\nunderapproximated:\n%s"
                           @@ QFL.Pred.str_of_list ua_preds));
                  if not @@ List.is_empty prefp then (
                    Debug.print @@ lazy "\nsynthesized prefixpoint:";
                    print_templ prefp);
                  if not @@ List.is_empty rank then (
                    Debug.print
                    @@ lazy "\nsynthesized ranking supermartingales:";
                    print_templ rank);
                  if not @@ List.is_empty postfp then (
                    Debug.print @@ lazy "\nsynthesized postfixpoint:";
                    print_templ postfp);
                  Ok
                    ( Verdict.Valid,
                      Some (match query.kind with LB -> postfp | UB -> prefp),
                      info )
              | Unsat _, info ->
                  Debug.print
                  @@ lazy "the templates used may not be expressive enough";
                  Ok (Unknown, None, info)
              | Unknown, info ->
                  Debug.print
                  @@ lazy
                       "the backend PQE solver failed or the templates used \
                        may not be expressive enough";
                  Ok (Unknown, None, info)
              | OutSpace _, _ -> failwith "out of space" (* TODO *)
              | Timeout, info -> Ok (Timeout, None, info) )
            >>= function
            | (Verdict.Valid as sol), Some fp, info ->
                let time = Timer.stop () in
                Debug.print @@ lazy "=========================";
                let fp =
                  fp
                  @ List.map (Map.Poly.to_alist fsub)
                      ~f:(fun (name, (args, quant_pred)) ->
                        ( name,
                          ( args,
                            Term.subst_funcs (Map.Poly.of_alist_exn fp)
                              quant_pred ) ))
                in
                print_query_verdict ~print_sol ~top_level:(i >= 0)
                  ~weakened:(weakened_by_earlier sols) ~info:(Some info)
                  ~witness:(Some (str_of_templ fp))
                  sol (sprintf "%fs" time);
                Or_error.return (sols @ [ sol ], pareto_cache @ [ Some fp ])
            | sol0, _, _ ->
                let time = Timer.stop () in
                Debug.print
                @@ lazy
                     (sprintf
                        "Problem %d was not settled by the backend, and the \
                         backup did not settle it either"
                        (i + 1));
                print_query_verdict ~print_sol ~top_level:(i >= 0)
                  ~weakened:(weakened_by_earlier sols) sol0 (sprintf "%fs" time);
                Or_error.return (sols @ [ sol0 ], pareto_cache @ [ None ])))

  (* Raised when the backend settles neither the bound asked for nor, at the
     one site that offers alternatives, any of them.  It is a named exception
     rather than [failwith] for two reasons: the search below uses it as control
     flow -- "that bound did not work, try the next" -- and a catch-all there
     would also swallow the timer's asynchronous [Timeout], continuing the
     search as if the budget had not run out; and what escapes the search is an
     ordinary "no answer", which the caller turns into an [unknown] verdict
     instead of a backtrace. *)
  exception Dist_check_unsettled

  (* the backend settled none of the bounds the search offered it: an answer
     about the problem's difficulty, not a failure of the tool, so it is
     reported as one and the caller's fold carries on with the file's remaining
     queries *)
  let report_unsettled_dist_check ~print_sol ub_time opt_time =
    print_query_verdict ~print_sol ~top_level:true ~weakened:false
      Verdict.Unknown
      (sprintf "%fs (UB checker), %fs (OMT solver)" ub_time opt_time);
    Or_error.return ([], [])

  let check_dist_bounds_inner ~print_sol ~ub_time ~opt_time qfl
      (q : QFL.Problem.dist_check) =
    let check ?(strict = false) bound sub =
      Timer.start ();
      let query : QFL.Problem.check =
        {
          params = [];
          left = None;
          kind = UB;
          name = q.name;
          args = q.args;
          bound;
          strict;
        }
      in
      let qfl =
        let sub =
          Map.Poly.of_alist_exn
            (List.map sub ~f:(fun (x, v) -> (x, T_real.mk_real v)))
        in
        QFL.Problem.
          {
            preds = List.map qfl.preds ~f:(QFL.Pred.subst sub);
            query = Check query;
          }
      in
      Debug.print ~id:None
      @@ lazy (sprintf "\ninput: %s\n" @@ QFL.Problem.str_of qfl);
      match check_bounds ~print_sol (-1, [], []) qfl query with
      | Ok (_, [ Some sol ]) ->
          ub_time := !ub_time +. Timer.stop ();
          let senv, t = List.Assoc.find_exn ~equal:Stdlib.( = ) sol q.name in
          let bound =
            Value.real_of @@ Evaluator.eval_term
            @@ Term.subst
                 (Map.Poly.of_alist_exn
                 @@ List.map2_exn senv q.args ~f:(fun (x, _) t -> (x, t)))
                 t
          in
          Debug.print @@ lazy (sprintf "found bound: %s\n" (Q.to_string bound));
          (List.map sub ~f:snd, bound)
      | _ ->
          ub_time := !ub_time +. Timer.stop ();
          raise Dist_check_unsettled
    in
    let h =
      let res =
        if Formula.is_atom q.bound then
          let atm, _ = Formula.let_atom q.bound in
          if Atom.is_psym_app atm then
            let op, args, _ = Atom.let_psym_app atm in
            match (op, args) with
            | T_real.RLeq, [ t; bound ] -> (
                try
                  let bound =
                    match Evaluator.eval_term bound with
                    | Value.Real r -> r
                    | _ -> failwith "unexpected"
                  in
                  let monomials =
                    Normalizer.linear_real_monomials_of (Value.Real Q.one) t
                  in
                  let c0 =
                    match Map.Poly.find monomials None with
                    | Some const -> Value.real_of const
                    | None -> Q.zero
                  in
                  let b = Q.(bound - c0) in
                  let cs =
                    List.map q.params ~f:(fun (var, _) ->
                        match
                          Map.Poly.find monomials
                            (Some (Term.mk_var var T_real.SReal))
                        with
                        | Some coeff -> Q.(Value.real_of coeff / b)
                        | None -> Q.zero)
                  in
                  Some cs
                with exn_ when not (Common.Timer.is_async exn_) -> None)
            | _ -> None
          else None
        else None
      in
      match res with
      | None ->
          if config.dist_bound_initialize_standard_basis then
            List.map ~f:(check ((*ToDo*) T_real.rone ()))
            @@ List.init (List.length q.params) ~f:(fun i ->
                List.init (List.length q.params) ~f:(fun j ->
                    ( Ident.Tvar ("@" ^ string_of_int (j + 1)),
                      if i = j then Q.one else Q.zero )))
          else
            List.init (List.length q.params) ~f:(fun i ->
                ( List.init (List.length q.params) ~f:(fun j ->
                      if i = j then Q.one else Q.zero),
                  Q.one ))
      | Some ws ->
          [
            check (T_real.rone ())
            @@ List.mapi ws ~f:(fun i w ->
                (Ident.Tvar ("@" ^ string_of_int (i + 1)), w));
          ]
    in
    let generators_of h =
      let vs = List.map q.params ~f:fst in
      let vmap = MuCyc.ApronInterface.mk_varmap vs in
      let atoms =
        List.map ~f:Normalizer.normalize_atom
        @@ List.map vs ~f:(fun v ->
            T_real.mk_rleq (T_real.rzero ()) (Term.mk_var v T_real.SReal))
        @ List.map h ~f:(fun (ws, b) ->
            T_real.mk_rleq
              (T_real.mk_rsum (T_real.rzero ())
              @@ List.map2_exn ws vs ~f:(fun w v ->
                  T_real.mk_rmul (T_real.mk_real w) (Term.mk_var v T_real.SReal))
              )
              (T_real.mk_real b))
      in
      let polyhedron = MuCyc.ApronInterface.mk_real_polyhedron vmap atoms in
      let vertices = MuCyc.ApronInterface.mk_vertex polyhedron vmap in
      List.map vertices ~f:(fun vertex ->
          List.map vs ~f:(Map.Poly.find_exn vertex))
    in
    let refine h =
      let gens = generators_of h in
      Debug.print ~id:None
      @@ lazy
           (sprintf "generators: %s"
              (String.concat_map_list ~sep:", " gens ~f:(fun ps ->
                   sprintf "[%s]"
                     (String.concat_map_list ~sep:", " ps ~f:Term.str_of))));
      let eps, weight, bounds =
        List.fold gens
          ~init:
            ( Q.zero,
              List.init (List.length q.params) ~f:(fun _ -> Q.zero),
              [ (Q.one, config.dist_bound_use_strict_bound) ] )
          ~f:(fun (eps, weight, bounds) ps ->
            if
              let sub =
                Map.Poly.of_alist_exn
                @@ List.map2_exn q.params ps ~f:(fun param p -> (fst param, p))
              in
              Evaluator.eval (Formula.subst sub q.bound)
            then (
              Debug.print ~id:None
              @@ lazy
                   (sprintf "non-cex generator: [%s]"
                      (String.concat_map_list ~sep:", " ps ~f:Term.str_of));
              (eps, weight, bounds))
            else (
              Debug.print ~id:None
              @@ lazy
                   (sprintf "cex generator: [%s]"
                      (String.concat_map_list ~sep:", " ps ~f:Term.str_of));
              let qs =
                (* the new variables replace the bound's parameters, so they
                   must not be a variable the bound already mentions *)
                let bound_tvs = Formula.tvs_of q.bound in
                List.init (List.length q.params) ~f:(fun _ ->
                    Term.mk_var
                      (Ident.mk_fresh_tvar_avoiding ~prefix:"q_"
                         ~taken:(Set.mem bound_tvs) ())
                      T_real.SReal)
              in
              let constrs =
                let sub =
                  Map.Poly.of_alist_exn
                  @@ List.map2_exn q.params qs ~f:(fun param q ->
                      (fst param, q))
                in
                Formula.subst sub q.bound
                :: Formula.leq
                     (T_real.mk_rsum (T_real.rzero ()) qs)
                     (T_real.rone ())
                :: List.map qs ~f:(fun q -> Formula.leq (T_real.rzero ()) q)
                @ List.map2_exn qs ps ~f:Formula.leq
              in
              let obj =
                let f =
                  if config.dist_bound_use_l1_norm then T_real.mk_rsub
                  else fun ?(info = Dummy) p q ->
                    let d = T_real.mk_rsub p q in
                    T_real.mk_rmul ~info d d
                in
                T_real.mk_rsum (T_real.rzero ()) (List.map2_exn ps qs ~f)
              in
              let fenv = Map.Poly.empty in
              Timer.start ();
              match
                if config.dist_bound_use_optimathsat then
                  OptiMathSAT.Solver.minimize constrs obj
                else
                  Z3Smt.Z3interface.check_opt ~id:None fenv constrs ~max:false
                    obj
              with
              | Some (eps', _, model) ->
                  opt_time := !opt_time +. Timer.stop ();
                  let sub =
                    Map.Poly.of_alist_exn
                    @@ List.map model ~f:(fun ((x, s), v) ->
                        let v =
                          match v with None -> Term.mk_dummy s | Some v -> v
                        in
                        if false then
                          print_endline
                          @@ sprintf "%s -> %s" (Ident.name_of_tvar x)
                               (Term.str_of v);
                        (x, v))
                  in
                  let eps' =
                    match eps' with
                    | Some eps' when false -> (
                        match Evaluator.eval_term eps' with
                        | Value.Real eps' -> eps'
                        | Value.Int eps' -> Q.of_bigint eps'
                        | eps' -> failwith ("eps' = " ^ Value.str_of eps'))
                    | _ -> (
                        match Evaluator.eval_term (Term.subst sub obj) with
                        | Value.Real eps' -> eps'
                        | eps' -> failwith ("eps' = " ^ Value.str_of eps'))
                  in
                  let qs = List.map qs ~f:(Term.subst sub) in
                  if Q.(eps < eps') then
                    let ws = List.map2_exn ps qs ~f:T_real.mk_rsub in
                    let bound =
                      if config.dist_bound_use_l1_norm then Q.one
                      else
                        let q_w =
                          T_real.mk_rsum (T_real.rzero ())
                            (List.map2_exn qs ws ~f:T_real.mk_rmul)
                        in
                        match Evaluator.eval_term q_w with
                        | Value.Real q_w -> q_w
                        | q_w -> failwith ("q_w = " ^ Value.str_of q_w)
                    in
                    let bound =
                      match config.dist_bound_relax with
                      | None -> [ (bound, config.dist_bound_use_strict_bound) ]
                      | Some r ->
                          let bound' =
                            let p_w =
                              T_real.mk_rsum (T_real.rzero ())
                                (List.map2_exn ps ws ~f:T_real.mk_rmul)
                            in
                            match Evaluator.eval_term p_w with
                            | Value.Real p_w -> p_w
                            | p_w -> failwith ("p_w = " ^ Value.str_of p_w)
                          in
                          [
                            (bound, config.dist_bound_use_strict_bound);
                            (Q.(min (bound + of_float r) bound'), true);
                          ]
                    in
                    ( eps',
                      List.map ws ~f:(fun w ->
                          match Evaluator.eval_term w with
                          | Value.Real w -> w
                          | w -> failwith ("w = " ^ Value.str_of w)),
                      bound )
                  else (eps, weight, bounds)
              | None ->
                  opt_time := !opt_time +. Timer.stop ();
                  assert false))
      in
      if Q.(eps = zero) then None
      else (
        Debug.print ~id:None
        @@ lazy
             (sprintf
                "abstraction refinement with the new weight [%s] and upper \
                 bound %s"
                (String.concat_map_list ~sep:", " weight ~f:Q.to_string)
                (Q.to_string (fst @@ List.hd_exn bounds)));
        let sub =
          List.mapi weight ~f:(fun i w ->
              (Ident.Tvar ("@" ^ string_of_int (i + 1)), w))
        in
        let res =
          let rec loop = function
            | [] -> assert false
            | (bound, strict) :: bounds -> (
                try check ~strict (T_real.mk_real bound) sub
                with Dist_check_unsettled when Fn.non List.is_empty bounds ->
                  loop bounds)
          in
          loop bounds
        in
        Some (res :: h))
    in
    let rec cegar h =
      match refine h with
      | None ->
          if print_sol then (
            print_endline
            @@ String.concat ~sep:", "
                 [
                   Verdict.str_of Verdict.Valid;
                   sprintf "%fs (UB checker)" !ub_time;
                   sprintf "%fs (OMT solver)" !opt_time;
                 ];
            List.iter h ~f:(fun (ws, b) ->
                print_endline
                @@ sprintf "weight: [%s], bound: %s"
                     (String.concat_map_list ~sep:", " ws ~f:Q.to_string)
                     (Q.to_string b)));
          Ok ([], [])
      | Some h -> cegar h
    in
    match cegar h with
    | Ok (_, _) -> Or_error.return ([], [])
    | Error err -> Or_error.error_string (Error.to_string_hum err)
    | exception Dist_check_unsettled ->
        report_unsettled_dist_check ~print_sol !ub_time !opt_time

  let check_dist_bounds ~print_sol qfl (q : QFL.Problem.dist_check) =
    let ub_time = ref 0.0 and opt_time = ref 0.0 in
    try check_dist_bounds_inner ~print_sol ~ub_time ~opt_time qfl q
    with Dist_check_unsettled ->
      report_unsettled_dist_check ~print_sol !ub_time !opt_time

  let solve_qfl ?(print_sol = false) (qfls : QFL.Problem.t list) =
    Debug.print @@ lazy "======== MuVal ========";
    verdicts_printed := [];
    let res =
      List.foldi qfls
        ~init:(Or_error.return ([], []))
        ~f:(fun i res qfl ->
          Debug.print
          @@ lazy
               (sprintf "\n---- Problem %d/%d ----" (i + 1) (List.length qfls));
          let open Or_error in
          res >>= fun (sols, pareto_cache) ->
          Debug.print ~id:None
          @@ lazy (sprintf "input: %s\n" @@ QFL.Problem.str_of qfl);
          let detections =
            if config.enable_geometric_pla then QFL.Accel.detect_geometric qfl
            else []
          in
          if config.enable_geometric_pla && not (List.is_empty detections) then
            Debug.print ~id:None
            @@ lazy
                 (let accel_problem = QFL.Accel.accelerate_applicable qfl in
                  let accel_template_config =
                    QFL.Accel.
                      {
                        num_conds = config.quant_prefp_templ_num_conds;
                        use_orig_ite = config.quant_prefp_templ_use_orig_ite;
                        cond_degree = config.quant_prefp_templ_cond_degree;
                        term_degree = config.quant_prefp_templ_term_degree;
                      }
                  in
                  sprintf
                    "[3. PLA detection]\n\
                     %s\n\
                     %s\n\
                     [4. Accelerated operator]\n\
                     %s\n\
                     %s\n"
                    (QFL.Accel.str_of_detections detections)
                    (QFL.Accel.str_of_geo_expectations
                    @@ QFL.Accel.geo_expectations_of_detections detections)
                    (QFL.Accel.str_of_accel_problem accel_problem)
                    (QFL.Accel.str_of_accel_formula_debug accel_template_config
                       accel_problem));
          let qfl =
            if true (*ToDo*) then qfl
            else (* this may cause size explosion? *)
              let qfl = QFL.Problem.simplify qfl in
              Debug.print ~id:None
              @@ lazy (sprintf "simplified: %s\n" @@ QFL.Problem.str_of qfl);
              qfl
          in
          match qfl.query with
          | ASAT (init, param_senv, param_constr) ->
              check_almost_sure_satisfaction_of_omega_regular_properties
                ~print_sol qfl
                (init, param_senv, Formula.conjuncts_of param_constr)
          | Check query ->
              check_bounds ~print_sol (i, sols, pareto_cache) qfl query
          | DistCheck query -> check_dist_bounds ~print_sol qfl query)
    in
    print_run_summary ~print_sol;
    res
end
