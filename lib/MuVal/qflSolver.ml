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

  (* [integrate_all constrs]: every integral [unif r. F] of the constraints
     replaced by its closed form ([QFL.Unif.integrate], which refuses an
     integrand it cannot integrate exactly).  Applied to every constraint list
     just before it becomes a PQE problem: by then each unknown has been
     replaced by its template, so an integrand is a piecewise polynomial in
     the integration variable, and no PQE solver sees the symbol.  The
     closed form is exact, so a certificate for the integrated constraints is
     one for the constraints with the integrals. *)
  let integrate_all = List.map ~f:QFL.Unif.integrate_formula

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

  (* [templates_for ~has_unif]: the template shapes of a bound check.  Without
     an integral, exactly [config.qfl.templates]: a problem with no [unif] is
     solved as the configuration says.  With one, the configuration's shapes
     with every condition taken from the body's own guards -- no template
     condition ([num_conds = 0]) in the pre-fixpoint, ranking and
     post-fixpoint templates, the input's if-then-else kept ([use_orig_ite]),
     and no guard in the under-approximation ([cond_degree = None]); the term
     degrees and every other field are the configuration's.

     Why: the closed form of [unif r. F] is exact only when each guard of the
     integrand is [alpha + beta * r >= 0] with [beta] a constant, for then the
     breakpoint [-alpha / beta] is a term of the state variables and the
     integral splits there.  A template condition [c0 + c1 * x >= 0] with
     unknown [c1], met at a point [x + 3r - 2], has [beta = 3 * c1]: the
     breakpoint is a rational function of the template's parameters and the
     integration refuses.  Inside a body-guard template every guard is one of
     the input's own, instantiated at the point of application, so its
     coefficient of [r] is a product of the input's constants and the
     integral is computed exactly.  Guarantees: the template shapes, never the
     verdict, change -- a certificate found under either is checked by the
     same constraints, so soundness is the bound checker's.  A configuration
     with conditions of degree 0 or an integral at a point free of [r] would
     integrate without this; it is overridden anyway, since a problem's
     integrals are the trigger, not their shapes. *)
  let templates_for ~has_unif : QflConfig.templates =
    if not has_unif then config.qfl.templates
    else
      let body_guards (t : QflConfig.quant_template) =
        { t with num_conds = 0; use_orig_ite = true }
      in
      let templates = config.qfl.templates in
      {
        templates with
        prefp = body_guards templates.prefp;
        rank = body_guards templates.rank;
        postfp = body_guards templates.postfp;
        underapprox = { templates.underapprox with cond_degree = None };
      }

  (* [config] with its template shapes replaced by [templates]; the three
     template-building functions below shadow [config] with it, so their
     template shapes are the caller's per-problem choice and every other
     field is the configuration's *)
  let with_templates templates =
    { config with qfl = { config.qfl with templates } }

  let underapprox_of ~templates (pred : QFL.Pred.t) =
    let config = with_templates templates in
    let cond, template =
      Templ.underapprox_of
        ~cond_degree:config.qfl.templates.underapprox.cond_degree
        ~term_degree:config.qfl.templates.underapprox.term_degree pred.args
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

  (* [num_conds], [cond_degree], [zero_reward]: the [QflConfig.Cache_after] payload *)
  let gen_cache_constr ~num_conds ~cond_degree ~zero_reward for_prefp
      (preds : QFL.Pred.t list) fsub pareto_cache =
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
                if zero_reward then T_real.rzero ()
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
                    @@ List.init (num_conds + 1)
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
                        List.init (num_conds + 1)
                          ~f:(fun _i ->
                            let w = Ident.mk_fresh_tvar ~prefix:(Some "w") () in
                            pc_templ_params :=
                              Map.add_exn !pc_templ_params ~key:w
                                ~data:T_real.SReal;
                            Term.mk_var w T_real.SReal))
                  in
                  let w_constrs =
                    let conds =
                      List.init (num_conds + 1)
                        ~f:(fun _i ->
                          let templ =
                            Templ.mk_affine
                            @@ Templ.terms_of cond_degree
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
                (if zero_reward then []
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

  (** The environments of a set of PQEs: [exi_senv], the template parameters,
      are the only unknowns, and there are no universally quantified variables
      at the problem level (each constraint quantifies its own).

      A template parameter is a CONSTANT to be found -- a nullary term of sort
      [Real] (or [Int]) -- and its kind says so: [RealFun] (or [IntFun]).  The
      kind is what a constraint solver dispatches on.  A backend that declares
      every unknown as a real constant (PolyQEnt) reads the sort alone and is
      indifferent to it; PCSat chooses a template by it, and an empty kind map
      defaulted every parameter to an ordinary predicate, for which a
      real-valued unknown has no template, so PCSat refused every PQE.  A
      parameter of any other sort keeps the default kind. *)
  let pqe_envs_of exi_senv =
    SMT.Problem.
      {
        decl_reading = SMT.Problem.Synthesize;
        lifted_universals = Map.Poly.empty;
        candidates = Map.Poly.empty;
        uni_sort = Set.Poly.empty;
        uni_senv = Map.Poly.empty;
        exi_senv;
        dep_map = Map.Poly.empty;
        kind_map =
          Map.Poly.filter_map exi_senv ~f:(fun sort ->
              if Term.is_real_sort sort then Some Kind.RealFun
              else if Term.is_int_sort sort then Some Kind.IntFun
              else None);
        fenv = Map.Poly.empty;
        dtenv = Map.Poly.empty;
      }

  (* Lower-bound constraints.  ASSUMES every body is nonnegative wherever the
     recursive functions it applies are nonnegative, at every state: the
     under-approximation replaces a body by [0] where its guard template is
     negative, which is below the body only where the body is nonnegative, so
     a negative reward breaks the certificate ([X =mu -1 + X/2], whose real
     solution is [-2], was answered valid for [X >= 0] with every template
     [0]).  [refuse_ill_formed] establishes the assumption for a query reached
     through [solve_qfl]; a caller that builds a problem otherwise must
     establish it itself. *)
  (* [cgen_pqes_lb ... ~state_guard]: [state_guard name args] are hypotheses
     on the state [args] of the function [name] (see [integer_state_guard]);
     the post-fixpoint, pre-fixpoint, ranking, ordering and template
     non-negativity obligations of [name] are stated under them, so a
     certificate is checked at those states only.  Default: no hypothesis,
     every obligation at every state. *)
  (* [~max_cert]: the certificate of the bound is [max(0, L)] for the
     post-fixpoint template [L], whose sign is left free.  This is sound when
     the under-approximated body [Phi'] is monotone on real-valued functions
     (what [refuse_unsound_query_shape] admits is: sums, non-negative factors,
     [min], [max], conditionals with unknown-free guards, integrals) and
     [Phi'(0) >= 0]: where [L <= 0], [max(0, L) = 0 <= Phi'(0) <=
     Phi'(max(0, L))]; where [L > 0], [L <= Phi'(L) <= Phi'(max(0, L))].  So
     the post-fixpoint obligation is required only under [L > 0], the
     template's non-negativity is dropped, [Phi'(0) >= 0] is added, [L <= u]
     still gives [max(0, L) <= u] since [u >= 0], and the query is asked of
     [max(0, L)] itself.  The returned post-fixpoint is [max(0, L)]. *)
  let cgen_pqes_lb ~templates (qfl : QFL.Problem.t) ?accel_problem
      ?(state_guard = fun _ _ -> []) ?(max_cert = false) ~preds_for_fsub_domain
      query_fml fsub pareto_cache =
    let config = with_templates templates in
    let query_fml = Formula.elim_min_max_list query_fml in
    let qfl_preds_for_templates =
      match accel_problem with
      | Some accel_problem when config.qfl.enable_geometric_pla ->
          let active_names = QFL.Accel.active_pred_names accel_problem in
          List.filter qfl.preds ~f:(fun pred -> Set.mem active_names pred.name)
      | _ -> qfl.preds
    in
    let conds, templ_paramss, templ_constrss, ua_preds =
      List.unzip4
      @@ List.map qfl_preds_for_templates ~f:(underapprox_of ~templates)
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
                (* [guard_complement_template]: where the guard is negative
                   the value is an affine template too (of the pre-fixpoint
                   template's term degree); off, it is zero *)
                let templ_params, quant_pred =
                  if config.qfl.templates.guard_complement_template then
                    let templ =
                      Templ.mk_affine
                      @@ Templ.terms_of
                           config.qfl.templates.prefp.term_degree (*ToDo*)
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
        (Templ.gen_quant_template ~num_conds:config.qfl.templates.prefp.num_conds
           ~use_orig_ite:config.qfl.templates.prefp.use_orig_ite
           ~annot_branches_follow_ite:
             config.qfl.templates.prefp.annot_branches_follow_ite
           ~cond_branches_follow_ite:
             config.qfl.templates.prefp.cond_branches_follow_ite
           ~cond_degree:config.qfl.templates.prefp.cond_degree
           ~term_degree:config.qfl.templates.prefp.term_degree)
    in
    let rank_templ_paramss, rank_templ_preds =
      strengthen_guard
        (Templ.gen_quant_template ~num_conds:config.qfl.templates.rank.num_conds
           ~use_orig_ite:config.qfl.templates.rank.use_orig_ite
           ~annot_branches_follow_ite:
             config.qfl.templates.rank.annot_branches_follow_ite
           ~cond_branches_follow_ite:
             config.qfl.templates.rank.cond_branches_follow_ite
           ~cond_degree:config.qfl.templates.rank.cond_degree
           ~term_degree:config.qfl.templates.rank.term_degree)
    in
    let coeffs = ref [] in
    let postfp_templ_paramss, postfp_templ_preds =
      strengthen_guard
        (Templ.gen_quant_template ~coeffs:(Some coeffs)
           ~num_conds:config.qfl.templates.postfp.num_conds
           ~use_orig_ite:config.qfl.templates.postfp.use_orig_ite
           ~annot_branches_follow_ite:
             config.qfl.templates.postfp.annot_branches_follow_ite
           ~cond_branches_follow_ite:
             config.qfl.templates.postfp.cond_branches_follow_ite
           ~cond_degree:config.qfl.templates.postfp.cond_degree
           ~term_degree:config.qfl.templates.postfp.term_degree)
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
          let head = Term.fvar_app_of_senv pred.name pred.args T_real.SReal in
          let positive =
            if max_cert then [ Formula.gt head (T_real.rzero ()) ] else []
          in
          List.concat_map (Term.elim_min_max_list pred.body) ~f:(fun body ->
              QFL.Problem.imply_antecedents
                (state_guard pred.name pred.args @ positive)
              @@ Formula.geq body head))
    in
    (* [Phi'(0) >= 0], the premise of [max_cert] that QFL's well-formedness
       does not give when a body subtracts *)
    let body_at_zero_nonnegative_constrs =
      if not max_cert then []
      else
        let zero_sub =
          Map.Poly.of_alist_exn
          @@ List.map ua_preds ~f:(fun (pred : QFL.Pred.t) ->
              (pred.name, (pred.args, T_real.rzero ())))
        in
        List.concat_map ua_preds ~f:(fun pred ->
            List.concat_map
              (Term.elim_min_max_list (Term.subst_funcs zero_sub pred.body))
              ~f:(fun body ->
                QFL.Problem.imply_antecedents (state_guard pred.name pred.args)
                @@ Formula.geq body (T_real.rzero ())))
    in
    let cert_of (name, (args, l)) =
      if max_cert then
        ( name,
          ( args,
            T_bool.mk_if_then_else
              (T_bool.of_formula @@ Formula.geq l (T_real.rzero ()))
              l (T_real.rzero ()) ) )
      else (name, (args, l))
    in
    let query_sub =
      Map.Poly.of_alist_exn @@ List.map postfp_templ_preds ~f:cert_of
    in
    let nonnegative_templ_preds =
      if max_cert then [] else postfp_templ_preds
    in
    let original_prefixpoint_constrs =
      List.map ~f:(Formula.subst_funcs prefp_sub)
      @@ List.concat_map ua_preds ~f:(fun pred ->
          List.concat_map (Term.elim_min_max_list pred.body) ~f:(fun body ->
              QFL.Problem.imply_antecedents (state_guard pred.name pred.args)
              @@ Formula.geq
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
          List.concat_map
            (Term.elim_min_max_list
            @@ Term.subst_funcs rank_sub ua_pred_delta.body)
            ~f:(fun body ->
              QFL.Problem.imply_antecedents (state_guard name rank_args)
              @@ Formula.leq
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
      | Some accel_problem when config.qfl.enable_geometric_pla ->
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
        (accel_problem, config.qfl.enable_geometric_pla, accelerated_rank_constrs)
      with
      | Some _, true, Some constrs -> constrs
      | Some _, true, None when rank_delta_is_trivial -> [ Formula.mk_false () ]
      | _ -> original_rank_constrs
    in
    let prefixpoint_constrs =
      match accel_problem with
      | Some accel_problem when config.qfl.enable_geometric_pla ->
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
        when config.qfl.enable_geometric_pla
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
      | Some _ when config.qfl.enable_geometric_pla ->
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
      List.concat_map templ_preds ~f:(fun (name, (args, quant_pred)) ->
          let pred =
            List.find_exn qfl_preds_for_templates ~f:(fun pred ->
                Stdlib.( = ) pred.name name)
          in
          QFL.Accel.template_nonnegative_formulas quant_pred
          |> List.concat_map
               ~f:
                 (QFL.Problem.imply_antecedents
                    (state_guard name args @ pred.arg_constrs)))
    in
    let constrs =
      List.concat templ_constrss
      @ (if config.qfl.templates.postfp_force_non_const then
           [
             Formula.or_of
               (List.map !coeffs ~f:(fun c -> Formula.neq c (T_real.rzero ())));
           ]
         else [])
      @ template_nonnegative_constrs
          (prefp_templ_preds @ rank_templ_preds @ nonnegative_templ_preds)
      @ unfolded_nonnegative_constrs @ body_at_zero_nonnegative_constrs
      @ List.concat_map postfp_templ_preds
          ~f:(fun (name, (postfp_args, postfp_body)) ->
            let prefp_args, prefp_body =
              List.Assoc.find_exn ~equal:Stdlib.( = ) prefp_templ_preds name
            in
            QFL.Problem.imply_antecedents (state_guard name postfp_args)
            @@ Formula.leq postfp_body
              (Term.rename
                 (LogicOld.ren_of_sort_env_list prefp_args postfp_args)
                 prefp_body))
      @ List.map ~f:(Formula.subst_funcs query_sub) query_fml
      @ postfixpoint_constrs @ prefixpoint_constrs @ ranking_constrs
    in
    let main, backup =
      match config.qfl.pareto_cache with
      | Cache_after { threshold; num_conds; cond_degree; zero_reward; _ }
        when (not max_cert) && List.length pareto_cache >= threshold ->
          (* not under [max_cert]: the cache reads post-fixpoints as
             non-negative everywhere *)
          let pc_constrs, pc_templ_params =
            gen_cache_constr ~num_conds ~cond_degree ~zero_reward
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
              PCSP.Problem.make ~prefix:(Some "q") (integrate_all pc_constrs)
              @@ pqe_envs_of (Map.force_merge templ_params pc_templ_params) ),
            Some
              ( ( Some ua_preds,
                  prefp_templ_preds,
                  rank_templ_preds,
                  postfp_templ_preds ),
                PCSP.Problem.make ~prefix:(Some "q") (integrate_all constrs)
                @@ pqe_envs_of templ_params ) )
      | _ ->
          ( ( ( Some ua_preds,
                prefp_templ_preds,
                rank_templ_preds,
                List.map postfp_templ_preds ~f:cert_of ),
              PCSP.Problem.make ~prefix:(Some "q") (integrate_all constrs)
              @@ pqe_envs_of templ_params ),
            None )
    in
    (main, backup)

  (* [state_guard] as in [cgen_pqes_lb], on the pre-fixpoint and template
     non-negativity obligations *)
  let cgen_pqes_ub ~templates (qfl : QFL.Problem.t) ?(state_guard = fun _ _ -> [])
      accel_problem query_fml fsub pareto_cache =
    let config = with_templates templates in
    let query_fml = Formula.elim_min_max_list query_fml in
    let qfl_preds_for_templates =
      if config.qfl.enable_geometric_pla then
        let active_names = QFL.Accel.active_pred_names accel_problem in
        List.filter qfl.preds ~f:(fun pred -> Set.mem active_names pred.name)
      else qfl.preds
    in
    let prefp_templ_paramss, prefp_templ_preds =
      List.unzip
      @@ List.map qfl_preds_for_templates ~f:(fun pred ->
          let template =
            Templ.gen_quant_template
              ~num_conds:config.qfl.templates.prefp.num_conds
              ~use_orig_ite:config.qfl.templates.prefp.use_orig_ite
              ~annot_branches_follow_ite:
                config.qfl.templates.prefp.annot_branches_follow_ite
              ~cond_branches_follow_ite:
                config.qfl.templates.prefp.cond_branches_follow_ite
              ~cond_degree:config.qfl.templates.prefp.cond_degree
              ~term_degree:config.qfl.templates.prefp.term_degree pred.args
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
      if config.qfl.enable_geometric_pla then
        QFL.Accel.body_nonnegative_formulas ~active_pred_names ~fsub
          accel_problem
      else []
    in
    let original_prefixpoint_constrs =
      List.map ~f:(Formula.subst_funcs prefp_sub)
      @@ List.concat_map qfl_preds_for_templates ~f:(fun pred ->
          List.concat_map (Term.elim_min_max_list pred.body) ~f:(fun body ->
              QFL.Problem.imply_antecedents (state_guard pred.name pred.args)
              @@ Formula.geq
                   (Term.fvar_app_of_senv pred.name pred.args T_real.SReal)
                   body))
    in
    let prefixpoint_constrs =
      if config.qfl.enable_geometric_pla then (
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
          let args, quant_pred = Map.Poly.find_exn prefp_sub pred.name in
          QFL.Accel.template_nonnegative_formulas quant_pred
          |> List.concat_map
               ~f:
                 (QFL.Problem.imply_antecedents
                    (state_guard pred.name args @ pred.arg_constrs)))
      @ unfolded_nonnegative_constrs @ pla_body_nonnegative_constrs
      @ List.map ~f:(Formula.subst_funcs prefp_sub) query_fml
      @ prefixpoint_constrs
    in
    let main, backup =
      match config.qfl.pareto_cache with
      | Cache_after { threshold; num_conds; cond_degree; zero_reward; _ }
        when List.length pareto_cache >= threshold ->
          let pc_constrs, pc_templ_params =
            gen_cache_constr ~num_conds ~cond_degree ~zero_reward
              (First prefp_sub) qfl.preds fsub pareto_cache
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
              PCSP.Problem.make (integrate_all pc_constrs)
              @@ pqe_envs_of (Map.force_merge templ_params pc_templ_params) ),
            Some
              ( (None, prefp_templ_preds, [], []),
                PCSP.Problem.make (integrate_all constrs)
                @@ pqe_envs_of templ_params ) )
      | _ ->
          ( ( (None, prefp_templ_preds, [], []),
              PCSP.Problem.make (integrate_all constrs)
              @@ pqe_envs_of templ_params ),
            None )
    in
    (main, backup)

  let div_ceil n d = if n % d = 0 then n / d else (n / d) + 1

  let solve_constrs templ_params constrs =
    let pqes =
      PCSP.Problem.make ~prefix:(Some "q") (integrate_all constrs) @@ pqe_envs_of templ_params
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
                    shp = config.qfl.templates.omega_regular.inv_shape;
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
              ~num_conds:config.qfl.templates.rank.num_conds
              ~use_orig_ite:config.qfl.templates.rank.use_orig_ite
              ~annot_branches_follow_ite:
                config.qfl.templates.rank.annot_branches_follow_ite
              ~cond_branches_follow_ite:
                config.qfl.templates.rank.cond_branches_follow_ite
              ~cond_degree:config.qfl.templates.rank.cond_degree
              ~term_degree:config.qfl.templates.rank.term_degree
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

  (** [eps_weight_of tsub eps] is the rational value that the solved model
      [tsub] gives the decrease weight [eps] of one predicate, or zero when that
      value is not a numeral.

      Assumes [eps] is a real-sorted template parameter of the last solved
      problem. The value is read after [Evaluator.simplify_term], because a
      template-based backend returns a parameter as an expression of its own
      template rather than as a literal: PCSat gives a nullary unknown as a
      selector over candidate terms, [case 0 [real(0)]], whose value is the
      selected branch. Without the simplification, reading that value as a
      literal raised an uncaught [Failure] and ended the run.

      Guarantees: [Q.gt (eps_weight_of tsub eps) Q.zero] only when the model
      gives [eps] that positive numeral. The fallback zero is the safe direction
      for every caller: the weight decides only whether a predicate counts as
      strictly ranked, which removes it from the predicates later steps must
      rank, and scales its ranking function; a predicate kept leaves the later
      problems as hard or harder, so the fallback can lose an answer but never
      makes one. *)
  let eps_weight_of tsub eps =
    match
      Evaluator.simplify_term @@ Term.subst tsub (Term.mk_var eps T_real.SReal)
    with
    | t when T_real.is_real t -> T_real.let_real t
    | t when T_int.is_int t -> Q.of_bigint (T_int.let_int t)
    | t ->
        Debug.print
        @@ lazy
             (sprintf "the weight %s is not a numeral in the model: %s"
                (Ident.name_of_tvar eps) (Term.str_of t));
        Q.zero

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
                            let eps = eps_weight_of tsub eps in
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
                        let eps = eps_weight_of tsub eps in
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
                            let eps = eps_weight_of tsub eps in
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
    (match config.qfl.templates.omega_regular.supermartingale with
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
      @ (if config.qfl.output_time then [ time ] else [])
      @ (match witness with
        | Some w when config.qfl.output_witness -> [ w ]
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

  (* Relaxing a QFL problem over integer-sorted states to one over the reals.

     The bound checker builds its certificates (pre- and post-fixpoint
     templates, ranking supermartingales) as polynomials over real-valued
     states, and the constraints it generates quantify over real states.  A
     problem whose functions take integer arguments (a pGCL [nat] variable, an
     SGCL variable that only ever holds integers) is therefore relaxed by
     [relax_to_reals] below, and by nothing else: every integer variable
     becomes a real one, and every integer operation its real counterpart.  This is sound in one direction only.

     - A certificate checked for every real state holds in particular for every
       integer state, so it proves the bound for the integer problem PROVIDED
       every operation maps integers to integers exactly as it does over the
       reals: addition, subtraction, negation, multiplication, absolute value, a
       power with a literal natural exponent, the comparisons and equality.
       Integer division and remainder do not ([x div 2] is not [x / 2]: a
       halving loop terminates on the integers and not on the reals), nor does a
       conversion from real to integer; a problem using one is not relaxed, and
       its query is answered [unknown] with the reason in the verbose trace.
     - A failure to find a certificate over the reals, or a real state violating
       the bound, says nothing about the integer problem, whose states are
       fewer.  The checker below answers [valid] or nothing ([unknown],
       [timeout]); it never refutes, so no refutation is drawn from a relaxed
       problem.

     A strict integer comparison [a < b] is rewritten to [a + 1 <= b] (and
     [a > b] to [a >= b + 1]) on the way: the two agree on every integer state,
     so the integer problem is unchanged, while the relaxed one no longer has
     to be certified on the real states strictly between [a] and [a + 1], which
     no integer state reaches.  A problem with no integer sort is returned
     unchanged. *)
  exception Not_relaxable of string

  let relax_sort = function T_int.SInt -> T_real.SReal | s -> s
  let relax_senv = List.map ~f:(fun (x, s) -> (x, relax_sort s))

  let rec relax_term = function
    | Term.Var (x, s, info) -> Term.mk_var ~info x (relax_sort s)
    | FunApp (T_int.Int n, [], info) -> T_real.mk_real ~info (Q.of_bigint n)
    | FunApp (T_int.Neg, [ t ], info) -> T_real.mk_rneg ~info (relax_term t)
    | FunApp (T_int.Abs, [ t ], info) -> T_real.mk_rabs ~info (relax_term t)
    | FunApp (T_int.Add, [ t1; t2 ], info) ->
        T_real.mk_radd ~info (relax_term t1) (relax_term t2)
    | FunApp (T_int.Sub, [ t1; t2 ], info) ->
        T_real.mk_rsub ~info (relax_term t1) (relax_term t2)
    | FunApp (T_int.Mul, [ t1; t2 ], info) ->
        T_real.mk_rmul ~info (relax_term t1) (relax_term t2)
    | FunApp (T_int.Power, [ t; FunApp (T_int.Int n, [], _) ], _)
      when Z.(geq n zero) && Z.fits_int n ->
        let t = relax_term t in
        List.fold (List.init (Z.to_int n) ~f:(fun _ -> t))
          ~init:(T_real.rone ()) ~f:T_real.mk_rmul
    | FunApp (T_int.Div _, _, _) ->
        raise (Not_relaxable "integer division is not real division")
    | FunApp (T_int.Rem _, _, _) ->
        raise (Not_relaxable "integer remainder has no real counterpart")
    | FunApp (T_irb.IntToReal, [ t ], _) -> relax_term t
    | FunApp
        ( (( T_real.(Real _ | RNeg | RAbs | RAdd | RSub | RMul | RDiv | RPower)
           | T_bool.IfThenElse ) as sym),
          ts,
          info ) ->
        Term.mk_fsym_app ~info sym (List.map ts ~f:relax_term)
    | FunApp (FVar (f, sargs, sret), ts, info) ->
        Term.mk_fsym_app ~info
          (FVar (f, List.map sargs ~f:relax_sort, relax_sort sret))
          (List.map ts ~f:relax_term)
    | FunApp (T_bool.Formula phi, [], info) ->
        Term.mk_fsym_app ~info (T_bool.Formula (relax_formula phi)) []
    | LetTerm (x, s, t1, t2, info) ->
        Term.mk_let_term ~info x (relax_sort s) (relax_term t1) (relax_term t2)
    | FunApp (sym, _, _) ->
        raise
          (Not_relaxable
             (sprintf "the operation %s is not known to agree on the integers \
                       and the reals"
                (Term.str_of_funsym sym)))

  and relax_atom = function
    | (Atom.True _ | Atom.False _) as atom -> atom
    | Atom.App (Predicate.Psym T_int.Lt, [ t1; t2 ], info) ->
        Atom.mk_app ~info (Predicate.Psym T_real.RLeq)
          [ T_real.mk_radd (relax_term t1) (T_real.rone ()); relax_term t2 ]
    | Atom.App (Predicate.Psym T_int.Gt, [ t1; t2 ], info) ->
        Atom.mk_app ~info (Predicate.Psym T_real.RGeq)
          [ relax_term t1; T_real.mk_radd (relax_term t2) (T_real.rone ()) ]
    | Atom.App (Predicate.Psym T_int.Leq, ts, info) ->
        Atom.mk_app ~info (Predicate.Psym T_real.RLeq)
          (List.map ts ~f:relax_term)
    | Atom.App (Predicate.Psym T_int.Geq, ts, info) ->
        Atom.mk_app ~info (Predicate.Psym T_real.RGeq)
          (List.map ts ~f:relax_term)
    | Atom.App
        ( (Predicate.Psym
             (T_bool.Eq | T_bool.Neq | T_real.(RLeq | RGeq | RLt | RGt)) as
           pred),
          ts,
          info ) ->
        Atom.mk_app ~info pred (List.map ts ~f:relax_term)
    | Atom.App (Predicate.Var (p, sorts), ts, info) ->
        Atom.mk_app ~info
          (Predicate.Var (p, List.map sorts ~f:relax_sort))
          (List.map ts ~f:relax_term)
    | Atom.App (pred, _, _) ->
        raise
          (Not_relaxable
             (sprintf "the predicate %s is not known to agree on the integers \
                       and the reals"
                (Predicate.str_of pred)))

  and relax_formula = function
    | Formula.Atom (atom, info) -> Formula.mk_atom ~info (relax_atom atom)
    | UnaryOp (op, phi, info) -> Formula.mk_unop ~info op (relax_formula phi)
    | BinaryOp (op, phi1, phi2, info) ->
        Formula.mk_binop ~info op (relax_formula phi1) (relax_formula phi2)
    | Bind (binder, senv, phi, info) ->
        Formula.mk_bind ~info binder (relax_senv senv) (relax_formula phi)
    | LetFormula (x, s, t, phi, info) ->
        Formula.mk_let_formula ~info x (relax_sort s) (relax_term t)
          (relax_formula phi)
    | LetRec _ ->
        raise (Not_relaxable "a fixpoint formula inside a QFL body")

  (* whether an integer sort occurs anywhere: a variable, a binder, a function's
     signature, an integer operation or comparison, or a conversion *)
  let rec int_in_term = function
    | Term.Var (_, s, _) -> Term.is_int_sort s
    | FunApp (sym, ts, _) -> int_in_fun_sym sym || List.exists ts ~f:int_in_term
    | LetTerm (_, s, t1, t2, _) ->
        Term.is_int_sort s || int_in_term t1 || int_in_term t2

  and int_in_fun_sym = function
    | T_int.(Int _ | Neg | Nop | Abs | Add | Sub | Mul | Div _ | Rem _ | Power)
    | T_int.Case _
    | T_irb.(IntToReal | RealToInt | IntToBV _ | BVToInt _) ->
        true
    | FVar (_, sargs, sret) -> List.exists (sret :: sargs) ~f:Term.is_int_sort
    | T_bool.Formula phi -> int_in_formula phi
    | _ -> false

  and int_in_formula = function
    | Formula.Atom (Atom.App (Predicate.Psym T_int.(Leq | Geq | Lt | Gt), _, _), _)
    | Formula.Atom (Atom.App (Predicate.Psym T_int.(PDiv | NotPDiv), _, _), _) ->
        true
    | Formula.Atom (Atom.App (Predicate.Var (_, sorts), ts, _), _) ->
        List.exists sorts ~f:Term.is_int_sort || List.exists ts ~f:int_in_term
    | Formula.Atom (Atom.App (_, ts, _), _) -> List.exists ts ~f:int_in_term
    | Formula.Atom ((Atom.True _ | Atom.False _), _) -> false
    | UnaryOp (_, phi, _) -> int_in_formula phi
    | BinaryOp (_, phi1, phi2, _) -> int_in_formula phi1 || int_in_formula phi2
    | Bind (_, senv, phi, _) ->
        List.exists senv ~f:(snd >> Term.is_int_sort) || int_in_formula phi
    | LetFormula (_, s, t, phi, _) ->
        Term.is_int_sort s || int_in_term t || int_in_formula phi
    | LetRec _ -> true

  let mentions_int (qfl : QFL.Problem.t) =
    let is_int (_, s) = Term.is_int_sort s in
    let in_term = int_in_term in
    let in_formula = int_in_formula in
    List.exists qfl.preds ~f:(fun (pred : QFL.Pred.t) ->
        List.exists pred.args ~f:is_int
        || in_term pred.body
        || List.exists (pred.annots @ pred.arg_constrs) ~f:in_formula)
    ||
    match qfl.query with
    | Check q ->
        List.exists q.params ~f:is_int
        || List.exists (q.bound :: q.args) ~f:in_term
        || Option.exists q.left ~f:in_formula
    | DistCheck q ->
        List.exists q.params ~f:is_int
        || List.exists q.args ~f:in_term
        || in_formula q.bound
    | ASAT (init, senv, phi) ->
        List.exists senv ~f:is_int
        || in_formula phi
        || Option.exists init ~f:(fun (_, ts) -> List.exists ts ~f:in_term)

  (* [relax_to_reals qfl query] is [Ok] of the relaxed problem and query, the
     input itself when it has no integer sort, or [Error] of the reason the
     relaxation would not be sound; see the comment above [Not_relaxable] *)
  let relax_to_reals (qfl : QFL.Problem.t) (query : QFL.Problem.check) =
    if not (mentions_int qfl) then Ok (qfl, query)
    else
      try
        let preds =
          List.map qfl.preds ~f:(fun (pred : QFL.Pred.t) ->
              {
                pred with
                args = relax_senv pred.args;
                body = relax_term pred.body;
                annots = List.map pred.annots ~f:relax_formula;
                arg_constrs = List.map pred.arg_constrs ~f:relax_formula;
              })
        in
        let query =
          QFL.Problem.
            {
              query with
              params = relax_senv query.params;
              left = Option.map query.left ~f:relax_formula;
              args = List.map query.args ~f:relax_term;
              bound = relax_term query.bound;
            }
        in
        let qfl = QFL.Problem.{ preds; query = Check query } in
        Debug.print ~id:None
        @@ lazy
             (sprintf "relaxed from the integers to the reals: %s\n"
             @@ QFL.Problem.str_of qfl);
        Ok (qfl, query)
      with Not_relaxable reason -> Error reason

  (* Reading a relaxed problem at its integer states only.

     [integer_states qfl query], on the problem BEFORE [relax_to_reals], is
     [Some (positions, params)] when [config.qfl.integer_states] is on and
     some function argument is integral or some query parameter is
     integer-sorted: [positions] gives, per function, the indices of its
     integral arguments ([integral_positions]: the integer-sorted ones, and
     the real ones that hold an integer at every state the query reaches), and
     [params] the query's integer parameters; otherwise [None], and the
     checker states every obligation at every real state as before.

     Why this is sound.  Let [I] be the set of states whose arguments at
     [positions] are integers.  The relaxed problem agrees with the input at
     every state of [I] (the contract of [relax_to_reals]), the query's state
     is in [I], and a state of [I] applies the functions only at states of
     [I] (the guarantee of [integral_positions]).  So on [I] the least
     fixpoint is that of the equations restricted to [I] -- each value at a
     state of [I] depends only on values at states of [I] -- and the query
     reads it only there.  Park induction for an upper bound and the
     post-fixpoint-with-ranking rule for a lower bound hold over any state
     space, so their obligations need to hold on [I] only, and each
     obligation of a function is stated under [is_int] of its integral
     arguments ([integer_state_guard]).  An obligation left without the
     hypothesis (the acceleration's, the Pareto cache's, the unfolded
     functions' non-negativity) is only stronger.

     Why it can matter.  On the reals the value of [X x =mu if x >= 1 then 1 +
     X (x - 1) else 0] is [floor x] (for [x >= 0]), so no linear post-fixpoint
     valid at every real state exceeds [x - 1], and [X 3 >= 3] cannot be
     proved; at the integer states the post-fixpoint [x] proves it. *)
  (* [integral ints t]: [t] is integer-valued whenever every variable of [ints]
     is, judged by its shape: an integer-sorted term, an integral real
     literal, a variable of [ints], a sum, difference, product or negation of
     such, or a conditional whose two branches are such *)
  let rec integral ints t =
    Term.is_int_sort (Term.sort_of t)
    ||
    match t with
    | Term.Var (x, _, _) -> Set.mem ints x
    | FunApp (T_real.Real q, [], _) -> Z.equal (Q.den q) Z.one
    | FunApp (T_irb.IntToReal, [ _ ], _) -> true
    | FunApp (T_real.(RAdd | RSub | RMul), [ t1; t2 ], _) ->
        integral ints t1 && integral ints t2
    | FunApp (T_real.RNeg, [ t1 ], _) -> integral ints t1
    | FunApp (T_bool.IfThenElse, [ _; t1; t2 ], _) ->
        integral ints t1 && integral ints t2
    | _ -> false

  (* [binder_free t]: [t] binds no variable (no [let], no quantifier, no
     integral binder, no symbol other than arithmetic, conditionals and
     function applications), so a variable occurring in an argument of an
     application in [t] is the enclosing equation's parameter of that name *)
  let rec binder_free = function
    | Term.Var _ -> true
    | LetTerm _ -> false
    | FunApp (sym, ts, _) ->
        (match sym with
        | T_real.(Real _ | RAdd | RSub | RMul | RNeg | RDiv)
        | T_int.(Int _ | Add | Sub | Mul | Neg)
        | T_irb.IntToReal | T_bool.IfThenElse | FVar _ ->
            true
        | T_bool.Formula phi -> binder_free_formula phi
        | _ -> false)
        && List.for_all ts ~f:binder_free

  and binder_free_formula = function
    | Formula.Atom ((Atom.True _ | Atom.False _), _) -> true
    | Atom (Atom.App (Predicate.Psym _, ts, _), _) ->
        List.for_all ts ~f:binder_free
    | UnaryOp (_, phi, _) -> binder_free_formula phi
    | BinaryOp (_, phi1, phi2, _) ->
        binder_free_formula phi1 && binder_free_formula phi2
    | _ -> false

  (* [integral_positions qfl query]: per function, its arity and the indices
     of the arguments that are integers at every state the query reaches:
     every integer-sorted argument, and every real-sorted one for which the
     query's argument is integral and so is the argument of every application
     of the function, given the integral arguments of the equation it occurs
     in.  Computed as a greatest fixpoint: start from every argument and drop
     one whose application is not shown integral, until nothing changes.  A
     real argument applied inside a body that binds variables is dropped.
     Guarantees: the set of states whose arguments at these positions are
     integers contains the query's state and is closed under the
     applications of every body. *)
  let integral_positions (qfl : QFL.Problem.t) (query : QFL.Problem.check) =
    let cand = Hashtbl.Poly.create () in
    List.iter qfl.preds ~f:(fun (pred : QFL.Pred.t) ->
        Hashtbl.set cand ~key:pred.name
          ~data:(Array.of_list_map pred.args ~f:(fun _ -> true)));
    let drop ~ints name ts =
      match Hashtbl.find cand name with
      | Some a when Array.length a = List.length ts ->
          List.foldi ts ~init:false ~f:(fun i changed t ->
              if a.(i) && not (integral ints t) then (
                a.(i) <- false;
                true)
              else changed)
      | Some a ->
          let changed = Array.exists a ~f:Fn.id in
          Array.fill a ~pos:0 ~len:(Array.length a) false;
          changed
      | None -> false
    in
    let query_ints =
      Set.Poly.of_list
      @@ List.filter_map query.params ~f:(fun (x, s) ->
          if Term.is_int_sort s then Some x else None)
    in
    ignore (drop ~ints:query_ints query.name query.args : bool);
    let rec loop () =
      let changed =
        List.fold qfl.preds ~init:false ~f:(fun changed (pred : QFL.Pred.t) ->
            let ints =
              let a = Hashtbl.find_exn cand pred.name in
              Set.Poly.of_list
              @@ List.filter_mapi pred.args ~f:(fun i (x, s) ->
                  if a.(i) || Term.is_int_sort s then Some x else None)
            in
            let ints =
              if binder_free pred.body then ints
              else Set.Poly.empty
            in
            Set.fold (Term.fvar_apps_of pred.body) ~init:changed
              ~f:(fun changed -> function
              | Term.FunApp (FVar (name, _, _), ts, _) ->
                  drop ~ints name ts || changed
              | _ -> changed))
      in
      if changed then loop ()
    in
    loop ();
    List.filter_map qfl.preds ~f:(fun (pred : QFL.Pred.t) ->
        let a = Hashtbl.find_exn cand pred.name in
        match
          List.filter_mapi pred.args ~f:(fun i (_, s) ->
              if a.(i) || Term.is_int_sort s then Some i else None)
        with
        | [] -> None
        | is -> Some (pred.name, (List.length pred.args, is)))

  let integer_states (qfl : QFL.Problem.t) (query : QFL.Problem.check) =
    if not config.qfl.integer_states then None
    else
      let positions = integral_positions qfl query in
      let params =
        List.filter_map query.params ~f:(fun (x, s) ->
            if Term.is_int_sort s then Some x else None)
      in
      if List.is_empty positions && List.is_empty params then None
      else Some (positions, params)

  (* [integer_state_guard positions name args]: [is_int] of each argument of
     [args] at an integer position of the function [name] *)
  let integer_state_guard positions name args =
    match List.Assoc.find positions ~equal:Ident.tvar_equal name with
    | Some (arity, is) when List.length args = arity ->
        List.map is ~f:(fun i ->
            let x, s = List.nth_exn args i in
            Formula.mk_atom @@ T_irb.mk_is_int @@ Term.mk_var x s)
    | _ -> []

  (* [refuse_unsound_query_shape ~fsub ~recursive query] refuses, through
     [Common.Refusal], a bound query whose certificate below would not be one,
     and returns [()] otherwise.

     The checker certifies [F args ⋈ bound] by replacing EVERY recursive
     function [G] (a predicate [unfold] keeps) by a template of the query's
     direction: a pre-fixpoint [P_G >= lfp G] for an upper bound, a
     post-fixpoint [Q_G <= lfp G] for a lower one.  That proves the query only
     if the query is monotone in the replaced applications in the direction
     that makes the approximation safe, so the contract, read after inlining
     [fsub] into the query, is:
     - [bound], [args] and the antecedent [left] apply no recursive function:
       there the approximation goes the wrong way round (for [F 1 <= G 1] the
       pre-fixpoint [P_G] over-approximates [G], and [F 1 <= P_G 1] says
       nothing about [F 1 <= G 1]: with [F x = 1] and [G x =mu 0.5 * G x],
       least fixpoint 0, the template [P_G = 1] satisfies every constraint and
       the false bound was answered valid);
     - the head [F args], once inlined, is nondecreasing in every recursive
       application it contains, seen per branch of its conditionals (whose
       conditions must be free of them): a branch is built from them by sums,
       products with and divisions by a factor free of them that is not a
       negative constant, and a subtraction of a term free of them, or it is
       a combination of them whose constant coefficients, equal applications
       summed, are all nonnegative ([1 - G x <= b] is a lower bound on [G],
       again the wrong direction).
     A comparison between two fixpoints needs the two sides approximated in
     opposite directions in one certificate, which this checker does not
     build.

     The same test is applied to the body of every recursive equation in
     [preds] (already inlined by [unfold]): Park induction -- a pre-fixpoint
     [P >= Phi(P)] bounds [lfp Phi] from above (Knaster-Tarski) -- and the
     post-fixpoint-with-ranking argument for lower bounds both need [Phi]
     monotone, and the templates do not check it.  Without the test the
     equation [X x =mu if x > 0 then 1 - X (x - 1) else 0], whose solution has
     [X 1 = 1], admitted the pre-fixpoint [X = 1/2] ([1/2 >= 1 - 1/2],
     [1/2 >= 0]), and the false bound [X 1 <= 1/2] was answered valid.  A
     factor mentioning a variable is assumed nonnegative here as in the head:
     that assumption is the program's obligation and is not checked. *)
  let refuse_unsound_query_shape ~fsub ~recursive ~(preds : QFL.Pred.t list)
      (query : QFL.Problem.check) =
    let applied t =
      Set.Poly.filter_map (Term.fvar_apps_of t) ~f:(function
        | Term.FunApp (FVar (name, _, _), _, _) when Set.mem recursive name ->
            Some name
        | _ -> None)
    in
    let free t = Set.is_empty (applied t) in
    let constant t =
      if free t && Set.is_empty (Term.tvs_of t) then
        match Evaluator.simplify_term t with
        | t when T_real.is_real t -> Some (T_real.let_real t)
        | t when T_int.is_int t -> Some (Q.of_bigint (T_int.let_int t))
        | _ -> None
      else None
    in
    (* a factor free of recursive functions that is not a negative constant;
       one that mentions a variable is taken to be nonnegative, the same
       obligation every recursive body already carries (a choice weight [p] in
       [p * G x + (1 - p) * G y] is a probability by the program's contract) *)
    let factor t =
      free t
      && ((not (Set.is_empty (Term.tvs_of t)))
         || Option.exists (constant t) ~f:(fun c -> Q.(geq c zero)))
    in
    (* [linear t]: [t] as a combination of recursive applications with
       constant coefficients, each application keyed by its printed form so
       that equal applications are summed, plus a part free of them; [None]
       when [t] is not of that shape.  A head normalised to
       [G a + G b * 1/2 - G a * 1/2] is nondecreasing although it subtracts
       an application: the coefficient of [G a] is [1/2]. *)
    let rec linear t =
      let scale c = Map.Poly.map ~f:(fun d -> Q.(c * d)) in
      let sum m1 m2 =
        Map.Poly.merge m1 m2 ~f:(fun ~key:_ -> function
          | `Both (c, d) -> Some Q.(c + d)
          | `Left c | `Right c -> Some c)
      in
      if free t then Some Map.Poly.empty
      else
        match t with
        | Term.FunApp (FVar (name, _, _), args, _)
          when Set.mem recursive name && List.for_all args ~f:free ->
            Some (Map.Poly.singleton (Term.str_of t) Q.one)
        | Term.FunApp ((T_real.RAdd | T_int.Add | T_num.NAdd _), [ t1; t2 ], _)
          ->
            Option.map2 (linear t1) (linear t2) ~f:sum
        | Term.FunApp ((T_real.RSub | T_int.Sub | T_num.NSub _), [ t1; t2 ], _)
          ->
            Option.map2 (linear t1) (linear t2) ~f:(fun m1 m2 ->
                sum m1 (scale Q.minus_one m2))
        | Term.FunApp ((T_real.RNeg | T_int.Neg | T_num.NNeg _), [ t1 ], _) ->
            Option.map (linear t1) ~f:(scale Q.minus_one)
        | Term.FunApp ((T_real.RMul | T_int.Mul | T_num.NMul _), [ t1; t2 ], _)
          -> (
            match (constant t1, constant t2) with
            | Some c, _ -> Option.map (linear t2) ~f:(scale c)
            | _, Some c -> Option.map (linear t1) ~f:(scale c)
            | None, None -> None)
        | Term.FunApp ((T_real.RDiv | T_num.NDiv _), [ t1; t2 ], _) -> (
            match constant t2 with
            | Some c when not (Q.equal c Q.zero) ->
                Option.map (linear t1) ~f:(scale Q.(one / c))
            | _ -> None)
        | _ -> None
    in
    let rec monotone t =
      free t
      ||
      match QFL.Unif.let_unif t with
      | Some (_, body) ->
          (* the integral is monotone in its integrand *)
          monotone body
      | None -> (
      match t with
      | Term.FunApp (FVar (name, _, _), args, _) when Set.mem recursive name ->
          List.for_all args ~f:free
      | Term.FunApp ((T_real.RAdd | T_int.Add | T_num.NAdd _), [ t1; t2 ], _) ->
          monotone t1 && monotone t2
      | Term.FunApp ((T_real.RSub | T_int.Sub | T_num.NSub _), [ t1; t2 ], _) ->
          monotone t1 && free t2
      | Term.FunApp ((T_real.RMul | T_int.Mul | T_num.NMul _), [ t1; t2 ], _) ->
          (factor t1 && monotone t2) || (factor t2 && monotone t1)
      | Term.FunApp ((T_real.RDiv | T_num.NDiv _), [ t1; t2 ], _) ->
          monotone t1 && factor t2
      | Term.FunApp (T_bool.IfThenElse, [ c; t1; t2 ], _) ->
          free c && monotone t1 && monotone t2
      | _ -> false)
    in
    let head =
      Term.subst_funcs fsub
      @@ Term.mk_fvar_app query.name
           (List.map query.args ~f:(Fn.const T_real.SReal))
           T_real.SReal query.args
    in
    let wrong_side =
      Set.Poly.union_list
      @@ List.map ~f:(Term.subst_funcs fsub >> applied)
      @@ (query.bound :: query.args)
      @ Option.to_list (Option.map query.left ~f:T_bool.of_formula)
    in
    match Set.min_elt wrong_side with
    | Some name ->
        Common.Refusal.refuse
          "the bound or the antecedent of the query applies %s, a recursive \
           function: the bound checker approximates every recursive function \
           in the direction of the query, so a comparison between two \
           fixpoints is not certified soundly"
          (Ident.name_of_tvar name)
    | None ->
        let nondecreasing t =
          monotone t
          || Option.exists (linear t)
               ~f:(Map.for_all ~f:(fun c -> Q.(geq c zero)))
        in
        let seen_nondecreasing t =
          List.for_all (Term.elim_min_max_list t) ~f:(fun t ->
              List.for_all (Term.elim_ite t) ~f:(fun (cond, t) ->
                  free (T_bool.of_formula cond) && nondecreasing t))
        in
        if not (seen_nondecreasing head) then
          Common.Refusal.refuse
            "the query's function, once its non-recursive definition is \
             inlined, is not seen to be nondecreasing in the recursive \
             functions it applies (%s), so approximating them in the direction \
             of the query does not bound it in that direction"
            (Term.str_of head);
        List.iter preds ~f:(fun (pred : QFL.Pred.t) ->
            if not (seen_nondecreasing pred.body) then
              Common.Refusal.refuse
                "the body of %s is not seen to be nondecreasing in the \
                 recursive functions it applies (%s): the bound checker's \
                 certificates (a pre-fixpoint for an upper bound, a \
                 post-fixpoint with a ranking function for a lower one) bound \
                 a least fixpoint only of a monotone equation"
                (Ident.name_of_tvar pred.name)
                (Term.str_of pred.body))

  (* whether an integral [unif r. F] occurs in the equations or the query *)
  let mentions_unif (qfl : QFL.Problem.t) =
    List.exists qfl.preds ~f:(fun (pred : QFL.Pred.t) ->
        QFL.Unif.term_mentions pred.body
        || List.exists (pred.annots @ pred.arg_constrs)
             ~f:QFL.Unif.formula_mentions)
    ||
    match qfl.query with
    | Check q ->
        List.exists (q.bound :: q.args) ~f:QFL.Unif.term_mentions
        || Option.exists q.left ~f:QFL.Unif.formula_mentions
    | DistCheck q ->
        List.exists q.args ~f:QFL.Unif.term_mentions
        || QFL.Unif.formula_mentions q.bound
    | ASAT (init, _, phi) ->
        QFL.Unif.formula_mentions phi
        || Option.exists init ~f:(fun (_, ts) ->
               List.exists ts ~f:QFL.Unif.term_mentions)

  (* [?int_states]: [integer_states] of the problem as read, for a caller
     that relaxed it already; absent, it is computed here from [qfl] *)
  let rec check_bounds ~print_sol ?int_states (i, sols, pareto_cache) qfl
      (query : QFL.Problem.check) =
    let int_states =
      match int_states with
      | Some int_states -> int_states
      | None -> integer_states qfl query
    in
    match relax_to_reals qfl query with
    | Ok (qfl', query') ->
        check_bounds_over_reals ~print_sol ~int_states
          (i, sols, pareto_cache) qfl' query'
    | Error reason ->
        Debug.print ~id:None
        @@ lazy
             (sprintf
                "[8. Solver result]\n\
                 result: unknown\n\
                 reason: the problem is over the integers and cannot be \
                 relaxed to the reals soundly: %s"
                reason);
        print_query_verdict ~print_sol ~top_level:(i >= 0)
          ~weakened:(weakened_by_earlier sols) Verdict.Unknown "0.000000s";
        Or_error.return (sols @ [ Verdict.Unknown ], pareto_cache @ [ None ])

  and check_bounds_over_reals ~print_sol ~int_states (i, sols, pareto_cache)
      qfl (query : QFL.Problem.check) =
    Timer.start ();
    let state_guard, query =
      match int_states with
      | None -> ((fun _ _ -> []), query)
      | Some (positions, params) ->
          (* a quantified integer parameter of the query ranges over the
             integers: [is_int] of it joins the query's antecedent *)
          let param_guards =
            List.filter_map query.params ~f:(fun (x, s) ->
                if List.mem params x ~equal:Ident.tvar_equal then
                  Some (Formula.mk_atom @@ T_irb.mk_is_int @@ Term.mk_var x s)
                else None)
          in
          ( integer_state_guard positions,
            if List.is_empty param_guards then query
            else
              {
                query with
                left =
                  Some
                    (Formula.and_of
                       (param_guards @ Option.to_list query.left));
              } )
    in
    (* a refusal of the input, not an internal error: the bound checking below
       is built for least fixpoints only *)
    if not @@ QFL.Problem.has_only_mu qfl then
      Common.Refusal.refuse
        "the QFL bound checker handles least fixpoints (=mu) only, and this \
         problem defines a greatest fixpoint (=nu)";
    let qfl_before_unfold = qfl in
    let has_unif = mentions_unif qfl in
    let templates = templates_for ~has_unif in
    if has_unif && config.qfl.enable_geometric_pla then
      Common.Refusal.refuse
        "the geometric PLA acceleration does not read integrals (unif); run \
         without enable_geometric_pla";
    let accel_problem = QFL.Accel.accelerate_applicable qfl_before_unfold in
    let fsub, qfl = QFL.Problem.unfold qfl_before_unfold in
    let fsub, qfl =
      if not has_unif then (fsub, qfl)
      else
        let unknowns = Set.Poly.of_list @@ QFL.Pred.pvars_of_list qfl.preds in
        let rewrite = QFL.Unif.rewrite_min_max ~unknowns in
        ( Map.Poly.map fsub ~f:(fun (args, body) -> (args, rewrite body)),
          {
            qfl with
            preds =
              List.map qfl.preds ~f:(fun (pred : QFL.Pred.t) ->
                  { pred with body = rewrite pred.body });
          } )
    in
    refuse_unsound_query_shape ~fsub
      ~recursive:(Set.Poly.of_list @@ QFL.Pred.pvars_of_list qfl.preds)
      ~preds:qfl.preds query;
    Debug.print ~id:None
    @@ lazy (sprintf "inlined: %s\n" @@ QFL.Problem.str_of ~fsub:(Some fsub) qfl);
    let ((ua_preds, prefp, rank, postfp), pqes), backup =
      let query_fml =
        Formula.subst_funcs fsub @@ QFL.Problem.formula_of_query (Check query)
      in
      match query.kind with
      | LB -> (
          match
            if config.qfl.enable_geometric_pla then
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
              cgen_pqes_lb ~templates qfl ~preds_for_fsub_domain query_fml fsub
                pareto_cache
          | None ->
              Debug.print ~id:None
              @@ lazy
                   (if config.qfl.enable_geometric_pla then
                      "geometric PLA lower-bound acceleration fallback: exact \
                       accelerated QFL body not available"
                    else "geometric PLA lower-bound acceleration disabled");
              let state_guard, max_cert =
                if
                  (not config.qfl.lb_max_on_invariant)
                  || config.qfl.enable_geometric_pla
                then (state_guard, false)
                else
                  let is_valid phi =
                    try
                      Z3Smt.Z3interface.is_valid ~id:None
                        ~timeout:(Some 5000) (LogicOld.get_fenv ()) phi
                    with exn_ when not (Timer.is_async exn_) -> false
                  in
                  let head =
                    Term.subst_funcs fsub
                    @@ Term.mk_fvar_app query.name
                         (List.map query.args ~f:(Fn.const T_real.SReal))
                         T_real.SReal query.args
                  in
                  match
                    QflReachInv.compute ~is_valid ~preds:qfl.preds
                      ~query_params:query.params ~query_left:query.left head
                  with
                  | Some (inv, descr) ->
                      Debug.print ~id:None
                      @@ lazy (sprintf "reachable-state invariant: %s" descr);
                      ( (fun name args -> state_guard name args @ inv name args),
                        true )
                  | None ->
                      Debug.print ~id:None
                      @@ lazy "reachable-state invariant: none proved";
                      (state_guard, true)
              in
              cgen_pqes_lb ~templates qfl ~state_guard ~max_cert
                ?accel_problem:
                  (if config.qfl.enable_geometric_pla then Some accel_problem
                   else None)
                ~preds_for_fsub_domain:qfl_before_unfold.preds query_fml fsub
                pareto_cache)
      | UB ->
          cgen_pqes_ub ~templates qfl ~state_guard accel_problem query_fml fsub
            pareto_cache
    in
    let timeout =
      (* a backup problem is built only by the Pareto cache *)
      match (backup, config.qfl.pareto_cache) with
      | Some _, Cache_after { timeout; _ } -> timeout
      | _ -> None
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
            @ [
                (match backup with
                | None when not config.qfl.lb_max_on_invariant -> Some fp
                | _ ->
                    (* a [lb_max_on_invariant] certificate bounds the solution
                       only on the reachable-state invariant of its query *)
                    None);
              ] )
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
          if config.qfl.dist_bound.initialize_standard_basis then
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
              [ (Q.one, config.qfl.dist_bound.use_strict_bound) ] )
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
                  if config.qfl.dist_bound.use_l1_norm then T_real.mk_rsub
                  else fun ?(info = Dummy) p q ->
                    let d = T_real.mk_rsub p q in
                    T_real.mk_rmul ~info d d
                in
                T_real.mk_rsum (T_real.rzero ()) (List.map2_exn ps qs ~f)
              in
              let fenv = Map.Poly.empty in
              Timer.start ();
              match
                if config.qfl.dist_bound.use_optimathsat then
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
                      if config.qfl.dist_bound.use_l1_norm then Q.one
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
                      match config.qfl.dist_bound.relax with
                      | None -> [ (bound, config.qfl.dist_bound.use_strict_bound) ]
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
                            (bound, config.qfl.dist_bound.use_strict_bound);
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
                  (* No optimum was found for this generator: the optimiser
                     left the question undecided (under the run's budget, or
                     a solver's own unknown), or the constraints have no
                     model.  Skipping the generator would be unsound: a
                     refinement that skips every counterexample generator
                     ends with [eps = 0], which this loop reads as the
                     bound holding.  So the distance check is unsettled,
                     which the caller reports as [unknown]. *)
                  opt_time := !opt_time +. Timer.stop ();
                  Debug.print ~id:None
                  @@ lazy
                       "the optimiser found no closest point for a \
                        counterexample generator; the distance check is \
                        unsettled";
                  raise Dist_check_unsettled))
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

  (* [refuse_ill_formed qfl query] refuses, through [Common.Refusal], a bound
     query outside the quantitative fixpoint logic of Kura, Unno and Tsukada,
     "Supermartingales for Unique Fixed Points: A Unified Approach to Lower
     Bound Verification" (PLDI 2026), and returns [()] otherwise.  There the
     values are [[0, inf]] and a body is
       F ::= X(e) | t | F1 + F2 | t * F | if phi then F1 else F2
     with [t] a non-negative real term; an expectation of mixed sign is not
     an input but two (its positive and negative parts, split before the
     query is written).  Every certificate below reads its input that way:
     the lower-bound under-approximation replaces a body by [0] where a guard
     template is negative, which is below the body only where the body is
     non-negative, and the ranking argument uses [lfp >= 0].  The equation
     [X =mu -1 + 0.5 * X] (real solution [-2]) was answered valid on the
     query [X >= 0] with every template [0].

     The check, per equation and per query:
     - a body is decomposed by the grammar, with [t / c] read as [(1/c) * F]
       (so [c > 0] is required), [min] and [max] read as their arguments, and
       [if phi then ... else ...] adding [phi] or its negation to the guards;
       anything else applying an unknown (a subtraction or a negation of one,
       a product of two, an unknown in a condition) is refused as outside the
       grammar;
     - every maximal subterm [t] free of unknowns (a divisor: [t > 0]; the
       query's bound: under its antecedent [left]) is judged in two
       strengths, where the guards are the enclosing conditions and the
       equation's argument constraints:
       (1) refused when [guards /\ t >= 0] has no model, i.e. [t] is negative
           at every state satisfying the guards (a closed negative [t] under
           no guard, such as [-1] in [X =mu -1 + 0.5 * X], is refused without
           asking);
       (2) accepted with a note on stderr, once per equation naming its
           terms, when [t] may be negative at some such state (or the
           question is undecided within 10 s): [guards => t >= 0] is not
           shown valid, but some state makes [t] non-negative.
       A [t] for which [guards => t >= 0] is valid (a closed one by
       evaluation) is accepted silently.
     CONTRACT.  When this returns [()], every body is in the grammar above
     and every term in it is non-negative at some state satisfying its
     guards; it is NOT established that each is non-negative at every such
     state.  A verdict on an input accepted under (2) ASSUMES that every term
     named in the note is non-negative at every state reachable from the
     query, which is what the certificates rely on (the under-approximation
     and [lfp >= 0] above); nothing checks it.  Requiring it at every
     guard-satisfying state, as the paper's semantics does, refused 58
     shipped inputs whose term (a counter or a coordinate returned at
     termination, a reward [1/2 * b]) carries no sign guard and is never
     negative on a reachable state.  The check runs on the input as written,
     before the integers are relaxed to the reals, so an integer variable is
     read as one. *)
  let refuse_ill_formed (qfl : QFL.Problem.t) (query : QFL.Problem.check) =
    let unknowns = Set.Poly.of_list @@ QFL.Pred.pvars_of_list qfl.preds in
    (* a nullary unknown is read as a term variable, any other as an
       application of a function variable *)
    let free t =
      Set.for_all (Term.tvs_of t) ~f:(Fn.non (Set.mem unknowns))
      && Set.for_all (Term.fvar_apps_of t) ~f:(function
           | Term.FunApp (FVar (name, _, _), _, _) ->
               not (Set.mem unknowns name)
           | _ -> true)
    in
    let zero_of t =
      if Stdlib.( = ) (Term.sort_of t) T_int.SInt then T_int.zero ()
      else T_real.rzero ()
    in
    let str_of_guards = function
      | [] -> "true"
      | guards -> Formula.str_of @@ Formula.and_of (List.rev guards)
    in
    (* the terms of the current equation accepted under strength (2), newest
       first, each with its guards *)
    let assumed = ref [] in
    (* every question below gets at most 10 s (or the run's remaining budget
       if smaller): an undecided one only costs the silent acceptance, never
       a refusal *)
    let budget () =
      Some
        (match Z3Smt.Z3interface.armed_budget_ms () with
        | Some ms -> Int.min ms 10_000
        | None -> 10_000)
    in
    (* a fresh solver: the question is asked before the integers are relaxed,
       and asked in the pooled context it left the later solving of an input
       over [y : int] (relaxed to [y : real]) not returning within 60 s where
       it had answered in 5 s *)
    let ask_valid phi =
      if Z3Smt.Z3interface.may_not_return phi then
        `Undecided "a question Z3 may not return from"
      else
        match
          Z3Smt.Z3interface.check_valid ~fresh_solver:true ~timeout:(budget ())
            ~id:None (LogicOld.get_fenv ()) phi
        with
        | `Valid -> `Valid
        | `Invalid _ -> `Invalid
        | `Timeout -> `Undecided "timeout"
        | `Unknown reason -> `Undecided reason
        | `Sat _ | `Unsat -> `Undecided "not a validity answer"
    in
    let ask_sat phi =
      if Z3Smt.Z3interface.may_not_return phi then
        `Undecided "a question Z3 may not return from"
      else
        match
          Z3Smt.Z3interface.check_sat ~fresh_solver:true ~timeout:(budget ())
            ~id:None (LogicOld.get_fenv ()) [ phi ]
        with
        | `Sat _ -> `Sat
        | `Unsat -> `Unsat
        | `Timeout -> `Undecided "timeout"
        | `Unknown reason -> `Undecided reason
        | _ -> `Undecided "not a satisfiability answer"
    in
    (* [show ~what ~strict guards t] judges [t > 0] (strict) or [t >= 0]
       under [guards] in the two strengths of the contract above: returns
       [()] when it holds at every guard-satisfying state, records [t] in
       [assumed] when it holds at some, and refuses naming [t] and [guards]
       when it holds at none *)
    let show ~what ~strict guards t =
      let goal = (if strict then Formula.gt else Formula.geq) t (zero_of t) in
      let closed = Set.is_empty (Term.tvs_of t) in
      let closed_value =
        if not closed then None
        else
          try Some (Evaluator.eval goal)
          with exn when not (Timer.is_async exn) -> None
      in
      let trace question answer =
        Debug.print ~id:None
        @@ lazy
             (sprintf "[well-formedness] %s: %s" (Formula.str_of question)
                answer)
      in
      let refuse () =
        Common.Refusal.refuse
          "not a QFL input: %s %s is %s at every state satisfying the guard \
           %s (QFL values are in [0, inf]; split a mixed-sign expectation \
           into its positive and negative parts)"
          what (Term.str_of t)
          (if strict then "non-positive" else "negative")
          (str_of_guards guards)
      in
      let decided =
        match closed_value with
        | Some true -> `Valid
        (* the shape decides strength (1): a closed term of the wrong sign
           under no guard is wrong at every state *)
        | Some false when List.is_empty guards -> `Never
        | _ -> (
            let valid_q = Formula.mk_imply (Formula.and_of guards) goal in
            let valid_a = ask_valid valid_q in
            trace valid_q
              (match valid_a with
              | `Valid -> "valid"
              | `Invalid -> "invalid"
              | `Undecided r -> "undecided: " ^ r);
            match valid_a with
            | `Valid -> `Valid
            | (`Invalid | `Undecided _) as valid_a -> (
                let sat_q = Formula.and_of (goal :: guards) in
                let sat_a = ask_sat sat_q in
                trace sat_q
                  (match sat_a with
                  | `Sat -> "sat"
                  | `Unsat -> "unsat"
                  | `Undecided r -> "undecided: " ^ r);
                match (sat_a, valid_a) with
                | `Unsat, _ -> `Never
                | `Sat, _ -> `Sometimes
                | `Undecided _, `Undecided r -> `Undecided r
                | `Undecided r, `Invalid -> `Undecided r))
      in
      match decided with
      | `Valid -> ()
      | `Never -> refuse ()
      | `Sometimes | `Undecided _ ->
          assumed :=
            sprintf "%s%s%s" (Term.str_of t)
              (if strict then " > 0" else " >= 0")
              (match guards with
              | [] -> ""
              | _ -> " under " ^ str_of_guards guards)
            :: !assumed
    in
    (* one note per equation (or for the query's bound) accepted under
       strength (2), naming its terms *)
    let note ~whose =
      match List.rev !assumed with
      | [] -> ()
      | terms ->
          assumed := [];
          Out_channel.output_string Out_channel.stderr
            (sprintf
               "note: QFL values are in [0, inf], and %s is not shown \
                non-negative at every state: the answer assumes %s at every \
                state reachable from the query\n"
               whose
               (String.concat ~sep:", " terms));
          Out_channel.flush Out_channel.stderr
    in
    let scalar ~what guards t =
      List.iter (Term.elim_min_max_list t) ~f:(show ~what ~strict:false guards)
    in
    (* a conditional is split before its freedom is asked, so that a refusal
       names the offending branch and the guard that leads to it *)
    let rec walk ~name guards t =
      match QFL.Unif.let_unif t with
      | Some _ when free t -> scalar ~what:"the term" guards (QFL.Unif.integrate t)
      | Some (r, body) ->
          (* an integral over [0, 1] of an integrand non-negative there is
             non-negative *)
          let rt = Term.mk_var r T_real.SReal in
          walk ~name
            (Formula.leq rt (T_real.rone ())
            :: Formula.geq rt (T_real.rzero ())
            :: guards)
            body
      | None -> (
      match t with
      | Term.FunApp (T_bool.IfThenElse, [ c; t1; t2 ], _) when free c ->
          let c = Formula.of_bool_term c in
          walk ~name (c :: guards) t1;
          walk ~name (Formula.mk_neg c :: guards) t2
      | _ when free t -> scalar ~what:"the term" guards t
      | _ -> (
        match t with
        | Term.FunApp (FVar (f, _, _), _, _) when Set.mem unknowns f -> ()
        | Term.Var (x, _, _) when Set.mem unknowns x -> ()
        | Term.FunApp (FVar (Ident.Tvar ("min" | "max"), _, _), args, _) ->
            List.iter args ~f:(walk ~name guards)
        | Term.FunApp ((T_real.RAdd | T_int.Add | T_num.NAdd _), [ t1; t2 ], _)
          ->
            walk ~name guards t1;
            walk ~name guards t2
        | Term.FunApp ((T_real.RMul | T_int.Mul | T_num.NMul _), [ t1; t2 ], _)
          when free t1 || free t2 ->
            let c, f = if free t1 then (t1, t2) else (t2, t1) in
            scalar ~what:"the factor" guards c;
            walk ~name guards f
        | Term.FunApp ((T_real.RDiv | T_num.NDiv _), [ t1; t2 ], _) when free t2
          ->
            List.iter (Term.elim_min_max_list t2)
              ~f:(show ~what:"the divisor" ~strict:true guards);
            walk ~name guards t1
        | _ ->
            Common.Refusal.refuse
              "not a QFL input: %s in the body of %s applies an unknown \
               outside the grammar X(e) | t | F + F | t * F | if phi then F \
               else F (QFL values are in [0, inf]; split a mixed-sign \
               expectation into its positive and negative parts)"
              (Term.str_of t) name))
    in
    List.iter qfl.preds ~f:(fun (pred : QFL.Pred.t) ->
        let name = Ident.name_of_tvar pred.name in
        walk ~name (List.rev pred.arg_constrs) pred.body;
        note ~whose:("a term of the body of " ^ name));
    if free query.bound then (
      scalar ~what:"the query's bound"
        (Option.to_list query.left)
        query.bound;
      note ~whose:"the query's bound")

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
          (match qfl.query with
          | Check query -> refuse_ill_formed qfl query
          | ASAT _ | DistCheck _ ->
              if mentions_unif qfl then
                Common.Refusal.refuse
                  "integrals (unif) are read by the bound checker only; the \
                   almost-sure and distribution checks do not take them");
          (* a bound query over integer states is relaxed to the reals before
             anything else reads it, the acceleration's detection included
             (see [relax_to_reals]); one that cannot be relaxed is kept as it
             is, is not given to the detection, and [check_bounds] answers it
             [unknown] *)
          let int_states =
            match qfl.query with
            | Check query -> integer_states qfl query
            | ASAT _ | DistCheck _ -> None
          in
          let qfl =
            match qfl.query with
            | Check query -> (
                match relax_to_reals qfl query with
                | Ok (qfl, _) -> qfl
                | Error _ -> qfl)
            | ASAT _ | DistCheck _ -> qfl
          in
          let detections =
            if config.qfl.enable_geometric_pla && not (mentions_int qfl) then
              QFL.Accel.detect_geometric qfl
            else []
          in
          if config.qfl.enable_geometric_pla && not (List.is_empty detections) then
            Debug.print ~id:None
            @@ lazy
                 (let accel_problem = QFL.Accel.accelerate_applicable qfl in
                  let accel_template_config =
                    QFL.Accel.
                      {
                        num_conds = config.qfl.templates.prefp.num_conds;
                        use_orig_ite = config.qfl.templates.prefp.use_orig_ite;
                        cond_degree = config.qfl.templates.prefp.cond_degree;
                        term_degree = config.qfl.templates.prefp.term_degree;
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
              check_bounds ~print_sol ~int_states (i, sols, pareto_cache) qfl
                query
          | DistCheck query -> check_dist_bounds ~print_sol qfl query)
    in
    print_run_summary ~print_sol;
    res
end
