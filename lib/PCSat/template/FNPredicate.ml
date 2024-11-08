open Core
open Common
open Common.Ext
open Common.Util
open Ast
open Ast.LogicOld
open PCSatCommon.HypSpace
open Function

module Config = struct
  type t = {
    verbose : bool;
    number_of_expr : int;
    number_of_cond_conj : int;
    depth : int;
    ext : int;
    upper_bound_expr_coeff : int option;
    upper_bound_expr_const : int option;
    expr_seeds : int list option;
    upper_bound_cond_coeff : int option;
    upper_bound_cond_const : int option;
    cond_seeds : int list option;
    max_number_of_cond_conj : int option;
    lower_bound_expr_coeff : int option;
    lower_bound_cond_coeff : int option;
    bound_each_expr_coeff : int option;
    bound_each_cond_coeff : int option;
    threshold_expr_coeff : int option;
    threshold_expr_const : int option;
    threshold_cond_coeff : int option;
    threshold_cond_const : int option;
    ignore_bool : bool;
    fix_shape : bool;
    fix_depth_ext : bool;
    fix_upper_bound : bool;
  }
  [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  let instantiate_ext_files cfg = Ok cfg

  let load_ext_file = function
    | ExtFile.Instance x -> Ok (ExtFile.Instance x)
    | Filename filename -> (
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename) >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x -> instantiate_ext_files x >>= fun x -> Ok (ExtFile.Instance x)
        | Error msg ->
            error_string
            @@ sprintf "Invalid FNPredicate Configuration (%s): %s" filename msg
        )
end

module type ArgType = sig
  val name : Ident.tvar
  val sorts : Sort.t list
  val fenv : LogicOld.FunEnv.t
  val sol_space : SolSpace.t
  val id : int option
end

(*
   - number of expressions : int
   - number of conjunctions in conditional expressions : int
   - coeff_upper_bound : Z.t
   - const_upper_bound : Z.t
   - const seed of_template : Z.t Set.Poly.t
   - coeff_upper_bound_for_cond : Z.t
   - const_upper_bound_for_cond : Z.t
   - const seed of_cond : Z.t Set.Poly.t
   *)
type parameter = {
  nd : int;
  nc : int;
  depth : int;
  ext : int;
  ubec : Z.t option;
  ubed : Z.t option;
  es : Z.t Set.Poly.t;
  ubcc : Z.t option;
  ubcd : Z.t option;
  cs : Z.t Set.Poly.t;
}

type parameter_update_type +=
  | ExprCondConjDepthExt
  | ExprCoeff
  | ExprConst
  | CondCoeff
  | CondConst

type state =
  int
  * int
  * int
  * int
  * int option
  * int option
  * int option
  * int option
  * bool
  * bool
  * bool
  * bool
  * bool
  * bool
[@@deriving to_yojson]

let state_of param labels : state =
  ( param.nd,
    param.nc,
    param.depth,
    param.ext,
    Option.map ~f:Z.to_int param.ubec,
    Option.map ~f:Z.to_int param.ubed,
    Option.map ~f:Z.to_int param.ubcc,
    Option.map ~f:Z.to_int param.ubcd,
    Set.mem labels ExprCondConjDepthExt (* ToDo: this is always true *),
    Set.mem labels ExprCoeff,
    Set.mem labels ExprConst,
    Set.mem labels CondCoeff,
    Set.mem labels CondConst,
    Set.mem labels TimeOut )

module Make (Cfg : Config.ConfigType) (Arg : ArgType) : Function.Type = struct
  let config = Cfg.config
  let id = Arg.id

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_id id

  let param =
    ref
      {
        nd = config.number_of_expr;
        nc = config.number_of_cond_conj;
        depth = config.depth;
        ext = config.ext;
        ubec = Option.map config.upper_bound_expr_coeff ~f:Z.of_int;
        ubed = Option.map config.upper_bound_expr_const ~f:Z.of_int;
        es =
          (match config.expr_seeds with
          | None -> Set.Poly.singleton Z.zero
          | Some ds -> Set.Poly.of_list @@ List.map ds ~f:Z.of_int);
        ubcc = Option.map config.upper_bound_cond_coeff ~f:Z.of_int;
        ubcd = Option.map config.upper_bound_cond_const ~f:Z.of_int;
        cs =
          (match config.cond_seeds with
          | None -> Set.Poly.singleton Z.zero
          | Some ds -> Set.Poly.of_list @@ List.map ds ~f:Z.of_int);
      }

  let init =
    {
      nd = (if config.fix_shape then config.number_of_expr else 1);
      nc = (if config.fix_shape then config.number_of_cond_conj else 1);
      depth = (if config.fix_depth_ext then config.depth else 0);
      ext = (if config.fix_depth_ext then config.ext else 0);
      ubec =
        (if config.fix_upper_bound then
           Option.map ~f:Z.of_int config.upper_bound_expr_coeff
         else Some Z.one);
      ubed =
        (if config.fix_upper_bound then
           Option.map ~f:Z.of_int config.upper_bound_expr_const
         else Some Z.zero);
      es = Set.Poly.singleton Z.zero;
      ubcc =
        (if config.fix_upper_bound then
           Option.map ~f:Z.of_int config.upper_bound_cond_coeff
         else Some Z.one);
      ubcd =
        (if config.fix_upper_bound then
           Option.map ~f:Z.of_int config.upper_bound_cond_const
         else Some Z.zero);
      cs = Set.Poly.singleton Z.zero;
    }

  let name_of () = Arg.name
  let kind_of () = Kind.str_of Kind.FN
  let sort_of () = Sort.mk_fun @@ Arg.sorts @ [ T_bool.SBool ]

  let params_of ~tag =
    ignore tag;
    sort_env_list_of_sorts Arg.sorts

  let show_state ?(config = PCSatCommon.RLConfig.disabled) labels =
    ignore config;
    Debug.print_stdout
    @@ lazy
         (sprintf "state of %s: %s" (Ident.name_of_tvar (name_of ()))
         @@ Yojson.Safe.to_string @@ state_to_yojson @@ state_of !param labels);
    Out_channel.flush Out_channel.stdout

  let str_of () =
    sprintf
      ("number of cases (max: %s) : %d\n"
     ^^ "number of condition conjuncts (max: %s) : %d\n"
     ^^ "depth (max: %s) : %d\n" ^^ "ext : %d\n"
     ^^ "upper bound of the sum of the abs of expression coefficients : %s\n"
     ^^ "upper bound of the abs of expression constant : %s\n"
     ^^ "seeds of expressions : %s\n"
     ^^ "upper bound of the sum of the abs of condition coefficients : %s\n"
     ^^ "upper bound of the abs of condition constant : %s\n"
     ^^ "seeds of conditions : %s")
      (SolSpace.str_of_tvar_and_flag Arg.name SolSpace.ND Arg.sol_space)
      !param.nd
      (SolSpace.str_of_tvar_and_flag Arg.name SolSpace.NC Arg.sol_space)
      !param.nc
      (SolSpace.str_of_tvar_and_flag Arg.name SolSpace.Depth Arg.sol_space)
      !param.depth !param.ext
      (match !param.ubec with None -> "N/A" | Some ubec -> Z.to_string ubec)
      (match !param.ubed with None -> "N/A" | Some ubed -> Z.to_string ubed)
      (String.concat_set ~sep:"," @@ Set.Poly.map !param.es ~f:Z.to_string)
      (match !param.ubcc with None -> "N/A" | Some ubcc -> Z.to_string ubcc)
      (match !param.ubcd with None -> "N/A" | Some ubcd -> Z.to_string ubcd)
      (String.concat_set ~sep:"," @@ Set.Poly.map !param.cs ~f:Z.to_string)

  let in_space () =
    SolSpace.in_space Arg.name SolSpace.ND !param.nd Arg.sol_space
    && SolSpace.in_space Arg.name SolSpace.NC !param.nc Arg.sol_space
    && SolSpace.in_space Arg.name SolSpace.Depth !param.depth Arg.sol_space

  let adjust_quals ~tag quals =
    let params = params_of ~tag in
    let eq_quals =
      Qualifier.AllTheory.mk_eq_quals_for_ith_param params
        (List.length params - 1)
    in
    Set.union eq_quals
    @@ Set.Poly.filter_map quals ~f:(fun phi ->
           match Normalizer.normalize phi with
           | Formula.Atom
               ( Atom.App (Predicate.Psym (T_bool.Eq | T_int.Geq), [ t1; t2 ], _),
                 _ ) ->
               Some (Formula.eq t1 t2)
           | phi ->
               let qual =
                 Z3Smt.Z3interface.qelim ~id ~fenv:Arg.fenv
                 @@ Formula.exists [ List.last_exn params ] phi
               in
               if Formula.is_bind qual || Set.is_empty (Formula.fvs_of qual)
               then None
               else Some qual)

  let init_quals _ _ = ()

  let update_hspace ~tag hspace =
    ignore tag;
    Qualifier.AllTheory.qualifiers_of ~fenv:Arg.fenv !param.depth hspace

  let gen_template ~tag ~ucore hspace =
    ignore tag;
    ignore ucore;
    let ( temp_params,
          hole_qualifiers_map,
          tmpl,
          constr_of_expr_dt_bound,
          cnstr_of_expr_coeffs,
          cnstr_of_expr_const,
          cnstr_of_cond_coeffs,
          cnstr_of_cond_const ) =
      Generator.gen_fn_predicate config.ignore_bool (Set.to_list hspace.quals)
        (Set.to_list hspace.terms)
        (Generator.mk_tp
           (List.init !param.nd ~f:(fun _ -> !param.nc))
           !param.depth !param.ext !param.ubec !param.ubed !param.es !param.ubcc
           !param.ubcd !param.cs)
        (Generator.mk_tsp
           (Option.map config.lower_bound_expr_coeff ~f:Z.of_int)
           (Option.map config.lower_bound_cond_coeff ~f:Z.of_int)
           (Option.map config.bound_each_expr_coeff ~f:Z.of_int)
           (Option.map config.bound_each_cond_coeff ~f:Z.of_int))
        hspace.params
    in
    (* let tmpl =
       Formula.elim_ite tmpl
       |> Evaluator.simplify
       |> Z3Smt.Z3interface.simplify ~id Arg.fenv
       in *)
    Debug.print
    @@ lazy
         (sprintf "[%s] predicate template:\n  %s"
            (Ident.name_of_tvar @@ Arg.name)
            (Formula.str_of tmpl));
    Debug.print
    @@ lazy
         (sprintf "[%s] constr_of_expr_dt_bound:\n  %s"
            (Ident.name_of_tvar @@ Arg.name)
            (Formula.str_of constr_of_expr_dt_bound));
    Debug.print
    @@ lazy
         (sprintf "[%s] cnstr_of_expr_coeffs:\n  %s"
            (Ident.name_of_tvar @@ Arg.name)
            (Formula.str_of cnstr_of_expr_coeffs));
    Debug.print
    @@ lazy
         (sprintf "[%s] cnstr_of_expr_const:\n  %s"
            (Ident.name_of_tvar @@ Arg.name)
            (Formula.str_of cnstr_of_expr_const));
    Debug.print
    @@ lazy
         (sprintf "[%s] cnstr_of_cond_coeffs:\n  %s"
            (Ident.name_of_tvar @@ Arg.name)
            (Formula.str_of cnstr_of_cond_coeffs));
    Debug.print
    @@ lazy
         (sprintf "[%s] cnstr_of_cond_const:\n  %s"
            (Ident.name_of_tvar @@ Arg.name)
            (Formula.str_of cnstr_of_cond_const));
    let tmpl =
      Logic.(Term.mk_lambda (of_old_sort_env_list hspace.params))
      @@ Logic.ExtTerm.of_old_formula tmpl
    in
    ( (ExprCondConjDepthExt, tmpl),
      [
        (ExprCoeff, Logic.ExtTerm.of_old_formula cnstr_of_expr_coeffs);
        (ExprConst, Logic.ExtTerm.of_old_formula cnstr_of_expr_const);
        (CondCoeff, Logic.ExtTerm.of_old_formula cnstr_of_cond_coeffs);
        (CondConst, Logic.ExtTerm.of_old_formula cnstr_of_cond_const);
        ( ExprCondConjDepthExt,
          Logic.ExtTerm.of_old_formula constr_of_expr_dt_bound );
      ],
      temp_params,
      hole_qualifiers_map )

  let restart (_param, actions) =
    Debug.print
    @@ lazy
         ("************* restarting "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    (init, actions @ [ "restart" ])

  let last_non_timeout_param = ref !param

  let revert (_param, actions) =
    Debug.print
    @@ lazy
         ("************* reverting "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    (!last_non_timeout_param, actions @ [ "revert" ])

  let increase_expr (param, actions) =
    Debug.print
    @@ lazy
         ("************* increasing number_of_expr of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with nd = param.nd + 1 }, actions @ [ "increase_expr" ])

  let decrease_expr (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing number_of_expr of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with nd = max (param.nd - 1) 0 }, actions @ [ "decrease_expr" ])

  let init_expr (param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing number_of_expr of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with nd = init.nd }, actions @ [ "init_expr" ])

  let increase_cond_conj (param, actions) =
    Debug.print
    @@ lazy
         ("************* increasing number_of_cond_conj of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with nc = param.nc + 1 }, actions @ [ "increase_cond_conj" ])

  let decrease_cond_conj (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing number_of_cond_conj of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ( { param with nc = max (param.nc - 1) 0 },
      actions @ [ "decrease_cond_conj" ] )

  let init_cond_conj (param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing number_of_cond_conj of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with nc = init.nc }, actions @ [ "init_cond_conj" ])

  let increase_depth (param, actions) =
    Debug.print
    @@ lazy
         ("************* increasing depth of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with depth = param.depth + 1 }, actions @ [ "increase_depth" ])

  let decrease_depth (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing depth of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ( { param with depth = max (param.depth - 1) 0 },
      actions @ [ "decrease_depth" ] )

  let init_depth (param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing depth of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with depth = init.depth }, actions @ [ "init_depth" ])

  let increase_ext (param, actions) =
    Debug.print
    @@ lazy
         ("************* increasing ext of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with ext = param.ext + 1 }, actions @ [ "increase_ext" ])

  let decrease_ext (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing ext of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with ext = max (param.ext - 1) 0 }, actions @ [ "decrease_ext" ])

  let init_ext (param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing ext of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with ext = init.ext }, actions @ [ "init_ext" ])

  let set_inf_expr_coeff (param, actions) =
    Debug.print
    @@ lazy
         ("************* setting upper_bound_expr_coeff of "
         ^ Ident.name_of_tvar Arg.name
         ^ " to infinity ***************");
    ({ param with ubec = None }, actions @ [ "set_inf_expr_coeff" ])

  let increase_expr_coeff threshold (param, actions) =
    match (param.ubec, threshold) with
    | Some ubec, Some thr when Z.Compare.(ubec >= Z.of_int thr) ->
        set_inf_expr_coeff (param, actions)
    | _, _ ->
        Debug.print
        @@ lazy
             ("************* increasing upper_bound_expr_coeff of "
             ^ Ident.name_of_tvar Arg.name
             ^ "***************");
        ( {
            param with
            ubec = Option.map param.ubec ~f:(fun ubec -> Z.(ubec + one));
          },
          actions @ [ "increase_expr_coeff" ] )

  let decrease_expr_coeff (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing upper_bound_expr_coeff of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ( {
        param with
        ubec = Option.map param.ubec ~f:(fun ubec -> Z.(max (ubec - one) zero));
      },
      actions @ [ "decrease_expr_coeff" ] )

  let init_expr_coeff (param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing upper_bound_expr_coeff of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with ubec = init.ubec }, actions @ [ "init_expr_coeff" ])

  let set_inf_expr_const (param, actions) =
    Debug.print
    @@ lazy
         ("************* setting upper_bound_expr_const of "
         ^ Ident.name_of_tvar Arg.name
         ^ " to infinity ***************");
    ({ param with ubed = None }, actions @ [ "set_inf_expr_const" ])

  let increase_expr_const threshold (param, actions) =
    match (param.ubed, threshold) with
    | Some ubed, Some thr when Z.Compare.(ubed >= Z.of_int thr) ->
        set_inf_expr_const (param, actions)
    | _, _ ->
        Debug.print
        @@ lazy
             ("************* increasing upper_bound_expr_const of "
             ^ Ident.name_of_tvar Arg.name
             ^ "***************");
        ( {
            param with
            ubed = Option.map param.ubed ~f:(fun ubed -> Z.(ubed + one));
          },
          actions @ [ "increase_expr_const" ] )

  let decrease_expr_const (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing upper_bound_expr_const of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ( {
        param with
        ubed = Option.map param.ubed ~f:(fun ubed -> Z.(max (ubed - one) zero));
      },
      actions @ [ "decrease_expr_const" ] )

  let init_expr_const (param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing upper_bound_expr_const of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with ubed = init.ubed }, actions @ [ "init_expr_const" ])

  let set_inf_cond_coeff (param, actions) =
    Debug.print
    @@ lazy
         ("************* setting upper_bound_cond_coeff of "
         ^ Ident.name_of_tvar Arg.name
         ^ " to infinity ***************");
    ({ param with ubcc = None }, actions @ [ "set_inf_cond_coeff" ])

  let increase_cond_coeff threshold (param, actions) =
    match (param.ubcc, threshold) with
    | Some ubcc, Some thr when Z.Compare.(ubcc >= Z.of_int thr) ->
        set_inf_cond_coeff (param, actions)
    | _, _ ->
        Debug.print
        @@ lazy
             ("************* increasing upper_bound_cond_coeff of "
             ^ Ident.name_of_tvar Arg.name
             ^ "***************");
        ( {
            param with
            ubcc = Option.map param.ubcc ~f:(fun ubcc -> Z.(ubcc + one));
          },
          actions @ [ "increase_cond_coeff" ] )

  let decrease_cond_coeff (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing upper_bound_cond_coeff of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ( {
        param with
        ubcc = Option.map param.ubcc ~f:(fun ubcc -> Z.(max (ubcc - one) zero));
      },
      actions @ [ "decrease_cond_coeff" ] )

  let init_cond_coeff (param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing upper_bound_cond_coeff of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with ubcc = init.ubcc }, actions @ [ "init_cond_coeff" ])

  let set_inf_cond_const (param, actions) =
    Debug.print
    @@ lazy
         ("************* setting upper_bound_cond_const of "
         ^ Ident.name_of_tvar Arg.name
         ^ " to infinity ***************");
    ({ param with ubcd = None }, actions @ [ "set_inf_cond_const" ])

  let increase_cond_const threshold (param, actions) =
    match (param.ubcd, threshold) with
    | Some ubcd, Some thr when Z.Compare.(ubcd >= Z.of_int thr) ->
        set_inf_cond_const (param, actions)
    | _, _ ->
        Debug.print
        @@ lazy
             ("************* increasing upper_bound_cond_const of "
             ^ Ident.name_of_tvar Arg.name
             ^ "***************");
        ( {
            param with
            ubcd = Option.map param.ubcd ~f:(fun ubcd -> Z.(ubcd + one));
          },
          actions @ [ "increase_cond_const" ] )

  let decrease_cond_const (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing upper_bound_cond_const of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ( {
        param with
        ubcd = Option.map param.ubcd ~f:(fun ubcd -> Z.(max (ubcd - one) zero));
      },
      actions @ [ "decrease_cond_const" ] )

  let init_cond_const (param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing upper_bound_cond_const of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with ubcd = init.ubcd }, actions @ [ "init_cond_const" ])

  let increase_depth_ext (param, actions) =
    if (param.depth + param.ext) mod 2 = 0 then increase_depth (param, actions)
    else increase_ext (param, actions)

  let try_then f g =
    let res = f () in
    let backup = !param in
    param := fst res;
    if in_space () then (
      param := backup;
      res)
    else g ()

  let increase_expr_cond_conj_depth_ext (param, actions) =
    let f () = increase_expr (param, actions) in
    let g () = increase_cond_conj (param, actions) in
    if
      List.exists Arg.sorts ~f:(fun s ->
          Term.is_dt_sort s || Term.is_array_sort s)
      && param.nd * param.nc > Integer.pow (param.depth + 1) 3
    then (*ToDo: try_then*) increase_depth_ext (param, actions)
    else if
      (param.nd + param.nc) mod 2 = 0
      ||
      match config.max_number_of_cond_conj with
      | None -> false
      | Some max -> param.nc >= max
    then try_then f g
    else try_then g f

  let rec inner param_actions = function
    | [] -> param_actions
    | ExprCondConjDepthExt :: labels ->
        inner
          (if config.fix_shape then
             if config.fix_depth_ext then param_actions
             else increase_depth_ext param_actions
           else increase_expr_cond_conj_depth_ext param_actions)
          labels
    | ExprCoeff :: labels ->
        inner
          (if config.fix_upper_bound then param_actions
           else increase_expr_coeff config.threshold_expr_coeff param_actions)
          labels
    | ExprConst :: labels ->
        inner
          (if config.fix_upper_bound then param_actions
           else increase_expr_const config.threshold_expr_const param_actions)
          labels
    | CondCoeff :: labels ->
        inner
          (if config.fix_upper_bound then param_actions
           else increase_cond_coeff config.threshold_cond_coeff param_actions)
          labels
    | CondConst :: labels ->
        inner
          (if config.fix_upper_bound then param_actions
           else increase_cond_const config.threshold_cond_const param_actions)
          labels
    | QDep :: labels -> inner param_actions labels
    | TimeOut :: _labels -> param_actions (* z3 may unexpectedly time out*)
    | _ -> assert false

  let actions_of labels =
    (snd @@ inner (!param, []) @@ Set.to_list labels) @ [ "end" ]

  let update_with_labels labels =
    param := fst @@ inner (!param, []) @@ Set.to_list labels

  (* called on failure, ignore config.fix_shape *)
  let rl_action labels =
    if not @@ Set.mem labels TimeOut then last_non_timeout_param := !param;
    let rec action param_actions =
      match In_channel.input_line_exn In_channel.stdin with
      | "increase_expr" -> action (increase_expr param_actions)
      | "decrease_expr" -> action (decrease_expr param_actions)
      | "init_expr" -> action (init_expr param_actions)
      | "increase_cond_conj" -> action (increase_cond_conj param_actions)
      | "decrease_cond_conj" -> action (decrease_cond_conj param_actions)
      | "init_cond_conj" -> action (init_cond_conj param_actions)
      | "increase_depth" -> action (increase_depth param_actions)
      | "decrease_depth" -> action (decrease_depth param_actions)
      | "init_depth" -> action (init_depth param_actions)
      | "increase_ext" -> action (increase_ext param_actions)
      | "decrease_ext" -> action (decrease_ext param_actions)
      | "init_ext" -> action (init_ext param_actions)
      | "set_inf_expr_coeff" -> action (set_inf_expr_coeff param_actions)
      | "increase_expr_coeff" -> action (increase_expr_coeff None param_actions)
      | "decrease_expr_coeff" -> action (decrease_expr_coeff param_actions)
      | "init_expr_coeff" -> action (init_expr_coeff param_actions)
      | "set_inf_expr_const" -> action (set_inf_expr_const param_actions)
      | "increase_expr_const" -> action (increase_expr_const None param_actions)
      | "decrease_expr_const" -> action (decrease_expr_const param_actions)
      | "init_expr_const" -> action (init_expr_const param_actions)
      | "set_inf_cond_coeff" -> action (set_inf_cond_coeff param_actions)
      | "increase_cond_coeff" -> action (increase_cond_coeff None param_actions)
      | "decrease_cond_coeff" -> action (decrease_cond_coeff param_actions)
      | "init_cond_coeff" -> action (init_cond_coeff param_actions)
      | "set_inf_cond_const" -> action (set_inf_cond_const param_actions)
      | "increase_cond_const" -> action (increase_cond_const None param_actions)
      | "decrease_cond_const" -> action (decrease_cond_const param_actions)
      | "init_cond_const" -> action (init_cond_const param_actions)
      | "restart" -> action (restart param_actions)
      | "revert" -> action (revert param_actions)
      | "end" -> fst param_actions
      | s -> failwith ("Unknown action: " ^ s)
    in
    param := action (!param, [])

  let restart () = param := fst @@ restart (!param, [])
  let update_with_solution _ = failwith "not implemented"
  let sync _thre = assert false
  (*let mx = max nd nc
           |> max @@ Z.to_int (match ubec with None -> Z.zero | Some n -> n)
           |> max @@ Z.to_int (match ubed with None -> Z.zero | Some n -> n)
           |> max @@ Z.to_int (match ubcc with None -> Z.zero | Some n -> n)
           |> max @@ Z.to_int (match ubcd with None -> Z.zero | Some n -> n) in
    let mn = mx - thre in
    let param' = (max nd mn), (max nc mn), (max depth mn), (max ext mn),
               Option.map ubec ~f:(Z.max (Z.of_int mn)),
               Option.map ubed ~f:(Z.max (Z.of_int mn)),
               es,
               Option.map ubcc ~f:(Z.max (Z.of_int mn)),
               Option.map ubcd ~f:(Z.max (Z.of_int mn)),
               cs in
    param := param'*)

  let _ =
    Debug.print
    @@ lazy
         (sprintf "************* initializing %s ***************"
            (Ident.name_of_tvar Arg.name));
    Debug.print @@ lazy (str_of ())
end
