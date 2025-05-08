open Core
open Common
open Common.Ext
open Common.Util
open Ast
open Ast.LogicOld
open Ast.HypSpace
open Function

module Config = struct
  type t = {
    verbose : bool;
    shape : int list;
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
            @@ sprintf "Invalid IntFunction Configuration (%s): %s" filename msg
        )
end

module type ArgType = sig
  val name : Ident.tvar
  val sorts : Sort.t list
  val fenv : LogicOld.FunEnv.t
  val id : int option
end

(*
   - template shape : int list
   - coeff_upper_bound : Z.t
   - const_upper_bound : Z.t
   - const seed of_template : Z.t Set.Poly.t
   - coeff_upper_bound_for_cond : Z.t
   - const_upper_bound_for_cond : Z.t
   - const seed of_cond : Z.t Set.Poly.t
   *)
type parameter = {
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

type parameter_update_type +=
  | ExprCondConjDepthExt
  | ExprCoeff
  | ExprConst
  | CondCoeff
  | CondConst

type state =
  int list
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
  ( param.shp,
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
        shp = config.shape;
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
    if config.fix_shape then
      {
        shp = config.shape;
        depth = 0;
        ext = 0;
        ubec = Some Z.one;
        ubed = Some Z.zero;
        es = Set.Poly.singleton Z.zero;
        ubcc = Some Z.one;
        ubcd = Some Z.zero;
        cs = Set.Poly.singleton Z.zero;
      }
    else
      {
        shp = [ 1 ];
        depth = 0;
        ext = 0;
        ubec = Some Z.one;
        ubed = Some Z.zero;
        es = Set.Poly.singleton Z.zero;
        ubcc = Some Z.one;
        ubcd = Some Z.zero;
        cs = Set.Poly.singleton Z.zero;
      }

  let name_of () = Arg.name
  let kind_of () = sprintf "flexible %s" (Kind.str_of Kind.IntFun)
  let sort_of () = Sort.mk_fun @@ Arg.sorts @ [ T_int.SInt ]

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
      ("shape : [%s]\n" ^^ "depth : %d\n" ^^ "ext : %d\n"
     ^^ "upper bound of the sum of the abs of expression coefficients : %s\n"
     ^^ "upper bound of the abs of expression constant : %s\n"
     ^^ "seeds of expressions : %s\n"
     ^^ "upper bound of the sum of the abs of condition coefficients : %s\n"
     ^^ "upper bound of the abs of condition constant : %s\n"
     ^^ "seeds of conditions : %s")
      (String.concat_map_list ~sep:";" !param.shp ~f:string_of_int)
      !param.depth !param.ext
      (match !param.ubec with None -> "N/A" | Some ubec -> Z.to_string ubec)
      (match !param.ubed with None -> "N/A" | Some ubed -> Z.to_string ubed)
      (String.concat_map_set ~sep:"," !param.es ~f:Z.to_string)
      (match !param.ubcc with None -> "N/A" | Some ubcc -> Z.to_string ubcc)
      (match !param.ubcd with None -> "N/A" | Some ubcd -> Z.to_string ubcd)
      (String.concat_map_set ~sep:"," !param.cs ~f:Z.to_string)

  let in_space () = true (* TODO *)

  let adjust_quals ~tag quals =
    let params = params_of ~tag in
    let eq_quals =
      Qual.mk_eq_quals_for_ith_param params (List.length params - 1)
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
    qualifiers_of ~fenv:Arg.fenv !param.depth hspace

  let gen_template ~tag ~ucore hspace =
    ignore tag;
    ignore ucore;
    let template =
      Templ.gen_fun ~ignore_bool:config.ignore_bool
        {
          terms = Set.to_list hspace.terms;
          quals = Set.to_list hspace.quals;
          shp = !param.shp;
          depth = !param.depth;
          ext = !param.ext;
          ubec = !param.ubec;
          ubed = !param.ubed;
          es = !param.es;
          ubcc = !param.ubcc;
          ubcd = !param.ubcd;
          cs = !param.cs;
        }
        {
          lbec = Option.map config.lower_bound_expr_coeff ~f:Z.of_int;
          lbcc = Option.map config.lower_bound_cond_coeff ~f:Z.of_int;
          beec = Option.map config.bound_each_expr_coeff ~f:Z.of_int;
          becc = Option.map config.bound_each_cond_coeff ~f:Z.of_int;
        }
        hspace.params (None, T_int.SInt)
    in
    (* let func =
       Formula.elim_ite tmpl
       |> Evaluator.simplify
       |> Z3Smt.Z3interface.simplify ~id Arg.fenv
       in *)
    Debug.print
    @@ lazy
         (sprintf "[%s] function template:\n  %s"
            (Ident.name_of_tvar @@ Arg.name)
            (Term.str_of template.func));
    Debug.print
    @@ lazy
         (sprintf "[%s] expr_params_bounds:\n  %s"
            (Ident.name_of_tvar @@ Arg.name)
            (Formula.str_of template.expr_params_bounds));
    Debug.print
    @@ lazy
         (sprintf "[%s] expr_coeffs_bounds:\n  %s"
            (Ident.name_of_tvar @@ Arg.name)
            (Formula.str_of template.expr_coeffs_bounds));
    Debug.print
    @@ lazy
         (sprintf "[%s] expr_const_bounds:\n  %s"
            (Ident.name_of_tvar @@ Arg.name)
            (Formula.str_of template.expr_const_bounds));
    Debug.print
    @@ lazy
         (sprintf "[%s] cond_coeffs_bounds:\n  %s"
            (Ident.name_of_tvar @@ Arg.name)
            (Formula.str_of template.cond_coeffs_bounds));
    Debug.print
    @@ lazy
         (sprintf "[%s] cond_const_bounds:\n  %s"
            (Ident.name_of_tvar @@ Arg.name)
            (Formula.str_of template.cond_const_bounds));
    let tmpl =
      Logic.(Term.mk_lambda (of_old_sort_env_list hspace.params))
      @@ Logic.ExtTerm.of_old_term template.func
    in
    ( (ExprCondConjDepthExt, tmpl),
      [
        (ExprCoeff, Logic.ExtTerm.of_old_formula template.expr_coeffs_bounds);
        (ExprConst, Logic.ExtTerm.of_old_formula template.expr_const_bounds);
        (CondCoeff, Logic.ExtTerm.of_old_formula template.cond_coeffs_bounds);
        (CondConst, Logic.ExtTerm.of_old_formula template.cond_const_bounds);
        ( ExprCondConjDepthExt,
          Logic.ExtTerm.of_old_formula template.expr_params_bounds );
      ],
      template.templ_params,
      template.hole_quals_map )

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
    ({ param with shp = 1 :: param.shp }, actions @ [ "increase_expr" ])

  let decrease_expr (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing number_of_expr of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ( { param with shp = (match param.shp with [] -> [] | _ :: shp -> shp) },
      actions @ [ "decrease_expr" ] )

  let increase_cond_conj expr_idx (param, actions) =
    Debug.print
    @@ lazy
         ("************* increasing number_of_cond_conj of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ( {
        param with
        shp =
          List.mapi param.shp ~f:(fun i nc ->
              if i = expr_idx then nc + 1 else nc);
      },
      actions @ [ "increase_cond_conj" ] )

  let decrease_cond_conj expr_idx (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing number_of_cond_conj of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ( {
        param with
        shp =
          List.mapi param.shp ~f:(fun i nc ->
              if i = expr_idx then max (nc - 1) 0 else nc);
      },
      actions @ [ "decrease_cond_conj" ] )

  let init_shape (param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing shape of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with shp = init.shp }, actions @ [ "init_shape" ])

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

  let increase_expr_cond_conj (param, actions) =
    if
      List.exists Arg.sorts ~f:(fun s ->
          Term.is_dt_sort s || Term.is_array_sort s)
      && List.fold param.shp ~init:1 ~f:( * ) > Integer.pow (param.depth + 1) 3
    then increase_depth_ext (param, actions)
    else
      match
        match config.max_number_of_cond_conj with
        | None -> Some (Random.int (List.length param.shp))
        | Some max ->
            List.find_mapi param.shp ~f:(fun idx nc ->
                if nc >= max then None else Some idx)
      with
      | None -> increase_expr (param, actions)
      | Some idx ->
          if
            (*ToDo*)
            (List.length param.shp + List.sum (module Int) param.shp ~f:Fn.id)
            mod 2
            = 0
          then increase_expr (param, actions)
          else increase_cond_conj idx (*ToDo*) (param, actions)

  let rec inner param_actions = function
    | [] -> param_actions
    | ExprCondConjDepthExt :: labels ->
        inner
          (if config.fix_shape then increase_depth_ext param_actions
           else increase_expr_cond_conj param_actions)
          labels
    | ExprCoeff :: labels ->
        inner
          (increase_expr_coeff config.threshold_expr_coeff param_actions)
          labels
    | ExprConst :: labels ->
        inner
          (increase_expr_const config.threshold_expr_const param_actions)
          labels
    | CondCoeff :: labels ->
        inner
          (increase_cond_coeff config.threshold_cond_coeff param_actions)
          labels
    | CondConst :: labels ->
        inner
          (increase_cond_const config.threshold_cond_const param_actions)
          labels
    | QualDep :: labels -> inner param_actions labels
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
      | "init_shape" -> action (init_shape param_actions)
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
      | s -> (
          let prefix = "increase_cond_conj@" in
          match String.chop_prefix s ~prefix with
          | Some res ->
              action (increase_cond_conj (int_of_string res) param_actions)
          | None -> (
              let prefix = "decrease_cond_conj@" in
              match String.chop_prefix s ~prefix with
              | Some res ->
                  action (decrease_cond_conj (int_of_string res) param_actions)
              | None -> failwith ("Unknown action: " ^ s)))
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
