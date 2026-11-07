(* Template for a numeric function unknown: [Make] for [Kind.IntFun] (sort
   [args -> Int]) and [MakeReal] for [Kind.RealFun] (sort [args -> Real]), the
   one family instantiated at two result sorts.  A guarded piecewise affine term
   over the arguments and the hypothesis space's terms, [number_of_expr] pieces
   under conditions of [number_of_cond_conj] conjuncts, with coefficient and
   constant bounds.  Shape, depth and bounds grow from the labels of an unsat
   core.

   At [Real] the constant of each piece is a [Real]-sorted template parameter
   ([Templ.gen_fun ~real_const]), so it may be any rational within the
   constant bound, while the coefficients of the arguments stay integers as at
   [Int].  A nullary [RealFun] unknown -- a real constant to be synthesised,
   which is what the template parameters of a polynomial quantified entailment
   are -- thus gets the template [c] with [|c - s| <= ub] for a seed [s] and
   the expression-constant bound [ub], raised on failure (at [Real] a nullary
   unknown grows by that bound alone; [Make] grows exactly as it did before
   [MakeReal] existed, nullary or not).  The bound makes the
   search incomplete for a solution of larger magnitude until it has been
   raised far enough, and never unsound: every candidate is validated. *)
open Core
open Common
open Common.Ext
open Common.Util
open Ast
open Ast.LogicOld
open Function

module Config = struct
  (* the coefficient bounds of the synthesized templates, by role *)
  type coeff_bound = {
    initial : int option; [@default Some 1]
        (** the starting bound on the sum of the absolute values of the coefficients
            ([None]: unbounded); a failure can raise it *)
    lower : int option; [@default None]
        (** a lower bound on the sum of the absolute values of the coefficients *)
    per_coefficient : int option; [@default None]
        (** a bound on the absolute value of each coefficient *)
    unbounded_above : int option; [@default None]
        (** once the coefficient bound has reached this value, raising it drops it
            altogether ([None]: it is raised by one each time) *)
  }
  [@@deriving yojson]

  type const_bound = {
    initial : int option; [@default Some 0]
        (** the starting bound on the sum of the absolute values of the constants
            ([None]: unbounded); a failure can raise it *)
    unbounded_above : int option; [@default None]
        (** once the constant bound has reached this value, raising it drops it
            altogether ([None]: it is raised by one each time) *)
    seeds : int list option; [@default None]
        (** the seed constants of the template ([None]: zero alone) *)
  }
  [@@deriving yojson]

  type role_bounds = {
    coeff : coeff_bound; [@default Common.Util.config_default coeff_bound_of_yojson "{}"]
    const : const_bound; [@default Common.Util.config_default const_bound_of_yojson "{}"]
  }
  [@@deriving yojson]

  type bounds = {
    expr : role_bounds; [@default Common.Util.config_default role_bounds_of_yojson "{}"]
        (** the bounds on the result expressions' coefficients and constants *)
    cond : role_bounds; [@default Common.Util.config_default role_bounds_of_yojson "{}"]
        (** the bounds on the branch conditions' coefficients and constants *)
  }
  [@@deriving yojson]

  type t = {
    verbose : bool; [@default false]
    number_of_expr : int; [@default 1]
    number_of_cond_conj : int; [@default 1]
    term_depth : int; [@default 0]
    extra_terms : int; [@default 0]
    bounds : bounds; [@default Common.Util.config_default bounds_of_yojson "{}"]
        (** the coefficient bounds of the synthesized templates *)
    max_number_of_cond_conj : int option; [@default None]
    branch_on_bool_args : bool; [@default false]
        (** offer the boolean parameters as branch conditions of the
            template ([Templ.gen_fun_bool_branch]) *)
    fix_shape : bool; [@default false]
  }
  [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  let instantiate_ext_files cfg = Ok cfg

  include MakeExtFile (struct
    type nonrec t = t

    let of_yojson = of_yojson
    let to_yojson = to_yojson
    let name = "IntFunction"
    let instantiate = instantiate_ext_files
  end)
end

module type ArgType = sig
  val name : Ident.tvar
  val sorts : Sort.t list
  val fenv : LogicOld.FunEnv.t
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
    (* [Z.to_int] is safe: the bounds are the template's configured
       coefficient and constant bounds, grown by one step at a time, never a
       model integer *)
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

(** the result sort a function template is instantiated at, and the kind of
    the unknowns it serves; [sort] is [Int] for [IntFun] and [Real] for
    [RealFun] *)
module type RetType = sig
  val kind : Kind.t
  val sort : Sort.t
end

module MakeOfSort (Ret : RetType) (Cfg : Config.ConfigType) (Arg : ArgType) :
  Function.Type = struct
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
        depth = config.term_depth;
        ext = config.extra_terms;
        ubec = Option.map config.bounds.expr.coeff.initial ~f:Z.of_int;
        ubed = Option.map config.bounds.expr.const.initial ~f:Z.of_int;
        es =
          (match config.bounds.expr.const.seeds with
          | None -> Set.Poly.singleton Z.zero
          | Some ds -> Set.Poly.of_list @@ List.map ds ~f:Z.of_int);
        ubcc = Option.map config.bounds.cond.coeff.initial ~f:Z.of_int;
        ubcd = Option.map config.bounds.cond.const.initial ~f:Z.of_int;
        cs =
          (match config.bounds.cond.const.seeds with
          | None -> Set.Poly.singleton Z.zero
          | Some ds -> Set.Poly.of_list @@ List.map ds ~f:Z.of_int);
      }

  let init =
    if config.fix_shape then
      {
        nd = config.number_of_expr;
        nc = config.number_of_cond_conj;
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
        nd = 1;
        nc = 1;
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
  let kind_of () = Kind.str_of Ret.kind
  let kind = Ret.kind
  let flexible = false
  let sort_of () = Sort.mk_fun @@ Arg.sorts @ [ Ret.sort ]
  let params_of () = sort_env_list_of_sorts Arg.sorts

  let show_state ?(config = PCSatCommon.RLConfig.disabled) labels =
    ignore config;
    Debug.print_stdout
    @@ lazy
         (sprintf "state of %s: %s" (Ident.name_of_tvar (name_of ()))
         @@ Yojson.Safe.to_string @@ state_to_yojson @@ state_of !param labels);
    Out_channel.flush Out_channel.stdout

  let str_of () =
    sprintf
      ("number of cases : %d\n" ^^ "number of condition conjuncts : %d\n"
     ^^ "depth : %d\n" ^^ "ext : %d\n"
     ^^ "upper bound of the sum of the abs of expression coefficients : %s\n"
     ^^ "upper bound of the abs of expression constant : %s\n"
     ^^ "seeds of expressions : %s\n"
     ^^ "upper bound of the sum of the abs of condition coefficients : %s\n"
     ^^ "upper bound of the abs of condition constant : %s\n"
     ^^ "seeds of conditions : %s")
      !param.nd !param.nc !param.depth !param.ext
      (match !param.ubec with None -> "N/A" | Some ubec -> Z.to_string ubec)
      (match !param.ubed with None -> "N/A" | Some ubed -> Z.to_string ubed)
      (String.concat_map_set ~sep:"," !param.es ~f:Z.to_string)
      (match !param.ubcc with None -> "N/A" | Some ubcc -> Z.to_string ubcc)
      (match !param.ubcd with None -> "N/A" | Some ubcd -> Z.to_string ubcd)
      (String.concat_map_set ~sep:"," !param.cs ~f:Z.to_string)

  let in_space () = true (* TODO *)
  let adjust_quals_terms = Fn.id

  let update_hspace hspace =
    HypSpace.qualifiers_of ~fenv:Arg.fenv !param.depth hspace

  let kind_cert_template () = None

  let gen_template ~ucore:_ (hspace : HypSpace.hspace) =
    let template =
      Function.refuse_without_template @@ fun () ->
      Templ.gen_fun ~print:Debug.print ~real_const:(Term.is_real_sort Ret.sort)
        ~ignore_bool:(not config.branch_on_bool_args)
        {
          consts = Set.to_list hspace.consts;
          terms = Set.to_list hspace.terms;
          quals = Set.to_list hspace.quals;
          shp = List.init !param.nd ~f:(fun _ -> !param.nc);
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
          lbec = Option.map config.bounds.expr.coeff.lower ~f:Z.of_int;
          lbcc = Option.map config.bounds.cond.coeff.lower ~f:Z.of_int;
          beec = Option.map config.bounds.expr.coeff.per_coefficient ~f:Z.of_int;
          becc = Option.map config.bounds.cond.coeff.per_coefficient ~f:Z.of_int;
        }
        hspace.params (None, Ret.sort)
    in
    (* let func =
       Formula.elim_ite tmpl
       |> Evaluator.simplify
       |> Z3Smt.Z3interface.simplify ~id Arg.fenv
       in *)
    Debug.print
    @@ lazy
         (sprintf "[%s] function template:\n  %s"
            (Ident.name_of_tvar Arg.name)
            (Term.str_of template.func));
    Debug.print
    @@ lazy
         (sprintf "[%s] expr_selectors_bounds:\n  %s"
            (Ident.name_of_tvar Arg.name)
            (Formula.str_of template.expr_selectors_bounds));
    Debug.print
    @@ lazy
         (sprintf "[%s] expr_coeffs_bounds:\n  %s"
            (Ident.name_of_tvar Arg.name)
            (Formula.str_of template.expr_coeffs_bounds));
    Debug.print
    @@ lazy
         (sprintf "[%s] expr_const_bounds:\n  %s"
            (Ident.name_of_tvar Arg.name)
            (Formula.str_of template.expr_const_bounds));
    Debug.print
    @@ lazy
         (sprintf "[%s] cond_coeffs_bounds:\n  %s"
            (Ident.name_of_tvar Arg.name)
            (Formula.str_of template.cond_coeffs_bounds));
    Debug.print
    @@ lazy
         (sprintf "[%s] cond_const_bounds:\n  %s"
            (Ident.name_of_tvar Arg.name)
            (Formula.str_of template.cond_const_bounds));
    let func =
      Logic.(Term.mk_lambda (of_old_sort_env_list hspace.params))
      @@ Logic.ExtTerm.of_old_term template.func
    in
    ( (ExprCondConjDepthExt, func),
      [
        ( false,
          ExprCoeff,
          Logic.ExtTerm.of_old_formula template.expr_coeffs_bounds );
        ( false,
          ExprConst,
          Logic.ExtTerm.of_old_formula template.expr_const_bounds );
        ( false,
          CondCoeff,
          Logic.ExtTerm.of_old_formula template.cond_coeffs_bounds );
        ( false,
          CondConst,
          Logic.ExtTerm.of_old_formula template.cond_const_bounds );
        ( true,
          ExprCondConjDepthExt,
          Logic.ExtTerm.of_old_formula template.expr_selectors_bounds );
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

  let increase_expr_cond_conj (param, actions) =
    if
      List.exists Arg.sorts ~f:(fun s ->
          Term.is_dt_sort s || Term.is_array_sort s)
      && param.nd * param.nc > Int.pow (param.depth + 1) 3
    then increase_depth_ext (param, actions)
    else if
      (param.nd + param.nc) mod 2 = 0
      ||
      match config.max_number_of_cond_conj with
      | None -> false
      | Some max -> param.nc >= max
    then increase_expr (param, actions)
    else increase_cond_conj (param, actions)

  let rec inner param_actions = function
    | [] -> param_actions
    | (ExprCondConjDepthExt | Shape) :: labels
      when Term.is_real_sort Ret.sort && List.is_empty Arg.sorts ->
        (* A nullary unknown denotes one value, so a guard can mention no
           argument and a second piece adds parameters and no candidate: every
           guarded term over no arguments equals one of its pieces.  What can
           widen its hypothesis space is the constant bound alone.  The same
           holds at [Int], but there the growth stays the one below, so that
           every existing run with a nullary integer unknown (refinement
           types, games, CHC) proposes the same templates as before the [Real]
           instance existed; only [MakeReal] takes this arm. *)
        inner
          (increase_expr_const config.bounds.expr.const.unbounded_above
             param_actions)
          labels
    | (ExprCondConjDepthExt | Shape) :: labels ->
        inner
          (if config.fix_shape then increase_depth_ext param_actions
           else increase_expr_cond_conj param_actions)
          labels
    | ExprCoeff :: labels ->
        inner
          (increase_expr_coeff config.bounds.expr.coeff.unbounded_above param_actions)
          labels
    | ExprConst :: labels ->
        inner
          (increase_expr_const config.bounds.expr.const.unbounded_above param_actions)
          labels
    | CondCoeff :: labels ->
        inner
          (increase_cond_coeff config.bounds.cond.coeff.unbounded_above param_actions)
          labels
    | CondConst :: labels ->
        inner
          (increase_cond_const config.bounds.cond.const.unbounded_above param_actions)
          labels
    | QualDep :: labels -> inner param_actions labels
    | TimeOut :: _labels -> param_actions (* z3 may unexpectedly time out*)
    | _ ->
        (* another template module's label: excluded by the contract of
           [Function.Type.update_with_labels] *)
        assert false

  let coeff_labels = [ ExprCoeff; CondCoeff ]
  let const_labels = [ ExprConst; CondConst ]

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

module Make = MakeOfSort (struct
  let kind = Kind.IntFun
  let sort = T_int.SInt
end)

module MakeReal = MakeOfSort (struct
  let kind = Kind.RealFun
  let sort = T_real.SReal
end)
