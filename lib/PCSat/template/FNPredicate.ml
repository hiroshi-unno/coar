(* Template for a functional predicate [FN(x, r)] -- one that holds of exactly
   one result [r] for each argument [x] -- and, through [MakeTot], for a total
   predicate over a given set of argument positions.

   The template is the graph [r = f(x)] of a guarded piecewise term: an
   if-then-else chain over [number_of_expr] expressions whose guards have
   [number_of_cond_conj] conjuncts, ending in an unguarded branch, the
   expressions affine over the arguments and the hypothesis space's terms
   with bounded coefficients (or, for a sequence result with
   [seq_result = Candidates _], a choice among bounded constructions).
   Since the term denotes a value everywhere, every instance is single-valued
   and total by construction, which is what makes the kind sound without a
   separate check.  Shape, depth and bounds
   grow from the labels of an unsat core as in the other templates. *)
open Core
open Common
open Common.Ext
open Common.Util
open Ast
open Ast.LogicOld
open Function

module Config = struct
  (** The bounds of the candidate results of a sequence-valued unknown's
      template (see [Templ.seq_candidates]). *)
  type seq_candidates = {
    concat_depth : int; [@default 1]
        (** concatenations a candidate result may contain *)
    max_candidates : int; [@default 24]
        (** length of each part of the candidate result list: the atoms, and
            the concatenations *)
    selector_depth : int; [@default 2]
        (** selector chains through single-constructor datatype arguments *)
    prefixes : bool; [@default false]
        (** also offer [seq.extract s 0 n] at integer arguments [n] *)
    length_cuts : bool; [@default false]
        (** also offer the prefix and the suffix of each sequence atom of the
            length of another sequence argument *)
  }
  [@@deriving yojson]

  (** Whether an unknown whose result sort is a sequence gets a template:
      [Off], the template is refused (answered [unknown]); [Candidates], an
      [ite] chain choosing among candidate results built from the arguments
      under learned conditions. *)
  type seq_result = Off | Candidates of seq_candidates [@@deriving yojson]

  (** Which argument tuples a function a reconstruction pass added is applied
      to in the hypothesis space of a functional unknown: [All_tuples], every
      tuple of reached terms of its argument sorts (a product, about 24^3
      terms for a function of three integers over two dozen arguments);
      [Clause_call_sites], only the tuples the clauses that mention the
      unknown pass to the function's own unknown (see
      [call_site_tuples]). *)
  type reconstructed_fun_apps = All_tuples | Clause_call_sites
  [@@deriving yojson]

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
    verbose : bool; [@default true]
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
    fix_shape : bool; [@default true]
    fix_depth_ext : bool; [@default false]
    fix_upper_bound : bool; [@default false]
    seq_result : seq_result; [@default Off]
        (** the template for an unknown whose result sort is a sequence (see
            [seq_result]) *)
    reconstructed_fun_apps : reconstructed_fun_apps; [@default All_tuples]
        (** see [reconstructed_fun_apps] *)
    skip_non_numeric_result_qelim : bool; [@default false]
        (** a qualifier that mentions the result, when the result sort is
            not an integer, a real or a bit-vector, is dropped from the
            initial qualifiers instead of being handed to quantifier
            elimination over the result.  Not exact in general: an
            elimination that removes the binder (an equation [r = t] by the
            one-point rule) gives a qualifier over the arguments, which this
            drops. *)
    fn_linear_part_own_args_only : bool; [@default false]
        (** the affine part of an integer, real or bit-vector result's
            template has coefficients on the unknown's own numeric arguments
            only, and the hypothesis-space terms are offered by the selector
            alone ([Templ.gen_irb_fun] says what is lost: [-t] and sums of
            terms).  One coefficient per term and a bound on the sum of their
            absolute values made the synthesis query undecidable by Z3 within
            its budget once there are thousands of terms.  A restriction of
            the candidates only, so not a soundness matter. *)
    record_result_leaf_depth : int option; [@default None]
        (** [Some d]: when the result sort is a record of integers -- built
            only from single-constructor datatypes, at most [d] constructors
            deep, over integer leaves (a tuple, a mutable reference's pair of
            current and final values, nestings of these) -- also offer as a
            candidate result that record with every leaf an affine expression
            over the integer arguments and the integer leaves of the
            arguments reached through at most [d] selectors
            ([Templ.gen_dt_fun]).  Without it a datatype-sorted result is
            chosen among the arguments and constructor terms over them, which
            cannot express a modified copy of an argument, such as the state
            of a closure after one more call.  [None]: not offered.  A
            widening of the candidates only, so not a soundness matter. *)
    exact_affine_coefficient : bool; [@default false]
        (** when a qualifier is solved for the unknown's result to give a
            candidate result term, read the result's coefficient exactly
            ([AffineTerm.exact_coeff_of]).  Off, the coefficient is taken to
            be 1 whatever it is, so a qualifier [-1 + y - r = 0] offers
            [1 - y] (not a root) and one with coefficient 2 or more offers a
            term too; on, only roots are offered and a qualifier whose
            coefficient is not 1 or -1 offers none.  Changes the candidate
            terms, so the search, on every path that reads qualifiers. *)
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
    let name = "FNPredicate"
    let instantiate = instantiate_ext_files
  end)
end

module type ArgType = sig
  val name : Ident.tvar
  val sorts : Sort.t list
  val fenv : LogicOld.FunEnv.t
  val sol_space : SolSpace.t
  val id : int option

  val problem_clauses : ClauseOld.t list Lazy.t
  (** the problem's clauses, read only under [Clause_call_sites] *)
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

(* What the template is for.  [total = None] is a functional predicate, whose
   last argument is the result.  [total = Some (universal, relation)] is a
   total predicate over the [universal] positions whose template is the graph
   of a function of those positions, one guarded piecewise term per remaining
   position, widened by a DNF relation when [relation] holds
   ([Templ.gen_tot_fun_predicate], which says why every member is total).  The
   shape parameters, their bounds and the labels that move them are the
   functional template's in both cases. *)
(* The template of a functional predicate [FN(x, r)]: the graph [r = f(x)] of
   [Templ.gen_fun]'s guarded piecewise term, as [Templ.gen_fn_predicate]
   builds it, except that when the result [r] is [Real] each affine part's
   constant is a [Real]-sorted parameter ([Templ.gen_fun ~real_const]) rather
   than [int_to_real] of an integer one.  Without that, and with integer
   coefficients over the arguments, every member denotes an integer
   combination of the arguments and the integer-valued terms, so a witness
   that has to be a non-integer rational -- the skolem of [exists r:real.
   r + r = 1 /\ ..], whose only witness is 1/2 -- lies outside the hypothesis
   space at every bound: the template refutes a satisfiable problem, or the
   loop searches forever.  The constant's bound is the integer one's,
   [|c - s| <= ubed] for a seed [s], so at [ubed = 0] the space is unchanged
   and every later bound only adds members.  The argument coefficients stay
   integers, so [r = x / 2] is still outside; a real-sorted field of a
   datatype or tuple result is not covered either ([gen_dt_fun] does not take
   [real_const]).  Single-valuedness and totality are [gen_fun]'s and do not
   depend on the constant's sort. *)
let gen_fn_predicate ?linear_own_args_only ?record_leaf_depth ~print
    ~ignore_bool ?seq_result tf_params tf_sub_params params :
    Templ.templ_func_pred =
  let args, (xret, sret) = List.rest_last params in
  let templ =
    Templ.gen_fun ?linear_own_args_only ?record_leaf_depth
      ~real_const:(Term.is_real_sort sret) ~print ~ignore_bool ?seq_result
      tf_params tf_sub_params args (Some xret, sret)
  in
  {
    templ_params = templ.templ_params;
    hole_quals_map = templ.hole_quals_map;
    pred = Formula.eq (Term.mk_var xret sret) templ.func;
    expr_selectors_bounds = templ.expr_selectors_bounds;
    expr_coeffs_bounds = templ.expr_coeffs_bounds;
    expr_const_bounds = templ.expr_const_bounds;
    cond_coeffs_bounds = templ.cond_coeffs_bounds;
    cond_const_bounds = templ.cond_const_bounds;
  }

module type WitnessType = sig
  val kind : Kind.t
  val total : (int list * bool) option
end

module MakeGen (Cfg : Config.ConfigType) (Arg : ArgType) (W : WitnessType) :
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
    {
      nd = (if config.fix_shape then config.number_of_expr else 1);
      nc = (if config.fix_shape then config.number_of_cond_conj else 1);
      depth = (if config.fix_depth_ext then config.term_depth else 0);
      ext = (if config.fix_depth_ext then config.extra_terms else 0);
      ubec =
        (if config.fix_upper_bound then
           Option.map ~f:Z.of_int config.bounds.expr.coeff.initial
         else Some Z.one);
      ubed =
        (if config.fix_upper_bound then
           Option.map ~f:Z.of_int config.bounds.expr.const.initial
         else Some Z.zero);
      es = Set.Poly.singleton Z.zero;
      ubcc =
        (if config.fix_upper_bound then
           Option.map ~f:Z.of_int config.bounds.cond.coeff.initial
         else Some Z.one);
      ubcd =
        (if config.fix_upper_bound then
           Option.map ~f:Z.of_int config.bounds.cond.const.initial
         else Some Z.zero);
      cs = Set.Poly.singleton Z.zero;
    }

  let name_of () = Arg.name
  let kind_of () = Kind.str_of W.kind
  let kind = W.kind
  let flexible = false
  let sort_of () = Sort.mk_fun @@ Arg.sorts @ [ T_bool.SBool ]
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
      (String.concat_map_set ~sep:"," !param.es ~f:Z.to_string)
      (match !param.ubcc with None -> "N/A" | Some ubcc -> Z.to_string ubcc)
      (match !param.ubcd with None -> "N/A" | Some ubcd -> Z.to_string ubcd)
      (String.concat_map_set ~sep:"," !param.cs ~f:Z.to_string)

  let in_space () =
    SolSpace.in_space Arg.name SolSpace.ND !param.nd Arg.sol_space
    && SolSpace.in_space Arg.name SolSpace.NC !param.nc Arg.sol_space
    && SolSpace.in_space Arg.name SolSpace.Depth !param.depth Arg.sol_space

  let adjust_quals_terms (quals, terms) =
    let params = params_of () in
    let quals', terms' =
      Qual.extract_terms_from_quals
        ~skip_non_numeric:config.skip_non_numeric_result_qelim
        ~exact_affine_coeff:config.exact_affine_coefficient
        ~qelim:(Z3Smt.Z3interface.qelim ~id ~fenv:Arg.fenv)
        params quals
    in
    (* a functional predicate's result is not an input of its own term, so no
       term may mention it; a total one's witness terms are cut down to the
       arguments each may read by the template itself *)
    ( quals',
      Set.union terms'
        (Templ.terms_over_set terms
           (if Option.is_none W.total then List.drop_last_exn params
            else params)) )

  (* [call_site_tuples params] maps each function [f] a reconstruction pass
     added for an unknown [rho] (named [recon_<rho>_...]) to the argument
     tuples, over [params], at which a clause mentioning this unknown applies
     [rho]: in each clause with an atom [this(a_1 .. a_n)], every argument
     [a_j] that is a variable is renamed to the parameter [params_j], and each
     atom [rho(u_1 .. u_k, ..)] of that clause gives the tuple
     [(u_1 .. u_k)] renamed, provided every variable of it was renamed (a
     tuple over the clause's other variables says nothing about the
     arguments).  [f]'s first [k] arguments are [rho]'s, its result [rho]'s
     last.  Every other function maps to [None] (all tuples).  The tuples are
     well-sorted: renaming keeps sorts and [rho]'s argument sorts are [f]'s. *)
  let call_site_tuples params =
    let reconstructed = Atomic.get PCSP.Problem.reconstructed_functions in
    let fun_of_rho =
      Map.Poly.filter_keys Arg.fenv ~f:(Set.mem reconstructed)
      |> Map.Poly.to_alist
    in
    let me = Ident.name_of_tvar Arg.name in
    let found = Hashtbl.Poly.create () in
    List.iter (Lazy.force Arg.problem_clauses) ~f:(fun (_, ps, ns, _) ->
        let atoms = Set.to_list (Set.union ps ns) in
        let apps =
          List.filter_map atoms ~f:(function
            | Atom.App (Predicate.Var (p, _), args, _) ->
                Some (Ident.name_of_pvar p, args)
            | _ -> None)
        in
        List.iter apps ~f:(fun (p, args) ->
            if String.equal p me && List.length args = List.length params then
              let ren =
                Map.Poly.of_alist_reduce ~f:(fun a _ -> a)
                @@ List.filter_map (List.zip_exn args params)
                     ~f:(fun (a, (x, s)) ->
                       match a with
                       | Term.Var (v, _, _) -> Some (v, Term.mk_var x s)
                       | _ -> None)
              in
              List.iter apps ~f:(fun (rho, rargs) ->
                  List.iter fun_of_rho ~f:(fun (f, (fargs, _, _, _, _)) ->
                      let k = List.length fargs in
                      if
                        String.is_prefix (Ident.name_of_tvar f)
                          ~prefix:("recon_" ^ rho ^ "_")
                        && List.length rargs > k
                      then
                        let us = List.take rargs k in
                        if
                          List.for_all us ~f:(fun u ->
                              Set.for_all (Term.tvs_of u) ~f:(Map.Poly.mem ren))
                        then
                          Hashtbl.add_multi found ~key:f
                            ~data:(List.map us ~f:(Term.subst ren))))));
    fun f ->
      if List.Assoc.mem fun_of_rho ~equal:Stdlib.( = ) f then
        Some
          (List.dedup_and_sort ~compare:Stdlib.compare
             (Hashtbl.find_multi found f))
      else None

  let update_hspace hspace =
    let func_app_tuples =
      match config.reconstructed_fun_apps with
      | All_tuples -> None
      | Clause_call_sites -> Some (call_site_tuples (params_of ()))
    in
    HypSpace.qualifiers_of ?func_app_tuples ~fenv:Arg.fenv !param.depth hspace

  let kind_cert_template () = None

  let gen_template ~ucore:_ (hspace : HypSpace.hspace) =
    let template =
      Function.refuse_without_template @@ fun () ->
      let seq_result =
        match config.seq_result with
        | Off -> None
        | Candidates c ->
            Some
              Templ.
                {
                  seq_concat_depth = c.concat_depth;
                  seq_max_candidates = c.max_candidates;
                  seq_selector_depth = c.selector_depth;
                  seq_prefixes = c.prefixes;
                  seq_length_cuts = c.length_cuts;
                }
      in
      (fun ~print ~ignore_bool tfp tfsp params ->
        match W.total with
        | None ->
            gen_fn_predicate
              ~linear_own_args_only:config.fn_linear_part_own_args_only
              ?record_leaf_depth:config.record_result_leaf_depth ~print
              ~ignore_bool ?seq_result tfp tfsp params
        | Some (universal, relation) ->
            Templ.gen_tot_fun_predicate
              ~linear_own_args_only:config.fn_linear_part_own_args_only
              ?record_leaf_depth:config.record_result_leaf_depth ~print
              ~ignore_bool ~universal ~relation ?seq_result tfp tfsp params)
        ~print:Debug.print ~ignore_bool:(not config.branch_on_bool_args)
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
        hspace.params
    in
    (* let pred =
       Formula.elim_ite template.pred
       |> Evaluator.simplify
       |> Z3Smt.Z3interface.simplify ~id Arg.fenv
       in *)
    Debug.print
    @@ lazy
         (sprintf "[%s] predicate template:\n  %s"
            (Ident.name_of_tvar Arg.name)
            (Formula.str_of template.pred));
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
    let tmpl =
      Logic.(Term.mk_lambda (of_old_sort_env_list hspace.params))
      @@ Logic.ExtTerm.of_old_formula template.pred
    in
    ( (ExprCondConjDepthExt, tmpl),
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
      && param.nd * param.nc > Int.pow (param.depth + 1) 3
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
    | (ExprCondConjDepthExt | Shape) :: labels ->
        inner
          (if config.fix_shape then
             if config.fix_depth_ext then param_actions
             else increase_depth_ext param_actions
           else increase_expr_cond_conj_depth_ext param_actions)
          labels
    | ExprCoeff :: labels ->
        inner
          (if config.fix_upper_bound then param_actions
           else increase_expr_coeff config.bounds.expr.coeff.unbounded_above param_actions)
          labels
    | ExprConst :: labels ->
        inner
          (if config.fix_upper_bound then param_actions
           else increase_expr_const config.bounds.expr.const.unbounded_above param_actions)
          labels
    | CondCoeff :: labels ->
        inner
          (if config.fix_upper_bound then param_actions
           else increase_cond_coeff config.bounds.cond.coeff.unbounded_above param_actions)
          labels
    | CondConst :: labels ->
        inner
          (if config.fix_upper_bound then param_actions
           else increase_cond_const config.bounds.cond.const.unbounded_above param_actions)
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

module Make (Cfg : Config.ConfigType) (Arg : ArgType) : Function.Type =
  MakeGen (Cfg) (Arg)
    (struct
      let kind = Kind.FN
      let total = None
    end)

(* A total predicate over [U.universal] given the functional template's width
   for its witnesses, and with [U.relation] a relation beside them. *)
module MakeTot
    (Cfg : Config.ConfigType)
    (Arg : ArgType)
    (U : sig
      val universal : int list
      val relation : bool
    end) : Function.Type =
  MakeGen (Cfg) (Arg)
    (struct
      let kind = Kind.Tot U.universal
      let total = Some (U.universal, U.relation)
    end)
