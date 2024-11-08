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
    number_of_disj : int;
    number_of_conj : int;
    incr_interval : int;
    depth : int;
    upper_bound_coeff : int option;
    upper_bound_const : int option;
    seeds : int list option;
    bound_each_coeff : int option;
    threshold_coeff : int option;
    threshold_const : int option;
    disj_first : bool;
    fix_shape : bool;
    eq_atom : bool;
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
            @@ sprintf "Invalid PredicateDNF Configuration (%s): %s" filename
                 msg)
end

module type ArgType = sig
  val name : Ident.tvar
  val sorts : Sort.t list
  val fenv : LogicOld.FunEnv.t
  val sol_space : SolSpace.t
  val id : int option
end

type parameter = {
  nd : int;
  nc : int;
  depth : int;
  ubc : Z.t option;
  ubd : Z.t option;
  s : Z.t Set.Poly.t;
}

type parameter_update_type += DepthDisjConj | Coeff | Const | Qual

type state =
  int * int * int * int option * int option * bool * bool * bool * bool * bool
[@@deriving to_yojson]

let state_of param labels : state =
  ( param.nd,
    param.nc,
    param.depth,
    Option.map ~f:Z.to_int param.ubc,
    Option.map ~f:Z.to_int param.ubd,
    Set.mem labels DepthDisjConj (* ToDo: this is always true *),
    Set.mem labels Coeff,
    Set.mem labels Const,
    Set.mem labels Qual (* ToDo: this is always true *),
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
        nd = config.number_of_disj;
        nc = config.number_of_conj;
        depth = config.depth;
        ubc = Option.map config.upper_bound_coeff ~f:Z.of_int;
        ubd = Option.map config.upper_bound_const ~f:Z.of_int;
        s =
          (match config.seeds with
          | None -> Set.Poly.singleton Z.zero
          | Some s -> Set.Poly.of_list @@ List.map s ~f:Z.of_int);
      }

  let init =
    {
      nd = 1;
      nc = 1;
      depth = 0;
      ubc = Some Z.one;
      ubd = Some Z.zero;
      s = Set.Poly.singleton Z.zero;
    }

  let name_of () = Arg.name
  let kind_of () = Kind.str_of Kind.Ord
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
      ("number of disjuncts (max: %s) : %d\n"
     ^^ "number of conjuncts (max: %s) : %d\n" ^^ "depth (max: %s) : %d\n"
     ^^ "upper bound of the sum of the abs of coefficients : %s\n"
     ^^ "upper bound of the sum of the abs of constant : %s\n" ^^ "seeds : %s")
      (SolSpace.str_of_tvar_and_flag Arg.name SolSpace.ND Arg.sol_space)
      !param.nd
      (SolSpace.str_of_tvar_and_flag Arg.name SolSpace.NC Arg.sol_space)
      !param.nc
      (SolSpace.str_of_tvar_and_flag Arg.name SolSpace.Depth Arg.sol_space)
      !param.depth
      (match !param.ubc with None -> "N/A" | Some ubc -> Z.to_string ubc)
      (match !param.ubd with None -> "N/A" | Some ubd -> Z.to_string ubd)
      (String.concat_set ~sep:"," @@ Set.Poly.map !param.s ~f:Z.to_string)

  let in_space () =
    SolSpace.in_space Arg.name SolSpace.ND !param.nd Arg.sol_space
    && SolSpace.in_space Arg.name SolSpace.NC !param.nc Arg.sol_space
    && SolSpace.in_space Arg.name SolSpace.Depth !param.depth Arg.sol_space

  let adjust_quals ~tag quals =
    ignore tag;
    quals

  let init_quals _ _ = ()

  let update_hspace ~tag hspace =
    ignore tag;
    Qualifier.AllTheory.qualifiers_of ~fenv:Arg.fenv ~add_mod2_quals:true
      !param.depth hspace

  let gen_template ~tag ~ucore hspace =
    ignore tag;
    ignore ucore;
    let ( temp_params,
          hole_qualifiers_map,
          tmpl,
          cnstr_of_coeffs,
          cnstr_of_consts,
          cnstr_of_quals ) =
      let terms =
        List.map ~f:(fun t -> (t, Term.sort_of t (*ToDo*)))
        @@ Set.to_list hspace.terms
      in
      let quals = Set.to_list hspace.quals in
      Generator.gen_dnf ~eq_atom:config.eq_atom ~terms ~quals
        ( List.init !param.nd ~f:(fun _ -> !param.nc),
          !param.ubc,
          !param.ubd,
          !param.s )
        (Option.map config.bound_each_coeff ~f:Z.of_int)
        hspace.params
    in
    Debug.print
    @@ lazy
         (sprintf "[%s] predicate template:\n  %s"
            (Ident.name_of_tvar Arg.name)
            (Formula.str_of tmpl));
    Debug.print
    @@ lazy
         (sprintf "[%s] cnstr_of_coeffs:\n  %s"
            (Ident.name_of_tvar Arg.name)
            (Formula.str_of cnstr_of_coeffs));
    Debug.print
    @@ lazy
         (sprintf "[%s] cnstr_of_consts:\n  %s"
            (Ident.name_of_tvar Arg.name)
            (Formula.str_of cnstr_of_consts));
    Debug.print
    @@ lazy
         (sprintf "[%s] cnstr_of_qualifiers:\n  %s"
            (Ident.name_of_tvar Arg.name)
            (Formula.str_of cnstr_of_quals));
    (*Debug.print @@ lazy
      ("qdeps:\n" ^ String.concat_map_list ~sep:"\n" qdeps ~f:PCSatCommon.QDep.str_of);*)
    let qual_qdeps_env = Generator.qual_env_of_hole_map hole_qualifiers_map in
    let tmpl =
      Logic.(
        Term.mk_lambda (of_old_sort_env_list  hspace.params))
      @@ Logic.ExtTerm.of_old_formula tmpl
    in
    ( (DepthDisjConj, tmpl),
      [
        (Coeff, Logic.ExtTerm.of_old_formula cnstr_of_coeffs);
        (Const, Logic.ExtTerm.of_old_formula cnstr_of_consts);
        (Qual, Logic.ExtTerm.of_old_formula cnstr_of_quals);
      ]
      @ qdep_constr_of_envs hspace.qdeps qual_qdeps_env,
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

  let increase_disj (param, actions) =
    Debug.print
    @@ lazy
         ("************* increasing number_of_disj of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with nd = param.nd + 1 }, actions @ [ "increase_disj" ])

  let decrease_disj (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing number_of_disj of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with nd = max (param.nd - 1) 0 }, actions @ [ "decrease_disj" ])

  let init_disj (param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing number_of_disj of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with nd = init.nd }, actions @ [ "init_disj" ])

  let increase_conj (param, actions) =
    Debug.print
    @@ lazy
         ("************* increasing number_of_conj of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with nc = param.nc + 1 }, actions @ [ "increase_conj" ])

  let decrease_conj (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing number_of_conj of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with nc = max (param.nc - 1) 0 }, actions @ [ "decrease_conj" ])

  let init_conj (param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing number_of_conj of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with nc = init.nc }, actions @ [ "init_conj" ])

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

  let set_inf_coeff (param, actions) =
    Debug.print
    @@ lazy
         ("************* setting upper_bound_coeff of "
         ^ Ident.name_of_tvar Arg.name
         ^ " to infinity ***************");
    ({ param with ubc = None }, actions @ [ "set_inf_coeff" ])

  let increase_coeff threshold (param, actions) =
    match (param.ubc, threshold) with
    | Some ubc, Some thr when Z.Compare.(ubc >= Z.of_int thr) ->
        set_inf_coeff (param, actions)
    | _, _ ->
        Debug.print
        @@ lazy
             ("************* increasing upper_bound_coeff of "
             ^ Ident.name_of_tvar Arg.name
             ^ "***************");
        ( { param with ubc = Option.map param.ubc ~f:(fun ubc -> Z.(ubc + one)) },
          actions @ [ "increase_coeff" ] )

  let decrease_coeff (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing upper_bound_coeff of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ( {
        param with
        ubc = Option.map param.ubc ~f:(fun ubc -> Z.(max (ubc - one) zero));
      },
      actions @ [ "decrease_coeff" ] )

  let init_coeff (param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing upper_bound_coeff of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with ubc = init.ubc }, actions @ [ "init_coeff" ])

  let set_inf_const (param, actions) =
    Debug.print
    @@ lazy
         ("************* setting upper_bound_const of "
         ^ Ident.name_of_tvar Arg.name
         ^ " to infinity ***************");
    ({ param with ubd = None }, actions @ [ "set_inf_const" ])

  let increase_const threshold (param, actions) =
    match (param.ubd, threshold) with
    | Some ubd, Some thr when Z.Compare.(ubd >= Z.of_int thr) ->
        set_inf_const (param, actions)
    | _, _ ->
        Debug.print
        @@ lazy
             ("************* increasing upper_bound_const of "
             ^ Ident.name_of_tvar Arg.name
             ^ "***************");
        ( { param with ubd = Option.map param.ubd ~f:(fun ubd -> Z.(ubd + one)) },
          actions @ [ "increase_const" ] )

  let decrease_const (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing upper_bound_const of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ( {
        param with
        ubd = Option.map param.ubd ~f:(fun ubd -> Z.(max (ubd - one) zero));
      },
      actions @ [ "decrease_const" ] )

  let init_const (param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing upper_bound_const of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with ubd = init.ubd }, actions @ [ "init_const" ])

  let try_then f g =
    let res = f () in
    let backup = !param in
    param := fst res;
    if in_space () then (
      param := backup;
      res)
    else g ()

  let increase_depth_disj_conj (param0, actions) =
    let f, g =
      if config.disj_first then
        ( (fun () -> increase_disj (param0, actions)),
          fun () -> increase_conj (param0, actions) )
      else
        ( (fun () -> increase_conj (param0, actions)),
          fun () -> increase_disj (param0, actions) )
    in
    if
      List.exists Arg.sorts ~f:(fun s ->
          Term.is_dt_sort s || Term.is_array_sort s)
      && param0.nd * param0.nc > Integer.pow (param0.depth + 1) 3
    then
      (*ToDo: try_then*)
      increase_depth @@ init_conj @@ init_disj (param0, actions)
    else if
      (param0.nd + param0.nc - 2) mod config.incr_interval
      < config.incr_interval - 1
    then try_then f g
    else try_then g f

  let rec inner param_actions = function
    | [] -> param_actions
    | DepthDisjConj :: labels ->
        inner
          (if config.fix_shape then param_actions
           else increase_depth_disj_conj param_actions)
          labels
    | Coeff :: labels ->
        inner (increase_coeff config.threshold_coeff param_actions) labels
    | Const :: labels ->
        inner (increase_const config.threshold_const param_actions) labels
    | Qual :: labels -> inner param_actions (*ToDo*) labels
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
      | "increase_conj" -> action (increase_conj param_actions)
      | "decrease_conj" -> action (decrease_conj param_actions)
      | "init_conj" -> action (init_conj param_actions)
      | "increase_disj" -> action (increase_disj param_actions)
      | "decrease_disj" -> action (decrease_disj param_actions)
      | "init_disj" -> action (init_disj param_actions)
      | "increase_depth" -> action (increase_depth param_actions)
      | "decrease_depth" -> action (decrease_depth param_actions)
      | "init_depth" -> action (init_depth param_actions)
      | "set_inf_coeff" -> action (set_inf_coeff param_actions)
      | "increase_coeff" -> action (increase_coeff None param_actions)
      | "decrease_coeff" -> action (decrease_coeff param_actions)
      | "init_coeff" -> action (init_coeff param_actions)
      | "set_inf_const" -> action (set_inf_const param_actions)
      | "increase_const" -> action (increase_const None param_actions)
      | "decrease_const" -> action (decrease_const param_actions)
      | "init_const" -> action (init_const param_actions)
      | "restart" -> action (restart param_actions)
      | "revert" -> action (revert param_actions)
      | "end" -> fst param_actions
      | s -> failwith ("Unknown action: " ^ s)
    in
    param := action (!param, [])

  let restart () = param := fst @@ restart (!param, [])
  let update_with_solution _ = failwith "not implemented"

  (*let open Formula in
    let dnf = Evaluator.simplify phi |> nnf_of |> dnf_of (*ToDo*)Map.Poly.empty in
    let nd = Set.length dnf in
    let extract_phi =
    Set.Poly.map dnf ~f:(fun (ps, ns, phi) ->
        assert (Set.is_empty ps && Set.is_empty ns);
        Formula.conjuncts_of phi |> Set.Poly.map ~f:Evaluator.simplify)
    in
    let (_, _, _, _, _, s) = !param in
    let nc, ubc, ubd = Set.fold ~init:(0, Z.zero, Z.zero) extract_phi ~f:(fun (nc, ubc, ubd) phis ->
      let get_coeff_abs_sum seed term = let open Term in
        let rec get_coeff_abs_sum_aux ~ex seed term =
          match Normalizer.normalize_term term with
          | Var (var, _, _) -> begin match Map.Poly.find ex var with | Some i -> i | None -> Z.one end
          | FunApp (funsym, terms, _) ->
            (match funsym, terms with
             | T_int.Int n, [] -> Z.(abs @@ n - seed)
             | T_int.Add, [t1; t2] -> Z.(get_coeff_abs_sum_aux ~ex seed t1 + get_coeff_abs_sum_aux ~ex seed t2)
             | T_int.Mult, [t1; t2] -> Z.(get_coeff_abs_sum_aux ~ex seed t1 * get_coeff_abs_sum_aux ~ex seed t2)
             | T_int.Neg, [t] -> get_coeff_abs_sum_aux ~ex seed t
             | T_int.Div, _ | T_int.Mod, _ (* ignore these int symbols *)
             | T_bool.Formula _, _ -> Z.one (** ToDo *)
             | _ -> assert false)
          | LetTerm(var, _, def, body, _) ->
            let def_sum = get_coeff_abs_sum_aux ~ex seed def in
            get_coeff_abs_sum_aux ~ex:(Map.Poly.set ~key:var ~data:def_sum ex) seed body
        in get_coeff_abs_sum_aux seed term ~ex:Map.Poly.empty
      in
      let rec update_value (nc, ubc, ubd) = function
        | UnaryOp (Not, phi, _)-> update_value (nc, ubc, ubd) phi
        | Atom (atom, _) -> (match Normalizer.normalize_atom atom with
            (* a = b -> a >= b && -a >= -b *)
            | Atom.App (pred, [t1; t2], _) -> begin
                if Term.is_bool_sort @@ Term.sort_of t1 then (
                  assert (Stdlib.(=) pred (Predicate.Psym T_bool.Eq) ||
                          Stdlib.(=) pred (Predicate.Psym T_bool.Neq));
                  let term_is_bool_terminal = function
                    | Term.FunApp (T_bool.Formula (Formula.Atom (atom, _)), [], _) ->
                      Atom.is_true atom || Atom.is_false atom
                    | _ -> false
                  in
                  List.fold [t1; t2] ~init:(nc, ubc, ubd) ~f:(fun (nc, ubc, ubd) term ->
                      if term_is_bool_terminal term then nc, ubc, ubd
                      else match term with
                        | Var _ -> nc, ubc, ubd
                        | FunApp (T_bool.Formula phi, _, _) -> update_value (nc, ubc, ubd) phi
                        | _ -> assert false))
                else
                  let ubc = Z.(max ubc @@ get_coeff_abs_sum Z.zero t1) in
                  let ubd' =
                    Set.Poly.map s ~f:(fun n -> get_coeff_abs_sum n t2)
                    |> Set.min_elt_exn
                  in
                  if Stdlib.(=) pred (Predicate.Psym T_bool.Eq) ||
                     Stdlib.(=) pred (Predicate.Psym T_bool.Neq) then
                    nc + 2, ubc, Z.(max ubd ubd')
                  else nc + 1, ubc, Z.(max ubd @@ ubd' + of_int 1)
              end
            | Atom.True _ | Atom.False _ -> nc, ubc, ubd
            | _ -> assert false)
        | _ -> assert false
      in
      let (nc', ubc', ubd') = Set.fold ~init:(0, Z.zero, Z.zero) phis ~f:update_value in
      max nc nc', Z.(max ubc ubc'), Z.(max ubd ubd'))
    in
    let (nd', nc', depth', ubc', ubd', s) = !param in
    let param' =
    (if (nc = 0 || nd = 0) then (1, 1, Z.zero, Z.one) (* just true or false *)
     else (nd, nc, ubc, ubd))
    |> fun (nd, nc, ubc, ubd) ->
    max nd nd', max nc nc', depth', Option.map ~f:(Z.max ubc) ubc', Option.map ~f:(Z.max ubd) ubd',
    s
    in
    param := param'*)
  let sync _thre = assert false
  (*let mx = max nd nc
           |> max @@ Z.to_int (match ubc with None -> Z.zero | Some n -> n)
           |> max @@ Z.to_int (match ubd with None -> Z.zero | Some n -> n) in
    let mn = mx - thre in
    let param' = (max nd mn), (max nc mn), depth,
               Option.map ubc ~f:(Z.max (Z.of_int mn)),
               Option.map ubd ~f:(Z.max (Z.of_int mn)),
               s in
    param := param'*)

  let _ =
    Debug.print
    @@ lazy
         (sprintf "************* initializing %s ***************"
            (Ident.name_of_tvar Arg.name));
    Debug.print @@ lazy (str_of ())
end
