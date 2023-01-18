open Core
open Common
open Common.Ext
open Ast
open Ast.LogicOld
open Function

module Config = struct
  type t = {
    verbose: bool;

    number_of_disj: int;
    number_of_conj: int;
    incr_interval: int;
    depth: int;

    upper_bound_coeff: int option;
    upper_bound_const: int option;
    seeds: int list option;

    bound_each_coeff: int option;
    threshold_coeff: int option;
    threshold_const: int option;

    disj_first: bool;
    fix_shape: bool;
    eq_atom: bool;
  } [@@deriving yojson]

  module type ConfigType = sig val config: t end

  let instantiate_ext_files cfg = Ok cfg

  let load_ext_file = function
    | Common.Util.ExtFile.Filename filename ->
      begin
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename)
        >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x ->
          instantiate_ext_files x >>= fun x ->
          Ok (Common.Util.ExtFile.Instance x)
        | Error msg ->
          error_string @@ Printf.sprintf
            "Invalid PredicateDNF Configuration (%s): %s" filename msg
      end
    | Common.Util.ExtFile.Instance x -> Ok (Common.Util.ExtFile.Instance x)
end

module type ArgType = sig
  val name  : Ident.tvar
  val sorts : Sort.t list
  val dtenv : LogicOld.DTEnv.t
  val fenv  : LogicOld.FunEnv.t
  val sol_space : PCSP.SolSpace.t
  val id    : int option
end

type parameter = int * int * int * Z.t option * Z.t option * Z.t Set.Poly.t
type parameter_update_type +=
  | DepthDisjConj
  | Coeff
  | Const
  | Qual

type state = int * int * int * int option * int option * bool * bool * bool * bool * bool [@@deriving to_yojson]
let state_of ((nd, nc, depth, ubc, ubd, _s) : parameter) labels : state =
  (nd, nc, depth, Option.map ~f:Z.to_int ubc, Option.map ~f:Z.to_int ubd,
   Set.Poly.mem labels DepthDisjConj (* ToDo: this is always true *),
   Set.Poly.mem labels Coeff,
   Set.Poly.mem labels Const,
   Set.Poly.mem labels Qual (* ToDo: this is always true *),
   Set.Poly.mem labels TimeOut)

module Make (Cfg : Config.ConfigType) (Arg: ArgType) : Function.Type = struct
  let config = Cfg.config
  let id = Arg.id

  module Debug = Debug.Make (val (Debug.Config.(if config.verbose then enable else disable)))
  let _ = Debug.set_id id

  let param : parameter ref =
    ref (config.number_of_disj, config.number_of_conj, config.depth,
         (Option.map config.upper_bound_coeff ~f:Z.of_int),
         (Option.map config.upper_bound_const ~f:Z.of_int),
         (match config.seeds with
          | None -> Set.Poly.singleton (Z.of_int 0)
          | Some s -> List.map s ~f:Z.of_int |> Set.Poly.of_list))
  let depth_of (_nd, _nc, depth, _ubc, _ubd, _s) = depth

  let params_of ~tag = ignore tag; sort_env_list_of_sorts Arg.sorts
  let adjust_quals ~tag quals =
    ignore tag;quals
  let init_quals _ _ = ()
  let gen_quals_terms ~tag (old_depth, old_quals, old_qdeps, old_terms) =
    let params = params_of ~tag in
    let depth = depth_of !param in
    let quals, qdeps, terms = Qualifier.AllTheory.qualifiers_of ~add_mod2_quals:true ~fenv:Arg.fenv depth old_depth params old_quals old_qdeps old_terms in
    (* Debug.print @@ lazy (Set.Poly.fold quals ~init:("generated qualifiers:") ~f:(fun ret phi -> ret ^ "\n" ^ (Formula.str_of phi)));
       Debug.print @@ lazy (Set.Poly.fold terms ~init:("generated terms:") ~f:(fun ret t -> ret ^ "\n" ^ (Term.str_of t))); *)
    depth, quals, qdeps, terms
  let gen_template ~tag quals qdeps terms =
    let params = params_of ~tag in
    let temp_params, hole_qualifiers_map, tmpl,
        cnstr_of_coeffs, cnstr_of_consts, cnstr_of_quals =
      let (nd, nc, _depth, ubc, ubd, s) = !param in
      Generator.gen_dnf
        config.eq_atom
        (List.dedup_and_sort ~compare:Stdlib.compare quals)
        (List.map ~f:(fun t -> t, Term.sort_of t(*ToDo*)) @@
         List.dedup_and_sort ~compare:Stdlib.compare terms)
        (List.init nd ~f:(fun _ -> nc), ubc, ubd, s)
        (Option.map config.bound_each_coeff ~f:Z.of_int)
        params in
    Debug.print @@ lazy (sprintf "[%s] predicate template:\n  %s" (Ident.name_of_tvar Arg.name) (Formula.str_of tmpl) );
    Debug.print @@ lazy (sprintf "[%s] quals:\n" (Ident.name_of_tvar @@ Arg.name) ^ String.concat_map_list ~sep:"\n" quals ~f:Formula.str_of);
    Debug.print @@ lazy (sprintf "[%s] cnstr_of_coeffs:\n  %s" (Ident.name_of_tvar Arg.name) (Formula.str_of cnstr_of_coeffs) );
    Debug.print @@ lazy (sprintf "[%s] cnstr_of_coeffs:\n  %s" (Ident.name_of_tvar Arg.name) (Formula.str_of cnstr_of_consts) );
    Debug.print @@ lazy (sprintf "[%s] cnstr_of_qualifiers:\n  %s" (Ident.name_of_tvar Arg.name) (Formula.str_of cnstr_of_quals) );
    (* Debug.print @@ lazy ("ctls:\n" ^ (String.concat_map_list ~sep:"\n" ctls ~f:PCSatCommon.QDep.str_of)); *)
    let qual_ctls_env = Generator.qual_env_of_hole_map hole_qualifiers_map in
    let tmpl =
      Logic.Term.mk_lambda (Logic.of_old_sort_env_list Logic.ExtTerm.of_old_sort params) @@
      Logic.ExtTerm.of_old_formula tmpl in
    (DepthDisjConj, tmpl),
    [(Const, cnstr_of_consts |> Logic.ExtTerm.of_old_formula);
     (Coeff, cnstr_of_coeffs |> Logic.ExtTerm.of_old_formula);
     (Qual, cnstr_of_quals |> Logic.ExtTerm.of_old_formula)]
    @ qdep_constr_of_envs qdeps qual_ctls_env,
    temp_params, hole_qualifiers_map

  let restart (_nd, _nc, _depth, _ubc, _ubd, _s) =
    Debug.print @@ lazy ("************* restarting " ^ Ident.name_of_tvar Arg.name ^ "***************");
    1, 1, 0, Some Z.one, Some Z.zero, Set.Poly.singleton (Z.of_int 0)

  let last_non_timeout_param = ref !param
  let revert (_nd, _nc, _depth, _ubc, _ubd, _s) =
    Debug.print @@ lazy ("************* reverting " ^ Ident.name_of_tvar Arg.name ^ "***************");
    !last_non_timeout_param

  let increase_disj (nd, nc, depth, ubc, ubd, s) =
    Debug.print @@ lazy ("************* increasing number_of_disj of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    nd+1, nc, depth, ubc, ubd, s

  let increase_conj (nd, nc, depth, ubc, ubd, s) =
    Debug.print @@ lazy ("************* increasing number_of_conj of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    nd, nc+1, depth, ubc, ubd, s

  let increase_depth (nd, nc, depth, ubc, ubd, s) =
    Debug.print @@ lazy ("************* increasing depth of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    nd, nc, depth+1, ubc, ubd, s

  let increase_depth_disj_conj (nd, nc, depth, ubc, ubd, s) =
    if
      List.exists Arg.sorts ~f:(fun s -> Fn.non Term.is_int_sort s && Fn.non Term.is_bool_sort s)
      && nd * nc > (depth + 1) * (depth + 1) * (depth + 1)
      && PCSP.SolSpace.in_space (Arg.name) PCSP.SolSpace.Depth depth Arg.sol_space
    then begin
      Debug.print @@ lazy ("************* partially restarting with depth increased " ^ Ident.name_of_tvar Arg.name ^ "***************");
      (1, 1, depth + 1, ubc, ubd, s)
    end else if config.disj_first then
      (if
        ((nd + nc) - 2) mod config.incr_interval < config.incr_interval - 1
        && PCSP.SolSpace.in_space (Arg.name) PCSP.SolSpace.ND depth Arg.sol_space
       then increase_disj (nd, nc, depth, ubc, ubd, s)
       else increase_conj (nd, nc, depth, ubc, ubd, s))
    else
      (if
        ((nd + nc) - 2) mod config.incr_interval < config.incr_interval - 1
        && PCSP.SolSpace.in_space (Arg.name) PCSP.SolSpace.NC depth Arg.sol_space
       then increase_conj (nd, nc, depth, ubc, ubd, s)
       else increase_disj (nd, nc, depth, ubc, ubd, s))

  let increase_coeff threshold (nd, nc, depth, ubc, ubd, s) =
    Debug.print @@ lazy ("************* increasing upper_bound_coeff of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    let ubc' =
      match ubc, threshold with
      | Some ubc, Some thr when Z.Compare.(ubc >= Z.of_int thr) -> None
      | _, _ -> Option.map ubc ~f:(fun ubc -> Z.(+) ubc (Z.of_int 1))
    in
    nd, nc, depth, ubc', ubd, s

  let increase_const threshold (nd, nc, depth, ubc, ubd, s) =
    Debug.print @@ lazy ("************* increasing upper_bound_const of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    let ubd' =
      match ubd, threshold with
      | Some ubd, Some thr when Z.Compare.(ubd >= Z.of_int thr) -> None
      | _, _ -> Option.map ubd ~f:(fun ubd -> Z.(+) ubd (Z.of_int 1))
    in
    nd, nc, depth, ubc, ubd', s

  let set_inf_coeff (nd, nc, depth, _ubc, ubd, s) =
    Debug.print @@ lazy ("************* setting upper_bound_coeff of " ^ Ident.name_of_tvar Arg.name ^ " to infinity ***************");
    let ubc' = None in
    nd, nc, depth, ubc', ubd, s

  let set_inf_const (nd, nc, depth, ubc, _ubd, s) =
    Debug.print @@ lazy ("************* setting upper_bound_const of " ^ Ident.name_of_tvar Arg.name ^ " to infinity ***************");
    let ubd' = None in
    nd, nc, depth, ubc, ubd', s

  let next () = param :=
      !param
      |> (if config.fix_shape then Fn.id else increase_depth_disj_conj)
      |> increase_coeff config.threshold_coeff
      |> increase_const config.threshold_const

  (* obsolete *)
  let update_with_solution phi =
    let open Formula in
    let dnf = Evaluator.simplify phi |> nnf_of |> dnf_of (*ToDo*)Map.Poly.empty in
    let nd = Set.Poly.length dnf in
    let extract_phi =
      Set.Poly.map dnf ~f:(fun (ps, ns, phi) ->
          assert (Set.Poly.is_empty ps && Set.Poly.is_empty ns);
          Formula.conjuncts_of phi |> Set.Poly.map ~f:Evaluator.simplify)
    in
    let (_, _, _, _, _, s) = !param in
    let nc, ubc, ubd = Set.Poly.fold ~init:(0, Z.of_int 0, Z.of_int 0) extract_phi ~f:(fun (nc, ubc, ubd) phis ->
        let get_coeff_abs_sum seed term = let open Term in
          let rec get_coeff_abs_sum_aux ~ex seed term =
            match Normalizer.normalize_term term with
            | Var (var, _, _) -> begin match Map.Poly.find ex var with | Some i -> i | None -> Z.of_int 1 end
            | FunApp (funsym, terms, _) ->
              (match funsym, terms with
               | T_int.Int n, [] -> Z.(abs @@ n - seed)
               | T_int.Add, [t1; t2] -> Z.(get_coeff_abs_sum_aux ~ex seed t1 + get_coeff_abs_sum_aux ~ex seed t2)
               | T_int.Mult, [t1; t2] -> Z.(get_coeff_abs_sum_aux ~ex seed t1 * get_coeff_abs_sum_aux ~ex seed t2)
               | T_int.Neg, [t] -> get_coeff_abs_sum_aux ~ex seed t
               | T_int.Div, _ | T_int.Mod, _ (* ignore these int symbols *)
               | T_bool.Formula _, _ -> Z.of_int 1 (** ToDo *)
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
                    let ubc = Z.(max ubc @@ get_coeff_abs_sum (Z.of_int 0) t1) in
                    let ubd' =
                      Set.Poly.map s ~f:(fun n -> get_coeff_abs_sum n t2)
                      |> Set.Poly.min_elt_exn
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
        let (nc', ubc', ubd') = Set.Poly.fold ~init:(0, Z.of_int 0, Z.of_int 0) phis ~f:update_value in
        max nc nc', Z.(max ubc ubc'), Z.(max ubd ubd'))
    in
    let (nd', nc', depth', ubc', ubd', s) = !param in
    let param' =
      (if (nc = 0 || nd = 0) then (1, 1, Z.of_int 0, Z.of_int 1) (* just true or false *)
       else (nd, nc, ubc, ubd))
      |> fun (nd, nc, ubc, ubd) ->
      max nd nd', max nc nc', depth', Option.map ~f:(Z.max ubc) ubc', Option.map ~f:(Z.max ubd) ubd',
      s
    in
    param := param'
  let update_with_labels labels =
    let rec inner param = function
      | [] -> param
      | DepthDisjConj :: labels -> inner (if config.fix_shape then param else increase_depth_disj_conj param) labels
      | Coeff :: labels -> inner (increase_coeff config.threshold_coeff param) labels
      | Const :: labels -> inner (increase_const config.threshold_const param) labels
      | Qual :: labels -> inner param(*ToDo*) labels
      | QDep :: labels -> inner param labels
      | TimeOut :: _labels -> param(* z3 may unexpectedly time out*)
      | _ -> assert false
    in
    param := inner !param @@ Set.Poly.to_list labels
  let show_state show_num_args labels =
    if show_num_args then
      Out_channel.print_endline (Format.sprintf "#args: %d" (List.length Arg.sorts));
    Out_channel.print_endline ("state of " ^ Ident.name_of_tvar Arg.name ^ ": " ^ Yojson.Safe.to_string @@ state_to_yojson @@ state_of !param labels);
    Out_channel.flush Out_channel.stdout
  (* called on failure, ignore config.fix_shape *)
  let rl_action labels =
    if not @@ Set.Poly.mem labels TimeOut then
      last_non_timeout_param := !param;
    let rec action param =
      match In_channel.input_line_exn In_channel.stdin with
      | "increase_conj" -> action (increase_conj param)
      | "increase_disj" -> action (increase_disj param)
      | "increase_depth" -> action (increase_depth param)
      | "increase_coeff" -> action (increase_coeff None param)
      | "increase_const" -> action (increase_const None param)
      | "set_inf_coeff" -> action (set_inf_coeff param)
      | "set_inf_const" -> action (set_inf_const param)
      | "restart" -> action (restart param)
      | "revert" -> action (revert param)
      | "end" -> param
      | s -> failwith ("Unknown action: " ^ s)
    in
    param := action !param
  let restart () = param := restart !param

  let sync thre =
    let nd, nc, depth, ubc, ubd, s = !param in
    let mx = max nd nc
             |> max @@ Z.to_int (match ubc with None -> Z.zero | Some n -> n)
             |> max @@ Z.to_int (match ubd with None -> Z.zero | Some n -> n) in
    let mn = mx - thre in
    let param' = (max nd mn), (max nc mn), depth,
                 Option.map ubc ~f:(Z.max (Z.of_int mn)),
                 Option.map ubd ~f:(Z.max (Z.of_int mn)),
                 s in
    param := param'

  let str_of () =
    let nd, nc, depth, ubc, ubd, s = !param in
    Printf.sprintf
      ("number of disjuncts (max: %s) : %d\n" ^^
       "number of conjuncts (max: %s) : %d\n" ^^
       "depth (max: %s) : %d\n" ^^
       "upper bound of the sum of the abs of coefficients : %s\n" ^^
       "upper bound of the sum of the abs of constant : %s\n" ^^
       "seeds : %s")
      (PCSP.SolSpace.str_of_tvar_and_flag Arg.name PCSP.SolSpace.ND Arg.sol_space) nd
      (PCSP.SolSpace.str_of_tvar_and_flag Arg.name PCSP.SolSpace.NC Arg.sol_space) nc
      (PCSP.SolSpace.str_of_tvar_and_flag Arg.name PCSP.SolSpace.Depth Arg.sol_space) depth
      (match ubc with None -> "N/A" | Some ubc -> Z.to_string ubc)
      (match ubd with None -> "N/A" | Some ubd -> Z.to_string ubd)
      (String.concat_set ~sep:"," @@ Set.Poly.map s ~f:Z.to_string)

  let _ =
    Debug.print @@ lazy ("************* initializing " ^ Ident.name_of_tvar Arg.name ^ " ***************");
    Debug.print @@ lazy (str_of ())
  let in_space () =
    let nd, nc, depth, _ubc, _ubd, _s = !param in
    PCSP.SolSpace.in_space (Arg.name) PCSP.SolSpace.Depth depth Arg.sol_space
    && PCSP.SolSpace.in_space (Arg.name) PCSP.SolSpace.NC nc Arg.sol_space
    && PCSP.SolSpace.in_space (Arg.name) PCSP.SolSpace.ND nd Arg.sol_space
end