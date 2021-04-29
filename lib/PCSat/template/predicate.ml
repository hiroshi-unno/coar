open Core
open Ast
open Ast.LogicOld
open Function

module Config = struct
  type t = {
    verbose: bool;

    number_of_disj: int;
    number_of_conj: int;

    upper_bound_coeff: int option;
    upper_bound_const: int option;
    seeds: int list option;

    bound_each_coeff: int option;
    threshold_coeff: int option;
    threshold_const: int option;

    disj_first: bool;
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
          error_string
          @@ Printf.sprintf
            "Invalid Predicate Configuration (%s): %s" filename msg
      end
    | Common.Util.ExtFile.Instance x -> Ok (Common.Util.ExtFile.Instance x)
end

module type ArgType = sig
  val name  : Ident.tvar
  val sorts : Sort.t list
  val dtenv : LogicOld.DTEnv.t
  val fenv  : (Ident.tvar * (Ident.tvar * Sort.t) list * Sort.t * Term.t * (Formula.t Set.Poly.t)) Core.Set.Poly.t
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
   Set.Poly.mem labels DepthDisjConj,
   Set.Poly.mem labels Coeff,
   Set.Poly.mem labels Const,
   Set.Poly.mem labels Qual,
   Set.Poly.mem labels TimeOut)

module Make (Cfg : Config.ConfigType) (Arg: ArgType) : Function.Type = struct
  let config = Cfg.config

  module Debug =
    Common.Debug.Make
      (val (Common.Debug.Config.(if config.verbose then enable else disable)))

  let param : parameter ref =
    ref (config.number_of_disj, config.number_of_conj, 0,
         (Option.map config.upper_bound_coeff ~f:Z.of_int),
         (Option.map config.upper_bound_const ~f:Z.of_int),
         (match config.seeds with
          | None -> Set.Poly.singleton (Z.of_int 0)
          | Some s -> List.map s ~f:Z.of_int |> Set.Poly.of_list))
  let depth_of (_nd, _nc, depth, _ubc, _ubd, _s) = depth

  let params_of () = SortEnv.of_sorts Arg.sorts
  let adjust_quals quals = quals
  let gen_quals_terms (old_depth, old_quals, old_terms) =
    let params = params_of () in
    let quals, terms = Qualifier.AllTheory.qualifiers_of ~fenv:Arg.fenv !param old_depth params old_quals old_terms in
    (* Debug.print @@ lazy (Set.Poly.fold quals ~init:("generated qualifiers:") ~f:(fun ret phi -> ret ^ "\n" ^ (Formula.str_of phi)));
       Debug.print @@ lazy (Set.Poly.fold terms ~init:("generated terms:") ~f:(fun ret t -> ret ^ "\n" ^ (Term.str_of t))); *)
    (depth_of !param), quals, terms
  let gen_template quals terms =
    let params = params_of () in
    let temp_params, hole_qualifiers_map, tmpl,
        cnstr_of_coeffs, cnstr_of_consts, cnstr_of_quals =
      Generator.gen_dnf
        config.eq_atom
        (List.dedup_and_sort ~compare:Stdlib.compare quals)
        (List.map ~f:(fun t -> t, Term.sort_of t(*ToDo*)) @@
         List.dedup_and_sort ~compare:Stdlib.compare terms)
        !param
        (Option.map config.bound_each_coeff ~f:Z.of_int)
        (SortEnv.list_of params) in
    (*Debug.print @@ lazy ("predicate template:\n  " ^ Formula.str_of tmpl);
      Debug.print @@ lazy ("cnstr_of_coeffs: " ^ (Formula.str_of cnstr_of_coeffs));
      Debug.print @@ lazy ("cnstr_of_consts: " ^ (Formula.str_of cnstr_of_consts));
      Debug.print @@ lazy ("cnstr_of_qualifiers: " ^ (Formula.str_of cnstr_of_quals)); *)
    let tmpl =
      Logic.Term.mk_lambda (Logic.SortEnv.of_old_sort_env Logic.ExtTerm.of_old_sort params) @@
      Logic.ExtTerm.of_old_formula tmpl in
    (DepthDisjConj, tmpl),
    [(Const, cnstr_of_consts |> Logic.ExtTerm.of_old_formula);
     (Coeff, cnstr_of_coeffs |> Logic.ExtTerm.of_old_formula);
     (Qual, cnstr_of_quals |> Logic.ExtTerm.of_old_formula)],
    temp_params, hole_qualifiers_map

  let restart (_nd, _nc, _depth, _ubc, _ubd, _s) =
    Debug.print @@ lazy ("************* restarting " ^ Ident.name_of_tvar Arg.name ^ "***************");
    1, 1, 0, Some Z.one, Some Z.zero, Set.Poly.singleton (Z.of_int 0)

  let last_non_timeout_param = ref !param
  let revert (_nd, _nc, _depth,  _ubc, _ubd, _s) =
    Debug.print @@ lazy ("************* reverting " ^ Ident.name_of_tvar Arg.name ^ "***************");
    !last_non_timeout_param

  let increase_conj (nd, nc, depth, ubc, ubd, s) =
    Debug.print @@ lazy ("************* increasing number_of_conj of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    nd, nc+1, depth, ubc, ubd, s

  let increase_disj (nd, nc, depth, ubc, ubd, s) =
    Debug.print @@ lazy ("************* increasing number_of_disj of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    nd+1, nc, depth, ubc, ubd, s

  let increase_depth_disj_conj (nd, nc, depth, ubc, ubd, s) =
    if List.exists Arg.sorts ~f:(fun s -> Stdlib.(<>) s T_int.SInt && Stdlib.(<>) s T_bool.SBool) && nd * nc > (depth + 1) * (depth + 1) then begin
      Debug.print @@ lazy ("************* partially restarting with depth increased of " ^ Ident.name_of_tvar Arg.name ^ "***************");
      (1, 1, depth + 1, ubc, ubd, s)
    end else if config.disj_first then
      (if (nd + nc) mod 2 = 0 then increase_disj (nd, nc, depth, ubc, ubd, s)
       else increase_conj (nd, nc, depth, ubc, ubd, s))
    else
      (if (nd + nc) mod 2 = 0 then increase_conj (nd, nc, depth, ubc, ubd, s)
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

  let next () = param := !param |> increase_depth_disj_conj |> increase_coeff config.threshold_coeff |> increase_const config.threshold_const

  (* obsolete *)
  let update_with_solution phi =
    let open Formula in
    let dnf = Evaluator.simplify phi |> nnf_of |> dnf_of in
    let nd = Set.Poly.length dnf in
    let extract_phi =
      Set.Poly.map dnf ~f:(fun (ps, ns, phi) ->
          assert (Set.Poly.is_empty ps && Set.Poly.is_empty ns);
          Formula.conjuncts_of phi |> Set.Poly.map ~f:Evaluator.simplify)
    in
    let (_, _, _, _, _, s) = !param in
    let nc, ubc, ubd = Set.Poly.fold ~init:(0, Z.of_int 0, Z.of_int 0) extract_phi ~f:(fun (nc, ubc, ubd) phis ->
        let rec get_coeff_abs_sum seed term = let open Term in
          match Normalizer.normalize_term term with
          | Var _ -> Z.of_int 1
          | FunApp (funsym, terms, _) ->
            (match funsym, terms with
             | T_int.Int n, [] -> Z.(abs @@ n - seed)
             | T_int.Add, [t1; t2] -> Z.(get_coeff_abs_sum seed t1 + get_coeff_abs_sum seed t2)
             | T_int.Mult, [t1; t2] -> Z.(get_coeff_abs_sum seed t1 * get_coeff_abs_sum seed t2)
             | T_int.Neg, [t] -> get_coeff_abs_sum seed t
             | T_int.Div, _ | T_int.Mod, _ (* ignore these int symbols *)
             | T_bool.Formula _, _ -> Z.of_int 1 (** ToDo *)
             | _ -> assert false)
        in
        let rec update_value (nc, ubc, ubd) = function
          | UnaryOp (Not, phi, _)-> update_value (nc, ubc, ubd) phi
          | Atom (atom, _) -> (match Normalizer.normalize_atom atom with
              (* a = b -> a >= b && -a >= -b *)
              | Atom.App (pred, [t1; t2], _) -> begin
                  if Stdlib.(=) (Term.sort_of t1) T_bool.SBool then (
                    assert (Stdlib.(=) pred (Predicate.Psym T_bool.Eq) || Stdlib.(=) pred (Predicate.Psym T_bool.Neq));
                    let term_is_bool_terminal = function
                      | Term.FunApp (T_bool.Formula (Formula.Atom (atom, _)), [], _) -> Atom.is_true atom || Atom.is_false atom
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
                    if Stdlib.(=) pred (Predicate.Psym T_bool.Eq) || Stdlib.(=) pred (Predicate.Psym T_bool.Neq) then
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
      | DepthDisjConj :: labels -> inner (increase_depth_disj_conj param) labels
      | Coeff :: labels -> inner (increase_coeff config.threshold_coeff param) labels
      | Const :: labels -> inner (increase_const config.threshold_const param) labels
      | Qual :: labels -> inner param(*ToDo*) labels
      | TimeOut :: _labels -> param(* z3 may unexpectedly time out*)
      | _ -> assert false
    in
    param := inner !param @@ Set.Poly.to_list labels
  (* called on failure *)
  let rl_action labels =
    if not @@ Set.Poly.mem labels TimeOut then
      last_non_timeout_param := !param;
    Out_channel.print_endline ("state of " ^ Ident.name_of_tvar Arg.name ^ ": " ^ Yojson.Safe.to_string @@ state_to_yojson @@ state_of !param labels);
    Out_channel.flush Out_channel.stdout;
    let rec action param =
      match In_channel.input_line_exn In_channel.stdin with 
      | "increase_conj" -> action (increase_conj param)
      | "increase_disj" -> action (increase_disj param)
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
      ("number of disjuncts : %d\n" ^^
       "number of conjuncts : %d\n" ^^
       "depth : %d\n" ^^
       "upper bound of the sum of the abs of coefficients : %s\n" ^^
       "upper bound of the sum of the abs of constant : %s\n" ^^
       "seeds : %s")
      nd nc depth
      (match ubc with None -> "N/A" | Some ubc -> Z.to_string ubc)
      (match ubd with None -> "N/A" | Some ubd -> Z.to_string ubd)
      (String.concat ~sep:"," @@ Set.Poly.to_list @@ Set.Poly.map s ~f:Z.to_string)

  let _ =
    Debug.print @@ lazy ("************* initializing " ^ Ident.name_of_tvar Arg.name ^ " ***************");
    Debug.print @@ lazy (str_of ())
end