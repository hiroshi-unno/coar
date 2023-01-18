open Core
open Common
open Common.Ext
open Common.Util
open Ast
open Ast.LogicOld
open Function

module Config = struct
  type t = {
    verbose: bool;
    depth: int;
    ext: int;
    shape: int list;
    upper_bound_expr_coeff: int option;
    upper_bound_expr_const: int option;
    expr_seeds: int list option;
    upper_bound_cond_coeff: int option;
    upper_bound_cond_const: int option;
    cond_seeds: int list option;

    max_number_of_cond_conj: int option;
    lower_bound_expr_coeff: int option;
    lower_bound_cond_coeff: int option;
    bound_each_expr_coeff: int option;
    bound_each_cond_coeff: int option;
    threshold_expr_coeff: int option;
    threshold_expr_const: int option;
    threshold_cond_coeff: int option;
    threshold_cond_const: int option;

    ignore_bool: bool;
    fix_shape: bool;
  } [@@deriving yojson]

  module type ConfigType = sig val config: t end

  let instantiate_ext_files cfg = Ok cfg

  let load_ext_file = function
    | ExtFile.Filename filename ->
      begin
        let open Or_error in
        try_with (fun () -> Yojson.Safe.from_file filename)
        >>= fun raw_json ->
        match of_yojson raw_json with
        | Ok x ->
          instantiate_ext_files x >>= fun x ->
          Ok (ExtFile.Instance x)
        | Error msg ->
          error_string @@ Printf.sprintf
            "Invalid FNPredicate Configuration (%s): %s" filename msg
      end
    | Instance x -> Ok (Instance x)
end

module type ArgType = sig
  val name  : Ident.tvar
  val sorts : Sort.t list
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
type parameter = int list * int * int * Z.t option * Z.t option * Z.t Set.Poly.t * Z.t option * Z.t option * Z.t Set.Poly.t
type parameter_update_type +=
  | ExprCondConjDepthExt
  | ExprCoeff
  | ExprConst
  | CondCoeff
  | CondConst

type state = int list * int * int * int option * int option * int option * int option * bool * bool * bool * bool * bool * bool [@@deriving to_yojson]
let state_of ((shp, depth, ext, ubec, ubed, _es, ubcc, ubcd, _cs) : parameter) labels : state =
  (shp, depth, ext, Option.map ~f:Z.to_int ubec, Option.map ~f:Z.to_int ubed, Option.map ~f:Z.to_int ubcc, Option.map ~f:Z.to_int ubcd,
   Set.Poly.mem labels ExprCondConjDepthExt (* ToDo: this is always true *),
   Set.Poly.mem labels ExprCoeff,
   Set.Poly.mem labels ExprConst,
   Set.Poly.mem labels CondCoeff,
   Set.Poly.mem labels CondConst,
   Set.Poly.mem labels TimeOut)

module Make (Cfg : Config.ConfigType) (Arg : ArgType) : Function.Type = struct
  let config = Cfg.config

  let id = Arg.id
  module Debug = Debug.Make (val (Debug.Config.(if config.verbose then enable else disable)))
  let _ = Debug.set_id id

  let param : parameter ref =
    ref (config.shape, config.depth, config.ext,
         (Option.map config.upper_bound_expr_coeff ~f:Z.of_int),
         (Option.map config.upper_bound_expr_const ~f:Z.of_int),
         (match config.expr_seeds with
          | None -> Set.Poly.singleton (Z.of_int 0)
          | Some ds -> List.map ds ~f:Z.of_int |> Set.Poly.of_list),
         (Option.map config.upper_bound_cond_coeff ~f:Z.of_int),
         (Option.map config.upper_bound_cond_const ~f:Z.of_int),
         (match config.cond_seeds with
          | None -> Set.Poly.singleton (Z.of_int 0)
          | Some ds -> List.map ds ~f:Z.of_int |> Set.Poly.of_list))

  let params_of ~tag = ignore tag; sort_env_list_of_sorts Arg.sorts
  let adjust_quals ~tag quals =
    let ret = List.last_exn @@ params_of ~tag in
    let fenv = Map.Poly.empty in (*TODO: generate fenv*)
    Set.Poly.filter_map quals ~f:(fun phi ->
        let qual = Z3Smt.Z3interface.qelim ~id fenv @@ Formula.exists [ret] phi in
        (*ToDo*)if Formula.is_bind qual || Set.Poly.is_empty (Formula.fvs_of qual) then None else Some qual)
  let init_quals _ _ = ()
  let gen_quals_terms ~tag (_old_depth, quals, _qdeps, terms) =
    ignore tag;
    (*TODO: generate quals and terms*)
    0, quals, _qdeps, terms
  let gen_template ~tag quals _qdeps terms =
    let params = params_of ~tag in
    let temp_params, hole_qualifiers_map, tmpl, _,
        cnstr_of_expr_coeffs, cnstr_of_expr_const,
        cnstr_of_cond_coeffs, cnstr_of_cond_const =
      Generator.gen_fn_predicate
        config.ignore_bool
        (List.dedup_and_sort ~compare:Stdlib.compare quals)
        (List.dedup_and_sort ~compare:Stdlib.compare terms)
        !param
        (Option.map config.lower_bound_expr_coeff ~f:Z.of_int,
         Option.map config.lower_bound_cond_coeff ~f:Z.of_int,
         Option.map config.bound_each_expr_coeff ~f:Z.of_int,
         Option.map config.bound_each_cond_coeff ~f:Z.of_int)
        params in
    let tmpl =
      Logic.Term.mk_lambda (Logic.of_old_sort_env_list Logic.ExtTerm.of_old_sort params) @@
      Logic.ExtTerm.of_old_formula tmpl in
    (ExprCondConjDepthExt, tmpl),
    ([(ExprCoeff, cnstr_of_expr_coeffs |> Logic.ExtTerm.of_old_formula);
      (ExprConst, cnstr_of_expr_const |> Logic.ExtTerm.of_old_formula);
      (CondCoeff, cnstr_of_cond_coeffs |> Logic.ExtTerm.of_old_formula);
      (CondConst, cnstr_of_cond_const |> Logic.ExtTerm.of_old_formula)]),
    temp_params, hole_qualifiers_map

  let restart (_shp, _depth, _ext, _ubec, _ubed, _es, _ubcc, _ubcd, _cs) =
    Debug.print @@ lazy ("************* restarting " ^ Ident.name_of_tvar Arg.name ^ "***************");
    [1], 1, 0, Some Z.one, Some Z.zero, Set.Poly.singleton (Z.of_int 0), Some Z.one, Some Z.zero, Set.Poly.singleton (Z.of_int 0)

  let last_non_timeout_param = ref !param
  let revert (_shp, _depth, _ext, _ubec, _ubed, _es, _ubcc, _ubcd, _cs) =
    Debug.print @@ lazy ("************* reverting " ^ Ident.name_of_tvar Arg.name ^ "***************");
    !last_non_timeout_param

  let increase_expr (shp, depth, ext, ubec, ubed, es, ubcc, ubcd, cs) =
    Debug.print @@ lazy ("************* increasing number_of_expr of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    1 :: shp, depth, ext, ubec, ubed, es, ubcc, ubcd, cs

  let increase_cond_conj expr_idx (shp, depth, ext, ubec, ubed, es, ubcc, ubcd, cs) =
    Debug.print @@ lazy ("************* increasing number_of_cond_conj of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    List.mapi shp ~f:(fun i nc -> if i = expr_idx then nc + 1 else nc), depth, ext, ubec, ubed, es, ubcc, ubcd, cs

  let increase_depth (shp, depth, ext, ubec, ubed, es, ubcc, ubcd, cs) =
    Debug.print @@ lazy ("************* partially restarting with depth increased " ^ Ident.name_of_tvar Arg.name ^ "***************");
    (shp, depth + 1, ext, ubec, ubed, es, ubcc, ubcd, cs)

  let increase_ext (shp, depth, ext, ubec, ubed, es, ubcc, ubcd, cs) =
    Debug.print @@ lazy ("************* partially restarting with ext increased " ^ Ident.name_of_tvar Arg.name ^ "***************");
    (shp, depth, ext + 1, ubec, ubed, es, ubcc, ubcd, cs)

  let increase_depth_ext (shp, depth, ext, ubec, ubed, es, ubcc, ubcd, cs) =
    if (depth + ext) mod 2 = 0 then
      increase_depth (shp, depth, ext, ubec, ubed, es, ubcc, ubcd, cs)
    else
      increase_ext (shp, depth, ext, ubec, ubed, es, ubcc, ubcd, cs)

  let increase_expr_cond_conj (shp, depth, ext, ubec, ubed, es, ubcc, ubcd, cs) =
    if
      List.exists Arg.sorts ~f:(fun s -> Fn.non Term.is_int_sort s && Fn.non Term.is_bool_sort s)
      && List.fold shp ~init:1 ~f:( * ) > (depth + 1) * (depth + 1) * (depth + 1)
    then
      increase_depth_ext (shp, depth, ext, ubec, ubed, es, ubcc, ubcd, cs)
    else
      match
        match config.max_number_of_cond_conj with
        | None -> Some (Random.int (List.length shp))
        | Some max -> List.find_mapi shp ~f:(fun idx nc -> if nc >= max then None else Some idx)
      with
      | None -> increase_expr (shp, depth, ext, ubec, ubed, es, ubcc, ubcd, cs)
      | Some idx ->
        if (*ToDo*)(List.length shp + List.sum (module Int) shp ~f:Fn.id) mod 2 = 0 then
          increase_expr (shp, depth, ext, ubec, ubed, es, ubcc, ubcd, cs)
        else
          increase_cond_conj idx(*ToDo*) (shp, depth, ext, ubec, ubed, es, ubcc, ubcd, cs)

  let increase_expr_coeff threshold (shp, depth, ext, ubec, ubed, es, ubcc, ubcd, cs) =
    Debug.print @@ lazy ("************* increasing upper_bound_expr_coeff of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    let ubec' =
      match ubec, threshold with
      | Some ubec, Some thr when Z.Compare.(ubec >= Z.of_int thr) -> None
      | _, _ -> Option.map ubec ~f:(fun ubec -> Z.(+) ubec (Z.of_int 1))
    in
    shp, depth, ext, ubec', ubed, es, ubcc, ubcd, cs

  let increase_expr_const threshold (shp, depth, ext, ubec, ubed, es, ubcc, ubcd, cs) =
    Debug.print @@ lazy ("************* increasing upper_bound_expr_const of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    let ubed' =
      match ubed, threshold with
      | Some ubed, Some thr when Z.Compare.(ubed >= Z.of_int thr) -> None
      | _, _ -> Option.map ubed ~f:(fun ubed -> Z.(+) ubed (Z.of_int 1))
    in
    shp, depth, ext, ubec, ubed', es, ubcc, ubcd, cs

  let increase_cond_coeff threshold (shp, depth, ext, ubec, ubed, es, ubcc, ubcd, cs) =
    Debug.print @@ lazy ("************* increasing upper_bound_cond_coeff of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    let ubcc' =
      match ubcc, threshold with
      | Some ubcc, Some thr when Z.Compare.(ubcc >= Z.of_int thr) -> None
      | _, _ -> Option.map ubcc ~f:(fun ubcc -> Z.(+) ubcc (Z.of_int 1))
    in
    shp, depth, ext, ubec, ubed, es, ubcc', ubcd, cs

  let increase_cond_const threshold (shp, depth, ext, ubec, ubed, es, ubcc, ubcd, cs) =
    Debug.print @@ lazy ("************* increasing upper_bound_cond_const of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    let ubcd' =
      match ubcd, threshold with
      | Some ubcd, Some thr when Z.Compare.(ubcd >= Z.of_int thr) -> None
      | _, _ -> Option.map ubed ~f:(fun ubcd -> Z.(+) ubcd (Z.of_int 1))
    in
    shp, depth, ext, ubec, ubed, es, ubcc, ubcd', cs

  let set_inf_expr_coeff (shp, depth, ext, _ubec, ubed, es, ubcc, ubcd, cs) =
    Debug.print @@ lazy ("************* setting upper_bound_expr_coeff of " ^ Ident.name_of_tvar Arg.name ^ " to infinity ***************");
    let ubec' = None in
    shp, depth, ext, ubec', ubed, es, ubcc, ubcd, cs

  let set_inf_expr_const (shp, depth, ext, ubec, _ubed, es, ubcc, ubcd, cs) =
    Debug.print @@ lazy ("************* setting upper_bound_expr_const of " ^ Ident.name_of_tvar Arg.name ^ " to infinity ***************");
    let ubed' = None in
    shp, depth, ext, ubec, ubed', es, ubcc, ubcd, cs

  let set_inf_cond_coeff (shp, depth, ext, ubec, ubed, es, _ubcc, ubcd, cs) =
    Debug.print @@ lazy ("************* setting upper_bound_cond_coeff of " ^ Ident.name_of_tvar Arg.name ^ " to infinity ***************");
    let ubcc' = None in
    shp, depth, ext, ubec, ubed, es, ubcc', ubcd, cs

  let set_inf_cond_const (shp, depth, ext, ubec, ubed, es, ubcc, _ubcd, cs) =
    Debug.print @@ lazy ("************* setting upper_bound_cond_const of " ^ Ident.name_of_tvar Arg.name ^ " to infinity ***************");
    let ubcd' = None in
    shp, depth, ext, ubec, ubed, es, ubcc, ubcd', cs

  let next () = param :=
      !param
      |> (if config.fix_shape then increase_depth_ext else increase_expr_cond_conj)
      |> increase_expr_coeff config.threshold_expr_coeff
      |> increase_expr_const config.threshold_expr_const
      |> increase_cond_coeff config.threshold_cond_coeff
      |> increase_cond_const config.threshold_cond_const

  let update_with_solution _ = assert false

  let update_with_labels labels =
    let rec inner param = function
      | [] -> param
      | ExprCondConjDepthExt :: labels -> inner (if config.fix_shape then increase_depth_ext param  else increase_expr_cond_conj param) labels
      | ExprCoeff :: labels -> inner (increase_expr_coeff config.threshold_expr_coeff param) labels
      | ExprConst :: labels -> inner (increase_expr_const config.threshold_expr_const param) labels
      | CondCoeff :: labels -> inner (increase_cond_coeff config.threshold_cond_coeff param) labels
      | CondConst :: labels -> inner (increase_cond_const config.threshold_cond_const param) labels
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
      | "increase_expr" -> action (increase_expr param)
      | "increase_expr_coeff" -> action (increase_expr_coeff None param)
      | "increase_expr_const" -> action (increase_expr_const None param)
      | "set_inf_expr_coeff" -> action (set_inf_expr_coeff param)
      | "set_inf_expr_const" -> action (set_inf_expr_const param)
      | "increase_cond_coeff" -> action (increase_cond_coeff None param)
      | "increase_cond_const" -> action (increase_cond_const None param)
      | "set_inf_cond_coeff" -> action (set_inf_cond_coeff param)
      | "set_inf_cond_const" -> action (set_inf_cond_const param)
      | "restart" -> action (restart param)
      | "revert" -> action (revert param)
      | "end" -> param
      | s ->
        let prefix = "increase_cond_conj@" in
        match String.chop_prefix s ~prefix with
        | Some res ->
          action (increase_cond_conj (int_of_string res) param)
        | None -> failwith ("Unknown action: " ^ s)
    in
    param := action !param
  let restart () = param := restart !param

  let sync _thre = ()(*
    let nd, nc, ubec, ubed, es, ubcc, ubcd, cs = !param in
    let mx = max nd nc
             |> max @@ Z.to_int (match ubec with None -> Z.zero | Some n -> n)
             |> max @@ Z.to_int (match ubed with None -> Z.zero | Some n -> n)
             |> max @@ Z.to_int (match ubcc with None -> Z.zero | Some n -> n)
             |> max @@ Z.to_int (match ubcd with None -> Z.zero | Some n -> n) in
    let mn = mx - thre in
    let param' = (max nd mn), (max nc mn),
                 Option.map ubec ~f:(Z.max (Z.of_int mn)),
                 Option.map ubed ~f:(Z.max (Z.of_int mn)),
                 es,
                 Option.map ubcc ~f:(Z.max (Z.of_int mn)),
                 Option.map ubcd ~f:(Z.max (Z.of_int mn)),
                 cs in
    param := param'*)

  let in_space () = true

  let str_of () =
    let shp, depth, ext, ubec, ubed, es, ubcc, ubcd, cs = !param in
    Printf.sprintf
      ("shape : [%s]\n" ^^
       "depth : %d\n" ^^
       "ext : %d\n" ^^
       "upper bound of the sum of the abs of expression coefficients : %s\n" ^^
       "upper bound of the abs of expression constant : %s\n" ^^
       "seeds of expressions : %s\n" ^^
       "upper bound of the sum of the abs of condition coefficients : %s\n" ^^
       "upper bound of the abs of condition constant : %s\n" ^^
       "seeds of conditions : %s")
      (String.concat_map_list ~sep:";" shp ~f:string_of_int)
      depth ext
      (match ubec with None -> "N/A" | Some ubec -> Z.to_string ubec)
      (match ubed with None -> "N/A" | Some ubed -> Z.to_string ubed)
      (String.concat_set ~sep:"," @@ Set.Poly.map es ~f:Z.to_string)
      (match ubcc with None -> "N/A" | Some ubcc -> Z.to_string ubcc)
      (match ubcd with None -> "N/A" | Some ubcd -> Z.to_string ubcd)
      (String.concat_set ~sep:"," @@ Set.Poly.map cs ~f:Z.to_string)

  let _ =
    Debug.print @@ lazy ("************* initializing " ^ Ident.name_of_tvar Arg.name ^ " ***************");
    Debug.print @@ lazy (str_of ())
end
