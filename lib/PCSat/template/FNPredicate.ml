open Core
open Common.Util
open Ast
open Ast.LogicOld
open Function

module Config = struct
  type t = {
    verbose: bool;

    number_of_expr: int;
    number_of_cond_conj: int;
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
          error_string
          @@ Printf.sprintf
            "Invalid FNPredicate Configuration (%s): %s" filename msg
      end
    | Instance x -> Ok (Instance x)
end

module type ArgType = sig
  val name  : Ident.tvar
  val sorts : Sort.t list
end

  (*
   - number of conditions : int
   - number of conjunctions : int
   - coeff_upper_bound : Z.t
   - const_upper_bound : Z.t
   - const seed of_template : Z.t Set.Poly.t
   - coeff_upper_bound_for_cond : Z.t
   - const_upper_bound_for_cond : Z.t
   - const seed of_cond : Z.t Set.Poly.t
   *)
type parameter = int * int * Z.t option * Z.t option * Z.t Set.Poly.t * Z.t option * Z.t option * Z.t Set.Poly.t
type parameter_update_type +=
  | ExprCondConj
  | ExprCoeff
  | ExprConst
  | CondCoeff
  | CondConst

module Make (Cfg : Config.ConfigType) (Arg : ArgType) : Function.Type = struct
  let config = Cfg.config

  module Debug =
    Common.Debug.Make
      (val (Common.Debug.Config.(if config.verbose then enable else disable)))

  let param : parameter ref =
    ref (config.number_of_expr, config.number_of_cond_conj,
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

  let params_of () = SortEnv.of_sorts Arg.sorts
  let adjust_quals quals =
    let ret = List.last_exn @@ SortEnv.list_of @@ params_of () in
    let fenv = Set.Poly.empty in (*TODO: generate fenv*)
    Set.Poly.filter_map quals ~f:(fun phi ->
        let qual = Z3Smt.Z3interface.qelim fenv @@ Formula.exists (SortEnv.of_list [ret]) phi in
        (*ToDo*)if Formula.is_bind qual || Set.Poly.is_empty (Formula.fvs_of qual) then None else Some qual)
  let gen_quals_terms (_old_depth, quals, terms) =
    (*TODO: generate quals and terms*)
    0, quals, terms
  let gen_template quals terms =
    let params = params_of () in
    let temp_params, hole_qualifiers_map, tmpl,
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
        (SortEnv.list_of params) in
    let tmpl =
      Logic.Term.mk_lambda (Logic.SortEnv.of_old_sort_env Logic.ExtTerm.of_old_sort params) @@
      Logic.ExtTerm.of_old_formula tmpl in
    (ExprCondConj, tmpl),
    ([(ExprCoeff, cnstr_of_expr_coeffs |> Logic.ExtTerm.of_old_formula);
      (ExprConst, cnstr_of_expr_const |> Logic.ExtTerm.of_old_formula);
      (CondCoeff, cnstr_of_cond_coeffs |> Logic.ExtTerm.of_old_formula);
      (CondConst, cnstr_of_cond_const |> Logic.ExtTerm.of_old_formula)]),
    temp_params, hole_qualifiers_map

  let update_expr_cond_conj (nd, nc, ubec, ubed, es, ubcc, ubcd, cs) =
    let nd', nc' = if (match config.max_number_of_cond_conj with None -> false | Some max -> nc >= max) || (nd + nc) mod 2 = 0 then begin
        Debug.print @@ lazy ("************* updating number_of_expr of " ^ Ident.name_of_tvar Arg.name ^ "***************");
        nd+1, nc
      end else begin
        Debug.print @@ lazy ("************* updating number_of_cond_conj of " ^ Ident.name_of_tvar Arg.name ^ "***************");
        nd, nc+1
      end in
    nd', nc', ubec, ubed, es, ubcc, ubcd, cs

  let update_expr_coeff (nd, nc, ubec, ubed, es, ubcc, ubcd, cs) =
    Debug.print @@ lazy ("************* updating upper_bound_expr_coeff of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    let ubec' =
      match ubec, config.threshold_expr_coeff with
      | Some ubec, Some thr when Z.Compare.(ubec >= Z.of_int thr) -> None
      | _, _ -> Option.map ubec ~f:(fun ubec -> Z.(+) ubec (Z.of_int 1))
    in
    nd, nc, ubec', ubed, es, ubcc, ubcd, cs

  let update_expr_const (nd, nc, ubec, ubed, es, ubcc, ubcd, cs) =
    Debug.print @@ lazy ("************* updating upper_bound_expr_const of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    let ubed' =
      match ubed, config.threshold_expr_const with
      | Some ubed, Some thr when Z.Compare.(ubed >= Z.of_int thr) -> None
      | _, _ -> Option.map ubed ~f:(fun ubed -> Z.(+) ubed (Z.of_int 1))
    in
    nd, nc, ubec, ubed', es, ubcc, ubcd, cs

  let update_cond_coeff (nd, nc, ubec, ubed, es, ubcc, ubcd, cs) =
    Debug.print @@ lazy ("************* updating upper_bound_cond_coeff of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    let ubcc' =
      match ubcc, config.threshold_cond_coeff with
      | Some ubcc, Some thr when Z.Compare.(ubcc >= Z.of_int thr) -> None
      | _, _ -> Option.map ubcc ~f:(fun ubcc -> Z.(+) ubcc (Z.of_int 1))
    in
    nd, nc, ubec, ubed, es, ubcc', ubcd, cs

  let update_cond_const (nd, nc, ubec, ubed, es, ubcc, ubcd, cs) =
    Debug.print @@ lazy ("************* updating upper_bound_cond_const of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    let ubcd' =
      match ubcd, config.threshold_cond_const with
      | Some ubcd, Some thr when Z.Compare.(ubcd >= Z.of_int thr) -> None
      | _, _ -> Option.map ubed ~f:(fun ubcd -> Z.(+) ubcd (Z.of_int 1))
    in
    nd, nc, ubec, ubed, es, ubcc, ubcd', cs

  let next () = param := !param |> update_expr_cond_conj |> update_expr_coeff |> update_expr_const |> update_cond_coeff |> update_cond_const

  let update_with_solution _ = assert false

  let update_with_labels labels =
    let rec inner param = function
      | [] -> param
      | ExprCondConj :: labels -> inner (update_expr_cond_conj param) labels
      | ExprCoeff :: labels -> inner (update_expr_coeff param) labels
      | ExprConst :: labels -> inner (update_expr_const param) labels
      | CondCoeff :: labels -> inner (update_cond_coeff param) labels
      | CondConst :: labels -> inner (update_cond_const param) labels
      | TimeOut :: _labels -> param(* z3 may unexpectedly time out*)
      | _ -> assert false
    in
    param := inner !param @@ Set.Poly.to_list labels
  let rl_action _labels = assert false
  let restart () = ()

  let sync thre =
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
    param := param'

  let str_of () =
    let nd, nc, ubec, ubed, es, ubcc, ubcd, cs = !param in
    Printf.sprintf
      ("number of cases : %d\n" ^^
       "number of condition conjuncts : %d\n" ^^
       "upper bound of the sum of the abs of expression coefficients : %s\n" ^^
       "upper bound of the abs of expression constant : %s\n" ^^
       "seeds of expressions : %s\n" ^^
       "upper bound of the sum of the abs of condition coefficients : %s\n" ^^
       "upper bound of the abs of condition constant : %s\n" ^^
       "seeds of conditions : %s")
      nd nc
      (match ubec with None -> "N/A" | Some ubec -> Z.to_string ubec)
      (match ubed with None -> "N/A" | Some ubed -> Z.to_string ubed)
      (String.concat ~sep:"," @@ Set.Poly.to_list @@ Set.Poly.map es ~f:Z.to_string)
      (match ubcc with None -> "N/A" | Some ubcc -> Z.to_string ubcc)
      (match ubcd with None -> "N/A" | Some ubcd -> Z.to_string ubcd)
      (String.concat ~sep:"," @@ Set.Poly.to_list @@ Set.Poly.map cs ~f:Z.to_string)

  let _ =
    Debug.print @@ lazy ("************* initializing " ^ Ident.name_of_tvar Arg.name ^ " ***************");
    Debug.print @@ lazy (str_of ())
end
