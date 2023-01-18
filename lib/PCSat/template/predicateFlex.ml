open Core
open Common
open Common.Ext
open Ast
open Ast.LogicOld
open Function

module Config = struct
  type t = {
    verbose: bool;

    shape: int list;
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
            "Invalid PredicateFlex Configuration (%s): %s" filename msg
      end
    | Common.Util.ExtFile.Instance x -> Ok (Common.Util.ExtFile.Instance x)
end

module type ArgType = sig
  val name  : Ident.tvar
  val id    : int option
  val sorts : Sort.t list
  val dtenv : LogicOld.DTEnv.t
  val fenv  : LogicOld.FunEnv.t
end

type parameter = int list * int * Z.t option * Z.t option * Z.t Set.Poly.t
type parameter_update_type +=
  | DepthDisjConj
  | Coeff
  | Const
  | Qual

type state = int list * int * int option * int option * bool * bool * bool * bool * bool [@@deriving to_yojson]
let state_of ((shp, depth, ubc, ubd, _s) : parameter) labels : state =
  (shp, depth, Option.map ~f:Z.to_int ubc, Option.map ~f:Z.to_int ubd,
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
    ref (config.shape, config.depth,
         (Option.map config.upper_bound_coeff ~f:Z.of_int),
         (Option.map config.upper_bound_const ~f:Z.of_int),
         (match config.seeds with
          | None -> Set.Poly.singleton (Z.of_int 0)
          | Some s -> List.map s ~f:Z.of_int |> Set.Poly.of_list))
  let depth_of (_shp, depth, _ubc, _ubd, _s) = depth

  let params_of ~tag = ignore tag; sort_env_list_of_sorts Arg.sorts
  let adjust_quals ~tag quals =
    ignore tag; quals
  let init_quals _ _ = ()
  let gen_quals_terms ~tag (old_depth, old_quals, old_qdeps, old_terms) =
    let params = params_of ~tag in
    let depth = depth_of !param in
    let quals, qdeps, terms = Qualifier.AllTheory.qualifiers_of ~fenv:Arg.fenv depth old_depth params old_quals old_qdeps old_terms in
    (* Debug.print @@ lazy (Set.Poly.fold quals ~init:("generated qualifiers:") ~f:(fun ret phi -> ret ^ "\n" ^ (Formula.str_of phi)));
       Debug.print @@ lazy (Set.Poly.fold terms ~init:("generated terms:") ~f:(fun ret t -> ret ^ "\n" ^ (Term.str_of t))); *)
    depth, quals, qdeps, terms
  let gen_template ~tag quals qdeps terms =
    let params = params_of ~tag in
    let temp_params, hole_qualifiers_map, tmpl,
        cnstr_of_coeffs, cnstr_of_consts, cnstr_of_quals =
      let (shp, _depth, ubc, ubd, s) = !param in
      Generator.gen_dnf
        config.eq_atom
        (List.dedup_and_sort ~compare:Stdlib.compare quals)
        (List.map ~f:(fun t -> t, Term.sort_of t(*ToDo*)) @@
         List.dedup_and_sort ~compare:Stdlib.compare terms)
        (shp, ubc, ubd, s)
        (Option.map config.bound_each_coeff ~f:Z.of_int)
        params in
    (*Debug.print @@ lazy ("predicate template:\n  " ^ Formula.str_of tmpl);
      Debug.print @@ lazy ("cnstr_of_coeffs: " ^ (Formula.str_of cnstr_of_coeffs));
      Debug.print @@ lazy ("cnstr_of_consts: " ^ (Formula.str_of cnstr_of_consts));
      Debug.print @@ lazy ("cnstr_of_qualifiers: " ^ (Formula.str_of cnstr_of_quals)); *)
    let qual_ctls_env = Generator.qual_env_of_hole_map hole_qualifiers_map in
    let tmpl =
      Logic.Term.mk_lambda (Logic.of_old_sort_env_list Logic.ExtTerm.of_old_sort params) @@
      Logic.ExtTerm.of_old_formula tmpl in
    (DepthDisjConj, tmpl),
    [(Const, cnstr_of_consts |> Logic.ExtTerm.of_old_formula);
     (Coeff, cnstr_of_coeffs |> Logic.ExtTerm.of_old_formula);
     (Qual, cnstr_of_quals |> Logic.ExtTerm.of_old_formula);]
    @ qdep_constr_of_envs qdeps qual_ctls_env,
    temp_params, hole_qualifiers_map

  let restart (_shp, _depth, _ubc, _ubd, _s) =
    Debug.print @@ lazy ("************* restarting " ^ Ident.name_of_tvar Arg.name ^ "***************");
    [1], 0, Some Z.one, Some Z.zero, Set.Poly.singleton (Z.of_int 0)

  let last_non_timeout_param = ref !param
  let revert (_shp, _depth, _ubc, _ubd, _s) =
    Debug.print @@ lazy ("************* reverting " ^ Ident.name_of_tvar Arg.name ^ "***************");
    !last_non_timeout_param

  let increase_disj (shp, depth, ubc, ubd, s) =
    Debug.print @@ lazy ("************* increasing number_of_disj of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    1 :: shp, depth, ubc, ubd, s

  let increase_conj disj_idx (shp, depth, ubc, ubd, s) =
    Debug.print @@ lazy ("************* increasing number_of_conj of " ^ Common.Util.Ordinal.string_of (Common.Util.Ordinal.make disj_idx) ^ " disjunct of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    List.mapi shp ~f:(fun i nc -> if i = disj_idx then nc + 1 else nc), depth, ubc, ubd, s

  let increase_depth (shp, depth, ubc, ubd, s) =
    Debug.print @@ lazy ("************* increasing depth of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    shp, depth+1, ubc, ubd, s

  let increase_depth_disj_conj (shp, depth, ubc, ubd, s) =
    let nd_nc = List.fold shp ~init:0 ~f:(+) in
    if List.exists Arg.sorts ~f:(fun s -> Fn.non Term.is_int_sort s && Fn.non Term.is_bool_sort s) && nd_nc > (depth + 1) * (depth + 1) * (depth + 1) then begin
      Debug.print @@ lazy ("************* partially restarting with depth increased " ^ Ident.name_of_tvar Arg.name ^ "***************");
      ([1], depth + 1, ubc, ubd, s)
    end else if config.disj_first then
      (if Random.bool ()(*ToDo*) then increase_disj (shp, depth, ubc, ubd, s)
       else increase_conj (Random.int (List.length shp)(*ToDo*)) (shp, depth, ubc, ubd, s))
    else
      (if Random.bool ()(*ToDo*) then increase_conj (Random.int (List.length shp)(*ToDo*)) (shp, depth, ubc, ubd, s)
       else increase_disj (shp, depth, ubc, ubd, s))

  let increase_coeff threshold (shp, depth, ubc, ubd, s) =
    Debug.print @@ lazy ("************* increasing upper_bound_coeff of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    let ubc' =
      match ubc, threshold with
      | Some ubc, Some thr when Z.Compare.(ubc >= Z.of_int thr) -> None
      | _, _ -> Option.map ubc ~f:(fun ubc -> Z.(+) ubc (Z.of_int 1))
    in
    shp, depth, ubc', ubd, s

  let increase_const threshold (shp, depth, ubc, ubd, s) =
    Debug.print @@ lazy ("************* increasing upper_bound_const of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    let ubd' =
      match ubd, threshold with
      | Some ubd, Some thr when Z.Compare.(ubd >= Z.of_int thr) -> None
      | _, _ -> Option.map ubd ~f:(fun ubd -> Z.(+) ubd (Z.of_int 1))
    in
    shp, depth, ubc, ubd', s

  let set_inf_coeff (shp, depth, _ubc, ubd, s) =
    Debug.print @@ lazy ("************* setting upper_bound_coeff of " ^ Ident.name_of_tvar Arg.name ^ " to infinity ***************");
    let ubc' = None in
    shp, depth, ubc', ubd, s

  let set_inf_const (shp, depth, ubc, _ubd, s) =
    Debug.print @@ lazy ("************* setting upper_bound_const of " ^ Ident.name_of_tvar Arg.name ^ " to infinity ***************");
    let ubd' = None in
    shp, depth, ubc, ubd', s

  let next () = param :=
      !param
      |> (if config.fix_shape then Fn.id else increase_depth_disj_conj)
      |> increase_coeff config.threshold_coeff
      |> increase_const config.threshold_const

  let update_with_solution _ = failwith "not implemented"
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
      | "increase_disj" -> action (increase_disj param)
      | "increase_depth" -> action (increase_depth param)
      | "increase_coeff" -> action (increase_coeff None param)
      | "increase_const" -> action (increase_const None param)
      | "set_inf_coeff" -> action (set_inf_coeff param)
      | "set_inf_const" -> action (set_inf_const param)
      | "restart" -> action (restart param)
      | "revert" -> action (revert param)
      | "end" -> param
      | s ->
        let prefix = "increase_conj@" in
        match String.chop_prefix s ~prefix with
        | Some res ->
          action (increase_conj (int_of_string res) param)
        | None -> failwith ("Unknown action: " ^ s)
    in
    param := action !param
  let restart () = param := restart !param

  let sync _thre = ()
  (*let sync thre =
    let shp, depth, ubc, ubd, s = !param in
    let nd = List.length shp in
    let nc = match List.max_elt ~compare:compare shp with None -> 0 | Some m -> m in
    let mx = max nd nc
             |> max @@ Z.to_int (match ubc with None -> Z.zero | Some n -> n)
             |> max @@ Z.to_int (match ubd with None -> Z.zero | Some n -> n) in
    let mn = mx - thre in
    let param' = (max nd mn), (max nc mn), depth,
                 Option.map ubc ~f:(Z.max (Z.of_int mn)),
                 Option.map ubd ~f:(Z.max (Z.of_int mn)),
                 s in
    param := param'*)

  let str_of () =
    let shp, depth, ubc, ubd, s = !param in
    Printf.sprintf
      ("shape : [%s]\n" ^^
       "depth : %d\n" ^^
       "upper bound of the sum of the abs of coefficients : %s\n" ^^
       "upper bound of the sum of the abs of constant : %s\n" ^^
       "seeds : %s")
      (String.concat_map_list ~sep:";" shp ~f:string_of_int) depth
      (match ubc with None -> "N/A" | Some ubc -> Z.to_string ubc)
      (match ubd with None -> "N/A" | Some ubd -> Z.to_string ubd)
      (String.concat_set ~sep:"," @@ Set.Poly.map s ~f:Z.to_string)

  let _ =
    Debug.print @@ lazy ("************* initializing " ^ Ident.name_of_tvar Arg.name ^ " ***************");
    Debug.print @@ lazy (str_of ())
  let in_space () = true (* TODO *)
end