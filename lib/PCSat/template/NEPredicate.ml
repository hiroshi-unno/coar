open Core
open Common
open Common.Ext
open Ast
open Ast.LogicOld
open Function

module Config = struct
  type t = {
    verbose: bool;
    depth: int;
    ext : int;
    upper_bound_coeff: int;
    upper_bound_const: int
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
  val fenv  : LogicOld.FunEnv.t
  val id : int option
end

type parameter = int * int * int * int
type parameter_update_type +=
  | DepthExt
  | Dummy
  | NeInt
  | Coeff
  | Const

type state = int * int * int* int * bool * bool * bool * bool * bool [@@deriving to_yojson]
let state_of ((depth, ext, ubc, ubd) : parameter) labels : state =
  (depth, ext, ubc, ubd,
   Set.Poly.mem labels DepthExt,
   Set.Poly.mem labels NeInt,
   Set.Poly.mem labels Coeff,
   Set.Poly.mem labels Const,
   Set.Poly.mem labels TimeOut)

module Make (Cfg : Config.ConfigType) (Arg: ArgType) : Function.Type = struct
  let config = Cfg.config
  let id = Arg.id

  module Debug = Debug.Make (val (Debug.Config.(if config.verbose then enable else disable)))
  let _ = Debug.set_id id

  let param : parameter ref =
    ref (config.depth, config.ext, config.upper_bound_coeff, config.upper_bound_const)
  let depth_of (depth, _, _, _) = depth
  let params_of ~tag = ignore tag; sort_env_list_of_sorts Arg.sorts
  let adjust_quals ~tag quals =
    ignore tag;
    Set.Poly.filter_map quals ~f:(fun phi ->
        let phi = Normalizer.normalize phi in
        match phi with
        | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, _, _), _) -> Some phi
        | Formula.Atom (Atom.App (Predicate.Psym T_int.Geq, [t1; t2], _), _) -> Some (Formula.eq t1 t2)
        | _ -> None)
  let filter_eq quals =
    Set.Poly.filter_map quals ~f:(fun phi ->
        let phi = Normalizer.normalize phi in
        match phi with
        | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, _, _), _) -> Some phi
        | _ -> None)
  let init_quals _ _ = ()
  let gen_quals_terms ~tag (old_depth, old_quals, old_qdeps, old_terms) =
    let params = params_of ~tag in
    let depth = depth_of !param in
    let quals, qdeps, terms =
      Qualifier.AllTheory.qualifiers_of
        ~fenv:Arg.fenv depth old_depth params old_quals old_qdeps old_terms
    in
    (* Debug.print @@ lazy (Set.Poly.fold quals ~init:("generated qualifiers:") ~f:(fun ret phi -> ret ^ "\n" ^ (Formula.str_of phi)));
       Debug.print @@ lazy (Set.Poly.fold terms ~init:("generated terms:") ~f:(fun ret t -> ret ^ "\n" ^ (Term.str_of t))); *)
    depth, filter_eq quals, qdeps, terms

  let gen_template ~tag quals _ terms =
    let params = params_of ~tag in
    let temp_params, tmpl, ne_constr, scope_constr, coeff_bound_constr, const_bound_constr =
      Generator.gen_ne_template quals terms (!param) params
    in
    Debug.print @@ lazy (sprintf "[%s] ne predicate template:\n  " (Ident.name_of_tvar @@ Arg.name) ^ Formula.str_of tmpl);
    Debug.print @@ lazy (sprintf "[%s] quals:\n" (Ident.name_of_tvar @@ Arg.name) ^ String.concat_map_list ~sep:"\n" quals ~f:(Formula.str_of));
    Debug.print @@ lazy (sprintf "[%s] ne_constr:\n  " (Ident.name_of_tvar @@ Arg.name) ^ Formula.str_of ne_constr);
    Debug.print @@ lazy (sprintf "[%s] scope_constr:\n  " (Ident.name_of_tvar @@ Arg.name) ^ Formula.str_of scope_constr);
    Debug.print @@ lazy (sprintf "[%s] coeff_bound_constr:\n  " (Ident.name_of_tvar @@ Arg.name) ^ Formula.str_of coeff_bound_constr);
    Debug.print @@ lazy (sprintf "[%s] const_bound_constr:\n  " (Ident.name_of_tvar @@ Arg.name) ^ Formula.str_of const_bound_constr);
    let tmpl =
      Logic.Term.mk_lambda (Logic.of_old_sort_env_list Logic.ExtTerm.of_old_sort params) @@
      Logic.ExtTerm.of_old_formula tmpl in
    (DepthExt, tmpl),
    [(Dummy, ne_constr |> Logic.ExtTerm.of_old_formula);
     (Dummy, scope_constr |> Logic.ExtTerm.of_old_formula);
     (Coeff, coeff_bound_constr |> Logic.ExtTerm.of_old_formula);
     (Const, const_bound_constr |> Logic.ExtTerm.of_old_formula)],
    temp_params, []

  let restart (_depth, _, _, _) =
    Debug.print @@ lazy ("************* restarting " ^ Ident.name_of_tvar Arg.name ^ "***************");
    1, 1, config.upper_bound_coeff, config.upper_bound_const

  let last_non_timeout_param = ref !param
  let revert (_depth, _, _, _) =
    Debug.print @@ lazy ("************* reverting " ^ Ident.name_of_tvar Arg.name ^ "***************");
    !last_non_timeout_param

  let increase_depth_ext (depth, ext, ubc, ubd) =
    if (depth + ext) mod 2 = 0 then begin
      Debug.print @@ lazy ("************* increasing depth of " ^ Ident.name_of_tvar Arg.name ^ "***************");
      depth+1, ext, ubc, ubd
    end else begin
      Debug.print @@ lazy ("************* increasing ext of " ^ Ident.name_of_tvar Arg.name ^ "***************");
      depth, ext + 1, ubc, ubd
    end

  let increase_coeff (depth, ext, ubc, ubd) =
    Debug.print @@ lazy ("************* increasing coeff of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    depth, ext, ubc + 1, ubd

  let increase_const (depth, ext, ubc, ubd) =
    Debug.print @@ lazy ("************* increasing const of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    depth, ext, ubc, ubd + 1

  let next () = param :=
      !param
      |> increase_depth_ext
      |> increase_coeff
      |> increase_const

  (* obsolete *)
  let update_with_solution _phi = assert false

  let update_with_labels labels =
    let rec inner param = function
      | [] -> param
      | DepthExt :: labels -> inner (increase_depth_ext param) labels
      | NeInt :: labels -> inner param labels
      | QDep :: labels -> inner param labels
      | Dummy :: labels -> inner param labels
      | Coeff :: labels -> inner (increase_coeff param) labels
      | Const :: labels -> inner (increase_const param) labels
      | TimeOut :: _labels -> param(* z3 may unexpectedly time out*)
      | _ -> assert false
    in
    param := inner !param @@ Set.Poly.to_list labels

  let rl_action labels =
    if not @@ Set.Poly.mem labels TimeOut then
      last_non_timeout_param := !param;
    Out_channel.print_endline ("state of " ^ Ident.name_of_tvar Arg.name ^ ": " ^ Yojson.Safe.to_string @@ state_to_yojson @@ state_of !param labels);
    Out_channel.flush Out_channel.stdout;
    let rec action param =
      match In_channel.input_line_exn In_channel.stdin with
      | "increase_depth_ext" -> action (increase_depth_ext param)
      | "restart" -> action (restart param)
      | "revert" -> action (revert param)
      | "increase_coeff" -> action (increase_coeff param)
      | "increase_const" -> action (increase_const param)
      | "end" -> param
      | s -> failwith ("Unknown action: " ^ s)
    in
    param := action !param
  let restart () = param := restart !param

  let sync _thre = ()

  let show_state show_num_args labels =
    if show_num_args then
      Out_channel.print_endline (Format.sprintf "#args: %d" (List.length Arg.sorts));
    Out_channel.print_endline ("state of " ^ Ident.name_of_tvar Arg.name ^ ": " ^ Yojson.Safe.to_string @@ state_to_yojson @@ state_of !param labels);
    Out_channel.flush Out_channel.stdout

  let str_of () =
    let (depth, ext, ubc, ubd) = !param in
    Printf.sprintf "depth: %d\next: %d\nubc: %d\nubd: %d" depth ext ubc ubd

  let _ =
    Debug.print @@ lazy ("************* initializing " ^ Ident.name_of_tvar Arg.name ^ " ***************");
    Debug.print @@ lazy (str_of ())
  let in_space () = true (* TODO *)
end