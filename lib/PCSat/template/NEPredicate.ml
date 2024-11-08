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
    depth : int;
    ext : int;
    upper_bound_coeff : int;
    upper_bound_const : int;
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
            @@ sprintf "Invalid NEPredicate Configuration (%s): %s" filename msg
        )
end

module type ArgType = sig
  val name : Ident.tvar
  val sorts : Sort.t list
  val fenv : LogicOld.FunEnv.t
  val id : int option
end

type parameter = { depth : int; ext : int; ubc : int; ubd : int }
type parameter_update_type += DepthExt | Dummy | NeInt | Coeff | Const

type state = int * int * int * int * bool * bool * bool * bool * bool
[@@deriving to_yojson]

let state_of param labels : state =
  ( param.depth,
    param.ext,
    param.ubc,
    param.ubd,
    Set.mem labels DepthExt,
    Set.mem labels NeInt,
    Set.mem labels Coeff,
    Set.mem labels Const,
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
        depth = config.depth;
        ext = config.ext;
        ubc = config.upper_bound_coeff;
        ubd = config.upper_bound_const;
      }

  let init = { depth = 0; ext = 0; ubc = 1; ubd = 0 }
  let name_of () = Arg.name
  let kind_of () = Kind.str_of Kind.NE
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
    sprintf "depth: %d\next: %d\nubc: %d\nubd: %d" !param.depth !param.ext
      !param.ubc !param.ubd

  let in_space () = true (* TODO *)

  let adjust_quals ~tag quals =
    ignore tag;
    Set.Poly.filter_map quals ~f:(fun phi ->
        match Normalizer.normalize phi with
        | Formula.Atom
            (Atom.App (Predicate.Psym (T_bool.Eq | T_int.Geq), [ t1; t2 ], _), _)
          ->
            Some (Formula.eq t1 t2)
        | _ -> None)

  let init_quals _ _ = ()

  let update_hspace ~tag hspace =
    ignore tag;
    Qualifier.AllTheory.qualifiers_of ~fenv:Arg.fenv !param.depth hspace

  let gen_template ~tag ~ucore hspace =
    ignore tag;
    ignore ucore;
    let quals =
      (*ToDo*)
      Set.Poly.filter_map hspace.quals ~f:(fun phi ->
          let phi = Normalizer.normalize phi in
          if Formula.is_eq phi then Some phi else None)
    in
    let params = params_of ~tag in
    let ( temp_params,
          tmpl,
          ne_constr,
          scope_constr,
          cnstr_of_coeffs,
          cnstr_of_consts ) =
      Generator.gen_ne_template (Set.to_list quals) (Set.to_list hspace.terms)
        (!param.depth, !param.ext, !param.ubc, !param.ubd)
        params
    in
    let hole_qualifiers_map = [] in
    Debug.print
    @@ lazy
         (sprintf "[%s] predicate template:\n  %s"
            (Ident.name_of_tvar @@ Arg.name)
            (Formula.str_of tmpl));
    Debug.print
    @@ lazy
         (sprintf "[%s] ne_constr:\n  %s"
            (Ident.name_of_tvar @@ Arg.name)
            (Formula.str_of ne_constr));
    Debug.print
    @@ lazy
         (sprintf "[%s] scope_constr:\n  %s"
            (Ident.name_of_tvar @@ Arg.name)
            (Formula.str_of scope_constr));
    Debug.print
    @@ lazy
         (sprintf "[%s] cnstr_of_coeffs:\n  %s"
            (Ident.name_of_tvar @@ Arg.name)
            (Formula.str_of cnstr_of_coeffs));
    Debug.print
    @@ lazy
         (sprintf "[%s] cnstr_of_consts:\n  %s"
            (Ident.name_of_tvar @@ Arg.name)
            (Formula.str_of cnstr_of_consts));
    let tmpl =
      Logic.(
        Term.mk_lambda (of_old_sort_env_list  hspace.params))
      @@ Logic.ExtTerm.of_old_formula tmpl
    in
    ( (DepthExt, tmpl),
      [
        (Dummy, Logic.ExtTerm.of_old_formula ne_constr);
        (Dummy, Logic.ExtTerm.of_old_formula scope_constr);
        (Coeff, Logic.ExtTerm.of_old_formula cnstr_of_coeffs);
        (Const, Logic.ExtTerm.of_old_formula cnstr_of_consts);
      ],
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

  let increase_coeff (param, actions) =
    Debug.print
    @@ lazy
         ("************* increasing coeff of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with ubc = param.ubc + 1 }, actions @ [ "increase_coeff" ])

  let decrease_coeff (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing coeff of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with ubc = max (param.ubc - 1) 0 }, actions @ [ "decrease_coeff" ])

  let init_coeff (param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing coeff of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with ubc = init.ubc }, actions @ [ "init_coeff" ])

  let increase_const (param, actions) =
    Debug.print
    @@ lazy
         ("************* increasing const of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with ubd = param.ubd + 1 }, actions @ [ "increase_const" ])

  let decrease_const (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing const of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with ubd = max (param.ubd - 1) 0 }, actions @ [ "decrease_const" ])

  let init_const (param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing const of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with ubd = init.ubd }, actions @ [ "init_const" ])

  let increase_depth_ext (param, actions) =
    if (param.depth + param.ext) mod 2 = 0 then increase_depth (param, actions)
    else increase_ext (param, actions)

  let rec inner param_actions = function
    | [] -> param_actions
    | DepthExt :: labels -> inner (increase_depth_ext param_actions) labels
    | (NeInt | QDep | Dummy) :: labels -> inner param_actions labels
    | Coeff :: labels -> inner (increase_coeff param_actions) labels
    | Const :: labels -> inner (increase_const param_actions) labels
    | TimeOut :: _labels -> param_actions (* z3 may unexpectedly time out*)
    | _ -> assert false

  let actions_of labels =
    (snd @@ inner (!param, []) @@ Set.to_list labels) @ [ "end" ]

  let update_with_labels labels =
    param := fst @@ inner (!param, []) @@ Set.to_list labels

  let rl_action labels =
    if not @@ Set.mem labels TimeOut then last_non_timeout_param := !param;
    Out_channel.flush Out_channel.stdout;
    let rec action param_actions =
      match In_channel.input_line_exn In_channel.stdin with
      | "increase_depth" -> action (increase_depth param_actions)
      | "decrease_depth" -> action (decrease_depth param_actions)
      | "init_depth" -> action (init_depth param_actions)
      | "increase_ext" -> action (increase_ext param_actions)
      | "decrease_ext" -> action (decrease_ext param_actions)
      | "init_ext" -> action (init_ext param_actions)
      | "increase_coeff" -> action (increase_coeff param_actions)
      | "decrease_coeff" -> action (decrease_coeff param_actions)
      | "init_coeff" -> action (init_coeff param_actions)
      | "increase_const" -> action (increase_const param_actions)
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
  let sync _thre = assert false

  let _ =
    Debug.print
    @@ lazy
         (sprintf "************* initializing %s ***************"
            (Ident.name_of_tvar Arg.name));
    Debug.print @@ lazy (str_of ())
end
