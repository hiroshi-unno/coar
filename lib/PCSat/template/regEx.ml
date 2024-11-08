open Core
open Common
open Common.Ext
open Common.Util
open Ast
open Ast.LogicOld
open PCSatCommon.HypSpace
open Function

module Config = struct
  type t = { verbose : bool; depth : int } [@@deriving yojson]

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
            @@ sprintf "Invalid RegEx Configuration (%s): %s" filename msg)
end

module type ArgType = sig
  val name : Ident.tvar
  val sorts : Sort.t list
  val fenv : LogicOld.FunEnv.t
  val id : int option
end

type parameter = { depth : int }
type parameter_update_type += Depth | Dummy
type state = int * bool [@@deriving to_yojson]

let state_of param labels : state =
  (param.depth, Set.mem labels Depth (* ToDo: this is always true *))

module Make (Cfg : Config.ConfigType) (Arg : ArgType) : Function.Type = struct
  let config = Cfg.config
  let id = Arg.id

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_id id
  let param = ref { depth = config.depth }
  let init = { depth = 0 }
  let name_of () = Arg.name
  let kind_of () = Kind.str_of Kind.RegEx
  let sort_of () = Sort.mk_fun @@ Arg.sorts @ [ T_regex.SRegEx ]

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

  let str_of () = sprintf "depth : %d" !param.depth
  let in_space () = true (* TODO *)

  let adjust_quals ~tag quals =
    ignore tag;
    quals

  let init_quals _ _ = ()

  let update_hspace ~tag hspace =
    ignore tag;
    Qualifier.AllTheory.qualifiers_of ~fenv:Arg.fenv !param.depth hspace

  let gen_template ~tag ~ucore hspace =
    ignore tag;
    ignore ucore;
    let temp_params = ref Map.Poly.empty in
    let cnstr_of_temp_params = ref @@ Formula.mk_true () in
    let hole_qualifiers_map = [] in
    let tmpl =
      let switch ts =
        let x = Ident.mk_fresh_parameter () in
        let xt = Term.mk_var x T_int.SInt in
        temp_params :=
          Map.Poly.add_exn !temp_params ~key:x ~data:Logic.ExtTerm.SInt;
        cnstr_of_temp_params :=
          Formula.and_of
          @@ !cnstr_of_temp_params
             :: Formula.mk_range xt Z.zero (Z.of_int @@ (List.length ts - 1));
        let cond n =
          (*let x = Ident.mk_fresh_parameter () in
            temp_params := Map.Poly.add_exn !temp_params ~key:x ~data:Logic.ExtTerm.SBool;
            Formula.of_bool_var x*)
          Formula.mk_atom @@ T_bool.mk_eq xt (T_int.mk_int @@ Z.of_int n)
        in
        let rec aux i = function
          | [] -> assert false
          | [ t ] -> t
          | t :: ts -> T_bool.ifte (cond i) t (aux (i + 1) ts)
        in
        aux 0 ts
      in
      let rec aux d =
        switch
        @@ T_regex.mk_empty () :: T_regex.mk_full () :: T_regex.mk_eps ()
           :: List.map (Set.to_list hspace.consts) ~f:T_regex.mk_str_to_re
        @
        if d <= 0 then []
        else
          [
            T_regex.mk_complement (aux (d - 1));
            T_regex.mk_star (aux (d - 1));
            T_regex.mk_plus (aux (d - 1));
            T_regex.mk_opt (aux (d - 1));
            T_regex.mk_concat (aux (d - 1)) (aux (d - 1));
            T_regex.mk_union (aux (d - 1)) (aux (d - 1));
            T_regex.mk_inter (aux (d - 1)) (aux (d - 1));
          ]
      in
      aux hspace.depth
    in
    let tmpl =
      if false then tmpl
      else
        (* ToDo: the following should be removed when the bug of dZ3 is fixed *)
        Evaluator.simplify_term
        @@ List.fold (Term.elim_ite tmpl) ~init:(T_regex.mk_empty ())
             ~f:(fun acc (cond, t) -> T_bool.ifte cond t acc)
    in
    Debug.print
    @@ lazy
         (sprintf "[%s] predicate template:\n  %s"
            (Ident.name_of_tvar @@ Arg.name)
            (Term.str_of tmpl));
    let tmpl =
      Logic.(
        Term.mk_lambda (of_old_sort_env_list  hspace.params))
      @@ Logic.ExtTerm.of_old_term tmpl
    in
    ( (Depth, tmpl),
      [ (Dummy, Logic.ExtTerm.of_old_formula !cnstr_of_temp_params) ],
      !temp_params,
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
    ({ depth = param.depth + 1 }, actions @ [ "increase_depth" ])

  let decrease_depth (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing depth of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ depth = max (param.depth - 1) 0 }, actions @ [ "decrease_depth" ])

  let init_depth (_param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing depth of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ depth = init.depth }, actions @ [ "init_depth" ])

  let rec inner param_actions = function
    | [] -> param_actions
    | Depth :: labels -> inner (increase_depth param_actions) labels
    | (Dummy | QDep) :: labels -> inner param_actions labels
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
      | "increase_depth" -> action (increase_depth param_actions)
      | "decrease_depth" -> action (decrease_depth param_actions)
      | "init_depth" -> action (init_depth param_actions)
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
