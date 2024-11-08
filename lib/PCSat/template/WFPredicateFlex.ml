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
    shape : int list;
    number_of_rfun_lexicos : int;
    depth : int;
    upper_bound_rfun_coeff : int option;
    upper_bound_rfun_const : int option;
    upper_bound_disc_coeff : int option;
    upper_bound_disc_const : int option;
    disc_seeds : int list option;
    norm_type : int;
    use_ifte : bool;
    lower_bound_rfun_coeff : int option;
    lower_bound_disc_coeff : int option;
    bound_each_rfun_coeff : int option;
    bound_each_disc_coeff : int option;
    threshold_rfun_coeff : int option;
    threshold_rfun_const : int option;
    threshold_disc_coeff : int option;
    threshold_disc_const : int option;
    ignore_bool : bool;
    fix_shape : bool;
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
            @@ sprintf "Invalid WFPredicateFlex Configuration (%s): %s" filename
                 msg)
end

module type ArgType = sig
  val name : Ident.tvar
  val sorts : Sort.t list
  val fenv : LogicOld.FunEnv.t
  val id : int option
end

type parameter = {
  shp : int list;
  nl : int;
  depth : int;
  ubrc : Z.t option;
  ubrd : Z.t option;
  ubdc : Z.t option;
  ubdd : Z.t option;
  ds : Z.t Set.Poly.t;
}

type parameter_update_type +=
  | LexicoPieceConj
  | RFunCoeff
  | RFunConst
  | DiscCoeff
  | DiscConst

type state =
  int list
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
  ( param.shp,
    param.nl,
    param.depth,
    Option.map ~f:Z.to_int param.ubrc,
    Option.map ~f:Z.to_int param.ubrd,
    Option.map ~f:Z.to_int param.ubdc,
    Option.map ~f:Z.to_int param.ubdd,
    Set.mem labels LexicoPieceConj (* ToDo: this is always true *),
    Set.mem labels RFunCoeff,
    Set.mem labels RFunConst,
    Set.mem labels DiscCoeff,
    Set.mem labels DiscConst,
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
        shp = config.shape;
        nl = config.number_of_rfun_lexicos;
        depth = config.depth;
        ubrc = Option.map config.upper_bound_rfun_coeff ~f:Z.of_int;
        ubrd = Option.map config.upper_bound_rfun_const ~f:Z.of_int;
        ubdc = Option.map config.upper_bound_disc_coeff ~f:Z.of_int;
        ubdd = Option.map config.upper_bound_disc_const ~f:Z.of_int;
        ds =
          (match config.disc_seeds with
          | None -> Set.Poly.singleton Z.zero
          | Some ds -> Set.Poly.of_list @@ List.map ds ~f:Z.of_int);
      }

  let init =
    {
      shp = [ 0 ];
      nl = 1;
      depth = 0;
      ubrc = Some Z.one;
      ubrd = Some Z.zero;
      ubdc = Some Z.one;
      ubdd = Some Z.zero;
      ds = Set.Poly.singleton Z.zero;
    }

  let name_of () = Arg.name
  let kind_of () = sprintf "flexible %s" (Kind.str_of Kind.WF)
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
      ("shape : [%s]\n" ^^ "number of lexicographic : %d\n" ^^ "depth : %d\n"
     ^^ "upper bound of the sum of the abs of ranking function coefficients : %s\n"
     ^^ "upper bound of the abs of ranking function constant : %s\n"
     ^^ "upper bound of the sum of the abs of discriminator coefficients : %s\n"
     ^^ "upper bound of the abs of discriminator constant : %s\n"
     ^^ "seeds : %s")
      (String.concat_map_list ~sep:";" !param.shp ~f:string_of_int)
      !param.nl !param.depth
      (match !param.ubrc with None -> "N/A" | Some ubrc -> Z.to_string ubrc)
      (match !param.ubrd with None -> "N/A" | Some ubrd -> Z.to_string ubrd)
      (match !param.ubdc with None -> "N/A" | Some ubdc -> Z.to_string ubdc)
      (match !param.ubdd with None -> "N/A" | Some ubdd -> Z.to_string ubdd)
      (String.concat_set ~sep:"," @@ Set.Poly.map !param.ds ~f:Z.to_string)

  let in_space () = true (* TODO *)

  let adjust_quals ~tag quals =
    let params = params_of ~tag in
    let params_x, params_y = List.split_n params (List.length params / 2) in
    let rename_x_y =
      Formula.rename (tvar_map_of_sort_env_list params_x params_y)
    in
    let rename_y_x =
      Formula.rename (tvar_map_of_sort_env_list params_y params_x)
    in
    Set.concat_map quals ~f:(fun phi ->
        let qual1 =
          Z3Smt.Z3interface.qelim ~id ~fenv:Arg.fenv
          @@ Formula.exists params_y phi
        in
        let qual2 =
          Z3Smt.Z3interface.qelim ~id ~fenv:Arg.fenv
          @@ Formula.exists params_x phi
        in
        Set.union
          (if Formula.is_bind qual1 || Set.is_empty (Formula.fvs_of qual1) then
             Set.Poly.empty
           else Set.Poly.of_list [ qual1; rename_x_y qual1 ])
          (if Formula.is_bind qual2 || Set.is_empty (Formula.fvs_of qual2) then
             Set.Poly.empty
           else Set.Poly.of_list [ rename_y_x qual2; qual2 ]))

  let init_quals _ _ = ()

  let update_hspace ~tag hspace =
    ignore tag;
    Qualifier.AllTheory.qualifiers_of ~fenv:Arg.fenv !param.depth hspace

  let gen_template ~tag ~ucore hspace =
    ignore tag;
    ignore ucore;
    assert (List.length hspace.params mod 2 = 0);
    let ( temp_params,
          hole_qualifiers_map,
          tmpl,
          cnstr_of_rfun_coeffs,
          cnstr_of_rfun_const,
          cnstr_of_disc_coeffs,
          cnstr_of_disc_const ) =
      Generator.gen_simplified_wf_predicate
        (*config.use_ifte*)
        (Set.to_list hspace.quals)
        (Set.to_list hspace.terms)
        ( !param.shp,
          !param.nl,
          !param.ubrc,
          !param.ubrd,
          !param.ubdc,
          !param.ubdd,
          !param.ds )
        ( config.norm_type,
          Option.map config.lower_bound_rfun_coeff ~f:Z.of_int,
          Option.map config.lower_bound_disc_coeff ~f:Z.of_int,
          Option.map config.bound_each_rfun_coeff ~f:Z.of_int,
          Option.map config.bound_each_disc_coeff ~f:Z.of_int )
        hspace.params
    in
    Debug.print
    @@ lazy
         (sprintf "[%s] predicate template:\n  %s"
            (Ident.name_of_tvar Arg.name)
            (Formula.str_of tmpl));
    Debug.print
    @@ lazy
         (sprintf "[%s] cnstr_of_rfun_coeffs:\n  %s"
            (Ident.name_of_tvar @@ Arg.name)
            (Formula.str_of cnstr_of_rfun_coeffs));
    Debug.print
    @@ lazy
         (sprintf "[%s] cnstr_of_rfun_const:\n  %s"
            (Ident.name_of_tvar @@ Arg.name)
            (Formula.str_of cnstr_of_rfun_const));
    Debug.print
    @@ lazy
         (sprintf "[%s] cnstr_of_disc_coeffs:\n  %s"
            (Ident.name_of_tvar @@ Arg.name)
            (Formula.str_of cnstr_of_disc_coeffs));
    Debug.print
    @@ lazy
         (sprintf "[%s] cnstr_of_disc_const:\n  %s"
            (Ident.name_of_tvar @@ Arg.name)
            (Formula.str_of cnstr_of_disc_const));
    let tmpl =
      Logic.(Term.mk_lambda (of_old_sort_env_list hspace.params))
      @@ Logic.ExtTerm.of_old_formula tmpl
    in
    ( (LexicoPieceConj, tmpl),
      [
        (RFunCoeff, Logic.ExtTerm.of_old_formula cnstr_of_rfun_coeffs);
        (RFunConst, Logic.ExtTerm.of_old_formula cnstr_of_rfun_const);
        (DiscCoeff, Logic.ExtTerm.of_old_formula cnstr_of_disc_coeffs);
        (DiscConst, Logic.ExtTerm.of_old_formula cnstr_of_disc_const);
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

  let increase_rfun_pieces (param, actions) =
    Debug.print
    @@ lazy
         ("************* increasing number_of_rfun_pieces of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with shp = 0 :: param.shp }, actions @ [ "increase_rfun_pieces" ])

  let decrease_rfun_pieces (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing number_of_rfun_pieces of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ( { param with shp = (match param.shp with [] -> [] | _ :: shp -> shp) },
      actions @ [ "decrease_rfun_pieces" ] )

  let increase_disc_conj piece_idx (param, actions) =
    Debug.print
    @@ lazy
         ("************* increasing number_of_disc_conj of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ( {
        param with
        shp =
          List.mapi param.shp ~f:(fun i ndc ->
              if i = piece_idx then ndc + 1 else ndc);
      },
      actions @ [ "increase_disc_conj@" ^ string_of_int piece_idx ] )

  let decrease_disc_conj piece_idx (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing number_of_disc_conj of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ( {
        param with
        shp =
          List.mapi param.shp ~f:(fun i ndc ->
              if i = piece_idx then max (ndc - 1) 0 else ndc);
      },
      actions @ [ "decrease_disc_conj@" ^ string_of_int piece_idx ] )

  let init_shape (param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing shape of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with shp = init.shp }, actions @ [ "init_shape" ])

  let increase_rfun_lexicos (param, actions) =
    Debug.print
    @@ lazy
         ("************* increasing number_of_rfun_lexicos of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with nl = param.nl + 1 }, actions @ [ "increase_rfun_lexicos" ])

  let decrease_rfun_lexicos (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing number_of_rfun_lexicos of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ( { param with nl = max (param.nl - 1) 0 },
      actions @ [ "decrease_rfun_lexicos" ] )

  let init_rfun_lexicos (param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing number_of_rfun_lexicos of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with nl = init.nl }, actions @ [ "init_rfun_lexicos" ])

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

  let set_inf_rfun_coeff (param, actions) =
    Debug.print
    @@ lazy
         ("************* setting upper_bound_rfun_coeff of "
         ^ Ident.name_of_tvar Arg.name
         ^ " to infinity ***************");
    ({ param with ubrc = None }, actions @ [ "set_inf_rfun_coeff" ])

  let increase_rfun_coeff threshold (param, actions) =
    match (param.ubrc, threshold) with
    | Some ubrc, Some thr when Z.Compare.(ubrc >= Z.of_int thr) ->
        set_inf_rfun_coeff (param, actions)
    | _, _ ->
        Debug.print
        @@ lazy
             ("************* increasing upper_bound_rfun_coeff of "
             ^ Ident.name_of_tvar Arg.name
             ^ "***************");
        ( {
            param with
            ubrc = Option.map param.ubrc ~f:(fun ubrc -> Z.(ubrc + one));
          },
          actions @ [ "increase_rfun_coeff" ] )

  let decrease_rfun_coeff (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing upper_bound_rfun_coeff of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ( {
        param with
        ubrc = Option.map param.ubrc ~f:(fun ubrc -> Z.(max (ubrc - one) zero));
      },
      actions @ [ "decrease_rfun_coeff" ] )

  let init_rfun_coeff (param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing upper_bound_rfun_coeff of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with ubrc = init.ubrc }, actions @ [ "init_rfun_coeff" ])

  let set_inf_rfun_const (param, actions) =
    Debug.print
    @@ lazy
         ("************* setting upper_bound_rfun_const of "
         ^ Ident.name_of_tvar Arg.name
         ^ " to infinity ***************");
    ({ param with ubrd = None }, actions @ [ "set_inf_rfun_const" ])

  let increase_rfun_const threshold (param, actions) =
    match (param.ubrd, threshold) with
    | Some ubrd, Some thr when Z.Compare.(ubrd >= Z.of_int thr) ->
        set_inf_rfun_const (param, actions)
    | _, _ ->
        Debug.print
        @@ lazy
             ("************* increasing upper_bound_rfun_const of "
             ^ Ident.name_of_tvar Arg.name
             ^ "***************");
        ( {
            param with
            ubrd = Option.map param.ubrd ~f:(fun ubrd -> Z.(ubrd + one));
          },
          actions @ [ "increase_rfun_const" ] )

  let decrease_rfun_const (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing upper_bound_rfun_const of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ( {
        param with
        ubrd = Option.map param.ubrd ~f:(fun ubrd -> Z.(max (ubrd - one) zero));
      },
      actions @ [ "decrease_rfun_const" ] )

  let init_rfun_const (param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing upper_bound_rfun_const of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with ubrd = init.ubrd }, actions @ [ "init_rfun_const" ])

  let set_inf_disc_coeff (param, actions) =
    Debug.print
    @@ lazy
         ("************* setting upper_bound_disc_coeff of "
         ^ Ident.name_of_tvar Arg.name
         ^ " to infinity ***************");
    ({ param with ubdc = None }, actions @ [ "set_inf_disc_coeff" ])

  let increase_disc_coeff threshold (param, actions) =
    match (param.ubdc, threshold) with
    | Some ubdc, Some thr when Z.Compare.(ubdc >= Z.of_int thr) ->
        set_inf_disc_coeff (param, actions)
    | _, _ ->
        Debug.print
        @@ lazy
             ("************* increasing upper_bound_disc_coeff of "
             ^ Ident.name_of_tvar Arg.name
             ^ "***************");
        ( {
            param with
            ubdc = Option.map param.ubdc ~f:(fun ubdc -> Z.(ubdc + one));
          },
          actions @ [ "increase_disc_coeff" ] )

  let decrease_disc_coeff (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing upper_bound_disc_coeff of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ( {
        param with
        ubdc = Option.map param.ubdc ~f:(fun ubdc -> Z.(max (ubdc - one) zero));
      },
      actions @ [ "decrease_disc_coeff" ] )

  let init_disc_coeff (param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing upper_bound_disc_coeff of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with ubdc = init.ubdc }, actions @ [ "init_disc_coeff" ])

  let set_inf_disc_const (param, actions) =
    Debug.print
    @@ lazy
         ("************* setting upper_bound_disc_const of "
         ^ Ident.name_of_tvar Arg.name
         ^ " to infinity ***************");
    ({ param with ubdd = None }, actions @ [ "set_inf_disc_const" ])

  let increase_disc_const threshold (param, actions) =
    match (param.ubdd, threshold) with
    | Some ubdd, Some thr when Z.Compare.(ubdd >= Z.of_int thr) ->
        set_inf_disc_const (param, actions)
    | _, _ ->
        Debug.print
        @@ lazy
             ("************* increasing upper_bound_disc_const of "
             ^ Ident.name_of_tvar Arg.name
             ^ "***************");
        ( {
            param with
            ubdd = Option.map param.ubdd ~f:(fun ubdd -> Z.(ubdd + one));
          },
          actions @ [ "increase_disc_const" ] )

  let decrease_disc_const (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing upper_bound_disc_const of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ( {
        param with
        ubdd = Option.map param.ubdd ~f:(fun ubdd -> Z.(max (ubdd - one) zero));
      },
      actions @ [ "decrease_disc_const" ] )

  let init_disc_const (param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing upper_bound_disc_const of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with ubdd = init.ubdd }, actions @ [ "init_disc_const" ])

  let increase_lexico_piece_conj (param, actions) =
    if param.nl >= List.length param.shp then
      let param, actions =
        increase_rfun_pieces
        @@ List.fold param.shp ~init:(param, actions)
             ~f:(Fn.flip increase_disc_conj)
      in
      increase_depth @@ init_rfun_lexicos
      @@ List.fold param.shp ~init:(param, actions) ~f:(fun acc _ ->
             increase_disc_conj 0 acc)
    else increase_rfun_lexicos (param, actions)

  let rec inner param_actions = function
    | [] -> param_actions
    | LexicoPieceConj :: labels ->
        inner
          (if config.fix_shape then param_actions
           else increase_lexico_piece_conj param_actions)
          labels
    | RFunCoeff :: labels ->
        inner
          (increase_rfun_coeff config.threshold_rfun_coeff param_actions)
          labels
    | RFunConst :: labels ->
        inner
          (increase_rfun_const config.threshold_rfun_const param_actions)
          labels
    | DiscCoeff :: labels ->
        inner
          (increase_disc_coeff config.threshold_disc_coeff param_actions)
          labels
    | DiscConst :: labels ->
        inner
          (increase_disc_const config.threshold_disc_const param_actions)
          labels
    | TimeOut :: _labels -> param_actions (* z3 may unexpectedly time out*)
    | QDep :: labels -> inner param_actions labels
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
      | "increase_rfun_lexicos" -> action (increase_rfun_lexicos param_actions)
      | "decrease_rfun_lexicos" -> action (decrease_rfun_lexicos param_actions)
      | "init_rfun_lexicos" -> action (init_rfun_lexicos param_actions)
      | "increase_rfun_pieces" -> action (increase_rfun_pieces param_actions)
      | "decrease_rfun_pieces" -> action (decrease_rfun_pieces param_actions)
      | "init_shape" -> action (init_shape param_actions)
      | "increase_depth" -> action (increase_depth param_actions)
      | "decrease_depth" -> action (decrease_depth param_actions)
      | "init_depth" -> action (init_depth param_actions)
      | "set_inf_rfun_coeff" -> action (set_inf_rfun_coeff param_actions)
      | "increase_rfun_coeff" -> action (increase_rfun_coeff None param_actions)
      | "decrease_rfun_coeff" -> action (decrease_rfun_coeff param_actions)
      | "init_rfun_coeff" -> action (init_rfun_coeff param_actions)
      | "set_inf_rfun_const" -> action (set_inf_rfun_const param_actions)
      | "increase_rfun_const" -> action (increase_rfun_const None param_actions)
      | "decrease_rfun_const" -> action (decrease_rfun_const param_actions)
      | "init_rfun_const" -> action (init_rfun_const param_actions)
      | "set_inf_disc_coeff" -> action (set_inf_disc_coeff param_actions)
      | "increase_disc_coeff" -> action (increase_disc_coeff None param_actions)
      | "decrease_disc_coeff" -> action (decrease_disc_coeff param_actions)
      | "init_disc_coeff" -> action (init_disc_coeff param_actions)
      | "set_inf_disc_const" -> action (set_inf_disc_const param_actions)
      | "increase_disc_const" -> action (increase_disc_const None param_actions)
      | "decrease_disc_const" -> action (decrease_disc_const param_actions)
      | "init_disc_const" -> action (init_disc_const param_actions)
      | "restart" -> action (restart param_actions)
      | "revert" -> action (revert param_actions)
      | "end" -> fst param_actions
      | s -> (
          let prefix = "increase_disc_conj@" in
          match String.chop_prefix s ~prefix with
          | Some res ->
              action (increase_disc_conj (int_of_string res) param_actions)
          | None -> (
              let prefix = "decrease_disc_conj@" in
              match String.chop_prefix s ~prefix with
              | Some res ->
                  action (decrease_disc_conj (int_of_string res) param_actions)
              | None -> failwith ("Unknown action: " ^ s)))
    in
    param := action (!param, [])

  let restart () = param := fst @@ restart (!param, [])
  let update_with_solution _ = assert false
  let sync _thre = assert false

  let _ =
    Debug.print
    @@ lazy
         (sprintf "************* initializing %s ***************"
            (Ident.name_of_tvar Arg.name));
    Debug.print @@ lazy (str_of ())
end
