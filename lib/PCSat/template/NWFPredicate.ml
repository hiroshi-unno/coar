open Core
open Common
open Common.Ext
open Ast
open Ast.LogicOld
open PCSatCommon.HypSpace
open Function

module type ArgType = sig
  val name : Ident.tvar
  val sorts : Sort.t list

  (*val dtenv : LogicOld.DTEnv.t*)
  val fenv : LogicOld.FunEnv.t
  val id : int option
  val tag_infos : (Ident.tvar, Sort.t list) Hashtbl.Poly.t
end

type parameter = {
  np : int;
  ndc : int;
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
  int
  * int
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
  ( param.np,
    param.ndc,
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

module Make (Cfg : WFPredicate.Config.ConfigType) (Arg : ArgType) :
  Function.Type = struct
  let config = Cfg.config
  let id = Arg.id

  module Debug =
    Debug.Make ((val Debug.Config.(if config.verbose then enable else disable)))

  let _ = Debug.set_id id

  let param =
    ref
      {
        np = config.number_of_rfun_pieces;
        ndc = config.number_of_disc_conj;
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
      np = 1;
      ndc = 0;
      nl = 1;
      depth = 0;
      ubrc = Some Z.one;
      ubrd = Some Z.zero;
      ubdc = Some Z.one;
      ubdd = Some Z.zero;
      ds = Set.Poly.singleton Z.zero;
    }

  let name_of () = Arg.name
  let kind_of () = Kind.str_of Kind.WF
  let sort_of () = Sort.mk_fun @@ Arg.sorts (*ToDo*) @ [ T_bool.SBool ]

  let params_of ~tag =
    let params_of_idx (tag_l, tag_r) =
      let sorts_l = Hashtbl.Poly.find_exn Arg.tag_infos tag_l in
      let sorts_r = Hashtbl.Poly.find_exn Arg.tag_infos tag_r in
      LogicOld.sort_env_list_of_sorts ~pre:"" @@ Arg.sorts @ sorts_l @ sorts_r
    in
    params_of_idx @@ Option.value_exn tag

  let show_state ?(config = PCSatCommon.RLConfig.disabled) labels =
    if config.show_num_args then
      Debug.print_stdout
      @@ lazy
           (sprintf "args: %s"
           @@ String.concat_map_list ~sep:"," ~f:(fun (tag, sorts) ->
                  sprintf "%s:(%d)" (Ident.name_of_tvar tag) (List.length sorts))
           @@ Hashtbl.Poly.to_alist Arg.tag_infos);
    Debug.print_stdout
    @@ lazy
         (sprintf "state of %s: %s" (Ident.name_of_tvar (name_of ()))
         @@ Yojson.Safe.to_string @@ state_to_yojson @@ state_of !param labels);
    Out_channel.flush Out_channel.stdout

  let str_of () =
    sprintf
      ("number of piecewise : %d\n"
     ^^ "number of discriminator conjuncts : %d\n"
     ^^ "number of lexicographic : %d\n" ^^ "depth : %d\n"
     ^^ "upper bound of the sum of the abs of ranking function coefficients : %s\n"
     ^^ "upper bound of the abs of ranking function constant : %s\n"
     ^^ "upper bound of the sum of the abs of discriminator coefficients : %s\n"
     ^^ "upper bound of the abs of discriminator constant : %s\n"
     ^^ "seeds : %s")
      !param.np !param.ndc !param.nl !param.depth
      (match !param.ubrc with None -> "N/A" | Some ubrc -> Z.to_string ubrc)
      (match !param.ubrd with None -> "N/A" | Some ubrd -> Z.to_string ubrd)
      (match !param.ubdc with None -> "N/A" | Some ubdc -> Z.to_string ubdc)
      (match !param.ubdd with None -> "N/A" | Some ubdd -> Z.to_string ubdd)
      (String.concat_set ~sep:"," @@ Set.Poly.map !param.ds ~f:Z.to_string)

  let in_space () = true (* TODO *)

  let params_of_idx_l tag_l =
    let sorts_l = Hashtbl.Poly.find_exn Arg.tag_infos tag_l in
    LogicOld.sort_env_list_of_sorts ~pre:"" @@ Arg.sorts @ sorts_l
    |> Fn.flip List.drop (List.length Arg.sorts)

  let params_of_idx_r tag_l tag_r =
    let sorts_l = Hashtbl.Poly.find_exn Arg.tag_infos tag_l in
    let sorts_r = Hashtbl.Poly.find_exn Arg.tag_infos tag_r in
    LogicOld.sort_env_list_of_sorts ~pre:"" @@ Arg.sorts @ sorts_l @ sorts_r
    |> Fn.flip List.drop (List.length Arg.sorts + List.length sorts_l)

  let adjust_quals ~tag quals =
    let idxl, idxr = Option.value_exn tag in
    let quals = Qualifier.AllTheory.add_quals_form_affine_eq_quals quals in
    if Stdlib.(idxl <> idxr) then quals
    else
      let params_x, params_y =
        (params_of_idx_l idxl, params_of_idx_r idxl idxr)
      in
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
            (if Formula.is_bind qual1 || Set.is_empty (Formula.fvs_of qual1)
             then Set.Poly.empty
             else Set.Poly.of_list [ qual1; rename_x_y qual1 ])
            (if Formula.is_bind qual2 || Set.is_empty (Formula.fvs_of qual2)
             then Set.Poly.empty
             else Set.Poly.of_list [ rename_y_x qual2; qual2 ]))

  let rcs, dcs, qds, qualmapl, qualmapr =
    let init_qualmap () =
      Hashtbl.Poly.map Arg.tag_infos ~f:(fun _ -> Set.Poly.empty)
    in
    Hashtbl.Poly.
      (create (), create (), create (), init_qualmap (), init_qualmap ())

  let reset_paramvars () =
    Hashtbl.Poly.(
      clear rcs;
      clear dcs;
      clear qds)

  let x_i i = Ident.Tvar (sprintf "x%d" (i + 1))

  let rec init_quals tag quals =
    let quals_with quals params =
      let vs = Set.Poly.of_list @@ List.map params ~f:fst in
      Set.filter quals ~f:(fun q ->
          Set.for_all (Formula.tvs_of q) ~f:(Set.mem vs))
    in
    let idxl, idxr = Option.value_exn tag in
    let params = LogicOld.sort_env_list_of_sorts ~pre:"" Arg.sorts in
    let params_x, params_y =
      (params_of_idx_l idxl, params_of_idx_r idxl idxr)
    in
    let quals = adjust_quals ~tag quals in
    let qualsl = quals_with quals (params @ params_x) in
    let qualsr = quals_with quals (params @ params_y) in
    let subst_y =
      Map.Poly.of_alist_exn
      @@ List.mapi (params @ params_y) ~f:(fun i (x, _) -> (x, x_i i))
    in
    let qualsr = Set.Poly.map ~f:(Formula.rename subst_y) qualsr in
    if Stdlib.(idxl <> idxr) then (
      init_quals (Some (idxl, idxl)) qualsl;
      init_quals (Some (idxr, idxr)) qualsr);
    Hashtbl.Poly.update qualmapl idxl ~f:(function
      | Some quals -> Set.union quals qualsl
      | None -> qualsl);
    Hashtbl.Poly.update qualmapr idxr ~f:(function
      | Some quals -> Set.union quals qualsr
      | None -> qualsr)

  let update_hspace ~tag hspace =
    ignore tag;
    let qualsl =
      Hashtbl.Poly.find_exn qualmapl @@ fst @@ Option.value_exn tag
    in
    let qualsr =
      let tag_l, tag_r = Option.value_exn tag in
      let qualsr = Hashtbl.Poly.find_exn qualmapr tag_r in
      let sorts_l = Hashtbl.Poly.find_exn Arg.tag_infos tag_l in
      let sorts_r = Hashtbl.Poly.find_exn Arg.tag_infos tag_r in
      let subst =
        Map.Poly.of_alist_exn
        @@ List.mapi (Arg.sorts @ sorts_r) ~f:(fun i _ ->
               if i < List.length Arg.sorts then (x_i i, x_i i)
               else (x_i i, x_i (i + List.length sorts_l)))
      in
      Set.Poly.map qualsr ~f:(Formula.rename subst)
    in
    let hspace =
      {
        hspace with
        quals = (if true (*ToDo*) then Set.Poly.empty else hspace.quals);
      }
    in
    let hspace =
      Qualifier.AllTheory.qualifiers_of ~fenv:Arg.fenv !param.depth hspace
    in
    { hspace with quals = Set.Poly.union_list [ hspace.quals; qualsl; qualsr ] }

  let gen_template ~tag ~ucore hspace =
    ignore ucore;
    let idxl, idxr = Option.value_exn tag in
    let real_name = Ident.mk_nwf_tvar Arg.name idxl idxr in
    let ( temp_params,
          hole_qualifiers_map,
          tmpl,
          cnstr_of_rfun_coeffs,
          cnstr_of_rfun_const,
          cnstr_of_disc_coeffs,
          cnstr_of_disc_const ) =
      Generator.gen_simplified_nwf_predicate
        (*config.use_ifte*)
        (Set.to_list hspace.quals)
        (Set.to_list hspace.terms) (rcs, dcs, qds)
        ( List.init !param.np ~f:(fun _ -> !param.ndc),
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
        ( LogicOld.sort_env_list_of_sorts ~pre:"" Arg.sorts,
          idxl,
          params_of_idx_l idxl,
          idxr,
          params_of_idx_r idxl idxr )
    in
    Debug.print
    @@ lazy
         (sprintf "[%s] predicate template:\n  %s"
            (Ident.name_of_tvar real_name)
            (Formula.str_of tmpl));
    Debug.print
    @@ lazy
         (sprintf "[%s] cnstr_of_rfun_coeffs:\n  %s"
            (Ident.name_of_tvar real_name)
            (Formula.str_of cnstr_of_rfun_coeffs));
    Debug.print
    @@ lazy
         (sprintf "[%s] cnstr_of_rfun_const:\n  %s"
            (Ident.name_of_tvar real_name)
            (Formula.str_of cnstr_of_rfun_const));
    Debug.print
    @@ lazy
         (sprintf "[%s] cnstr_of_disc_coeffs:\n  %s"
            (Ident.name_of_tvar real_name)
            (Formula.str_of cnstr_of_disc_coeffs));
    Debug.print
    @@ lazy
         (sprintf "[%s] cnstr_of_disc_const:\n  %s"
            (Ident.name_of_tvar real_name)
            (Formula.str_of cnstr_of_disc_const));
    let tmpl =
      let params = params_of ~tag in
      Logic.(Term.mk_lambda (of_old_sort_env_list params))
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
    ({ param with np = param.np + 1 }, actions @ [ "increase_rfun_pieces" ])

  let decrease_rfun_pieces (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing number_of_rfun_pieces of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ( { param with np = max (param.np - 1) 0 },
      actions @ [ "decrease_rfun_pieces" ] )

  let init_rfun_pieces (param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing number_of_rfun_pieces of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with np = init.np }, actions @ [ "init_rfun_pieces" ])

  let increase_disc_conj (param, actions) =
    Debug.print
    @@ lazy
         ("************* increasing number_of_disc_conj of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with ndc = param.ndc + 1 }, actions @ [ "increase_disc_conj" ])

  let decrease_disc_conj (param, actions) =
    Debug.print
    @@ lazy
         ("************* decreasing number_of_disc_conj of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ( { param with ndc = max (param.ndc - 1) 0 },
      actions @ [ "decrease_disc_conj" ] )

  let init_disc_conj (param, actions) =
    Debug.print
    @@ lazy
         ("************* initializing number_of_disc_conj of "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    ({ param with ndc = init.ndc }, actions @ [ "init_disc_conj" ])

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
    if param.nl >= param.np then
      increase_depth @@ increase_disc_conj @@ increase_rfun_pieces
      @@ init_rfun_lexicos (param, actions)
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
    reset_paramvars ();
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
      | "init_rfun_pieces" -> action (init_rfun_pieces param_actions)
      | "increase_disc_conj" -> action (increase_disc_conj param_actions)
      | "decrease_disc_conj" -> action (decrease_disc_conj param_actions)
      | "init_disc_conj" -> action (init_disc_conj param_actions)
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
      | s -> failwith ("Unknown action: " ^ s)
    in
    param := action (!param, [])

  let restart () = param := fst @@ restart (!param, [])
  let update_with_solution _ = assert false
  let sync _thre = assert false
  (*let np, ndc, nl, depth, ubrc, ubrd, ubdc, ubdd, ds = !param in
    let mx = max nl np
           |> max @@ Z.to_int (match ubrc with None -> Z.zero | Some n -> n)
           |> max @@ Z.to_int (match ubrd with None -> Z.zero | Some n -> n)
           |> max ndc
           |> max @@ Z.to_int (match ubdc with None -> Z.zero | Some n -> n)
           |> max @@ Z.to_int (match ubdd with None -> Z.zero | Some n -> n) in
    let mn = mx - thre in
    let param' = (max np mn), (max ndc mn), (max nl mn), (max depth mn),
               Option.map ubrc ~f:(Z.max (Z.of_int mn)),
               Option.map ubrd ~f:(Z.max (Z.of_int mn)),
               Option.map ubdc ~f:(Z.max (Z.of_int mn)),
               Option.map ubdd ~f:(Z.max (Z.of_int mn)),
               ds in
    param := param'*)

  let _ =
    Debug.print
    @@ lazy
         (sprintf "************* initializing %s ***************"
            (Ident.name_of_tvar Arg.name));
    Debug.print @@ lazy (str_of ())
end

let modules = Hashtbl.Poly.create ()

let make ~(id : int option) ~(name : Ident.tvar) config arg =
  match Hashtbl.Poly.find modules (id, name) with
  | Some m -> m
  | None ->
      let (module Config : WFPredicate.Config.ConfigType) = config in
      let (module Arg : ArgType) = arg in
      (module Make (Config) (Arg) : Function.Type) |> fun m ->
      Hashtbl.Poly.add_exn modules ~key:(id, name) ~data:m;
      m
