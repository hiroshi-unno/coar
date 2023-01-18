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

    shape: int list;
    number_of_rfun_lexicos: int;

    upper_bound_rfun_coeff: int option;
    upper_bound_rfun_const: int option;
    upper_bound_disc_coeff: int option;
    upper_bound_disc_const: int option;
    disc_seeds: int list option;

    norm_type: int;
    use_ifte: bool;
    lower_bound_rfun_coeff: int option;
    lower_bound_disc_coeff: int option;
    bound_each_rfun_coeff: int option;
    bound_each_disc_coeff: int option;
    threshold_rfun_coeff: int option;
    threshold_rfun_const: int option;
    threshold_disc_coeff: int option;
    threshold_disc_const: int option;

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
            "Invalid WFPredicateFlex Configuration (%s): %s" filename msg
      end
    | Instance x -> Ok (Instance x)
end

module type ArgType = sig
  val name  : Ident.tvar
  val sorts : Sort.t list
  val id : int option
end

type parameter = int list * int * Z.t option * Z.t option * Z.t option * Z.t option * Z.t Set.Poly.t
type parameter_update_type +=
  | LexicoPieceConj
  | RFunCoeff
  | RFunConst
  | DiscCoeff
  | DiscConst

type state = int list * int * int option * int option * int option * int option * bool * bool * bool * bool * bool * bool [@@deriving to_yojson]
let state_of ((shp, nl, ubrc, ubrd, ubdc, ubdd, _ds) : parameter) labels : state =
  (shp, nl, Option.map ~f:Z.to_int ubrc, Option.map ~f:Z.to_int ubrd, Option.map ~f:Z.to_int ubdc, Option.map ~f:Z.to_int ubdd,
   Set.Poly.mem labels LexicoPieceConj (* ToDo: this is always true *),
   Set.Poly.mem labels RFunCoeff,
   Set.Poly.mem labels RFunConst,
   Set.Poly.mem labels DiscCoeff,
   Set.Poly.mem labels DiscConst,
   Set.Poly.mem labels TimeOut)

module Make (Cfg : Config.ConfigType) (Arg : ArgType) : Function.Type = struct
  let config = Cfg.config

  let id = Arg.id
  module Debug = Debug.Make (val (Debug.Config.(if config.verbose then enable else disable)))
  let _ = Debug.set_id id

  let param : parameter ref =
    ref (config.shape, config.number_of_rfun_lexicos,
         (Option.map config.upper_bound_rfun_coeff ~f:Z.of_int),
         (Option.map config.upper_bound_rfun_const ~f:Z.of_int),
         (Option.map config.upper_bound_disc_coeff ~f:Z.of_int),
         (Option.map config.upper_bound_disc_const ~f:Z.of_int),
         (match config.disc_seeds with
          | None -> Set.Poly.singleton (Z.of_int 0)
          | Some ds -> List.map ds ~f:Z.of_int |> Set.Poly.of_list))

  let params_of ~tag = ignore tag; sort_env_list_of_sorts Arg.sorts
  let adjust_quals ~tag quals =
    let params = params_of ~tag in
    let params_x, params_y = List.split_n params (List.length params / 2) in
    let rename_x_y = Formula.rename (tvar_map_of_sort_env_list params_x params_y) in
    let rename_y_x = Formula.rename (tvar_map_of_sort_env_list params_y params_x) in
    let fenv = Map.Poly.empty in (*TODO:generate fenv*)
    let quals =
      Set.Poly.fold quals ~init:Set.Poly.empty ~f:(fun quals phi ->
          let qual1 = Z3Smt.Z3interface.qelim ~id fenv @@ Formula.exists params_y phi in
          let qual2 = rename_y_x @@ Z3Smt.Z3interface.qelim ~id fenv @@ Formula.exists params_x phi in
          let quals = (*ToDo*)if Formula.is_bind qual1 || Set.Poly.is_empty (Formula.fvs_of qual1) then quals else Set.Poly.add quals qual1 in
          let quals = (*ToDo*)if Formula.is_bind qual2 || Set.Poly.is_empty (Formula.fvs_of qual2) then quals else Set.Poly.add quals qual2 in
          quals) in
    Set.Poly.union quals (Set.Poly.map quals ~f:rename_x_y)
  let init_quals _ _ = ()
  let gen_quals_terms ~tag (_old_depth, quals, _qdeps, terms) =
    (*TODO: generate quals and terms*)
    ignore tag;
    0, quals, _qdeps, terms
  let gen_template ~tag quals _qdeps terms =
    let params = params_of ~tag in
    let temp_params, hole_qualifiers_map, tmpl,
        cnstr_of_rfun_coeffs, cnstr_of_rfun_const, cnstr_of_disc_coeffs, cnstr_of_disc_const =
      Generator.gen_simplified_wf_predicate
        (*config.use_ifte*)
        (List.dedup_and_sort ~compare:Stdlib.compare quals)
        (List.dedup_and_sort ~compare:Stdlib.compare terms)
        !param
        (config.norm_type,
         Option.map config.lower_bound_rfun_coeff ~f:Z.of_int,
         Option.map config.lower_bound_disc_coeff ~f:Z.of_int,
         Option.map config.bound_each_rfun_coeff ~f:Z.of_int,
         Option.map config.bound_each_disc_coeff ~f:Z.of_int)
        params in
    (*Debug.print @@ lazy (Formula.str_of tmpl);*)
    let tmpl =
      Logic.Term.mk_lambda (Logic.of_old_sort_env_list Logic.ExtTerm.of_old_sort params) @@
      Logic.ExtTerm.of_old_formula tmpl in
    (LexicoPieceConj, tmpl),
    ([(RFunCoeff, cnstr_of_rfun_coeffs |> Logic.ExtTerm.of_old_formula);
      (RFunConst, cnstr_of_rfun_const |> Logic.ExtTerm.of_old_formula);
      (DiscCoeff, cnstr_of_disc_coeffs |> Logic.ExtTerm.of_old_formula);
      (DiscConst, cnstr_of_disc_const |> Logic.ExtTerm.of_old_formula)]),
    temp_params, hole_qualifiers_map

  let restart (_shp, _nl, _ubrc, _ubrd, _ubdc, _ubdd, _ds) =
    Debug.print @@ lazy ("************* restarting " ^ Ident.name_of_tvar Arg.name ^ "***************");
    [0], 1, Some Z.one, Some Z.zero, Some Z.one, Some Z.zero, Set.Poly.singleton (Z.of_int 0)

  let last_non_timeout_param = ref !param
  let revert (_shp, _nl, _ubrc, _ubrd, _ubdc, _ubdd, _ds) =
    Debug.print @@ lazy ("************* reverting " ^ Ident.name_of_tvar Arg.name ^ "***************");
    !last_non_timeout_param

  let increase_rfun_pieces (shp, nl, ubrc, ubrd, ubdc, ubdd, ds) =
    Debug.print @@ lazy ("************* increasing number_of_rfun_pieces of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    0 :: shp, nl, ubrc, ubrd, ubdc, ubdd, ds

  let increase_disc_conj piece_idx (shp, nl, ubrc, ubrd, ubdc, ubdd, ds) =
    Debug.print @@ lazy ("************* increasing number_of_disc_conj of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    List.mapi shp ~f:(fun i ndc -> if i = piece_idx then ndc + 1 else ndc), nl, ubrc, ubrd, ubdc, ubdd, ds

  let increase_rfun_lexicos (shp, nl, ubrc, ubrd, ubdc, ubdd, ds) =
    Debug.print @@ lazy ("************* increasing number_of_rfun_lexicos of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    shp, nl+1, ubrc, ubrd, ubdc, ubdd, ds

  let increase_lexico_piece_conj (shp, nl, ubrc, ubrd, ubdc, ubdd, ds) =
    if nl >= List.length shp then begin
      Debug.print @@ lazy ("************* restarting number_of_rfun_lexicos of " ^ Ident.name_of_tvar Arg.name ^ "***************");
      Debug.print @@ lazy ("************* increasing number_of_rfun_pieces of " ^ Ident.name_of_tvar Arg.name ^ "***************");
      Debug.print @@ lazy ("************* increasing number_of_disc_conj of " ^ Ident.name_of_tvar Arg.name ^ "***************");
      (*ToDo*)List.length shp :: List.map shp ~f:(fun ndc -> ndc + 1), 1, ubrc, ubrd, ubdc, ubdd, ds
    end else increase_rfun_lexicos (shp, nl, ubrc, ubrd, ubdc, ubdd, ds)

  let increase_rfun_coeff threshold (shp, nl, ubrc, ubrd, ubdc, ubdd, ds) =
    Debug.print @@ lazy ("************* increasing upper_bound_rfun_coeff of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    let ubrc' =
      match ubrc, threshold with
      | Some ubrc, Some thr when Z.Compare.(ubrc >= Z.of_int thr) -> None
      | _, _ -> Option.map ubrc ~f:(fun ubrc -> Z.(+) ubrc (Z.of_int 1))
    in
    shp, nl, ubrc', ubrd, ubdc, ubdd, ds

  let increase_rfun_const threshold (shp, nl, ubrc, ubrd, ubdc, ubdd, ds) =
    Debug.print @@ lazy ("************* increasing upper_bound_rfun_const of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    let ubrd' =
      match ubrd, threshold with
      | Some ubrd, Some thr when Z.Compare.(ubrd >= Z.of_int thr) -> None
      | _, _ -> Option.map ubrd ~f:(fun ubrd -> Z.(+) ubrd (Z.of_int 1))
    in
    shp, nl, ubrc, ubrd', ubdc, ubdd, ds

  let increase_disc_coeff threshold (shp, nl, ubrc, ubrd, ubdc, ubdd, ds) =
    Debug.print @@ lazy ("************* increasing upper_bound_disc_coeff of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    let ubdc' =
      match ubdc, threshold with
      | Some ubdc, Some thr when Z.Compare.(ubdc >= Z.of_int thr) -> None
      | _, _ -> Option.map ubdc ~f:(fun ubdc -> Z.(+) ubdc (Z.of_int 1))
    in
    shp, nl, ubrc, ubrd, ubdc', ubdd, ds

  let increase_disc_const threshold (shp, nl, ubrc, ubrd, ubdc, ubdd, ds) =
    Debug.print @@ lazy ("************* increasing upper_bound_disc_const of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    let ubdd' =
      match ubdd, threshold with
      | Some ubdd, Some thr when Z.Compare.(ubdd >= Z.of_int thr) -> None
      | _, _ -> Option.map ubdd ~f:(fun ubdd -> Z.(+) ubdd (Z.of_int 1))
    in
    shp, nl, ubrc, ubrd, ubdc, ubdd', ds

  let set_inf_rfun_coeff (shp, nl, _ubrc, ubrd, ubdc, ubdd, ds) =
    Debug.print @@ lazy ("************* setting upper_bound_rfun_coeff of " ^ Ident.name_of_tvar Arg.name ^ " to infinity ***************");
    let ubrc' = None in
    shp, nl, ubrc', ubrd, ubdc, ubdd, ds

  let set_inf_rfun_const (shp, nl, ubrc, _ubrd, ubdc, ubdd, ds) =
    Debug.print @@ lazy ("************* setting upper_bound_rfun_const of " ^ Ident.name_of_tvar Arg.name ^ " to infinity ***************");
    let ubrd' = None in
    shp, nl, ubrc, ubrd', ubdc, ubdd, ds

  let set_inf_disc_coeff (shp, nl, ubrc, ubrd, _ubdc, ubdd, ds) =
    Debug.print @@ lazy ("************* setting upper_bound_disc_coeff of " ^ Ident.name_of_tvar Arg.name ^ " to infinity ***************");
    let ubdc' = None in
    shp, nl, ubrc, ubrd, ubdc', ubdd, ds

  let set_inf_disc_const (shp, nl, ubrc, ubrd, ubdc, _ubdd, ds) =
    Debug.print @@ lazy ("************* setting upper_bound_disc_const of " ^ Ident.name_of_tvar Arg.name ^ " to infinity ***************");
    let ubdd' = None in
    shp, nl, ubrc, ubrd, ubdc, ubdd', ds

  let next () = param :=
      !param
      |> (if config.fix_shape then Fn.id else increase_lexico_piece_conj)
      |> increase_rfun_coeff config.threshold_rfun_coeff
      |> increase_rfun_const config.threshold_rfun_const
      |> increase_disc_coeff config.threshold_disc_coeff
      |> increase_disc_const config.threshold_disc_const

  let update_with_solution _ = assert false

  let update_with_labels labels =
    let rec inner param = function
      | [] -> param
      | LexicoPieceConj :: labels -> inner (if config.fix_shape then param else increase_lexico_piece_conj param) labels
      | RFunCoeff :: labels -> inner (increase_rfun_coeff config.threshold_rfun_coeff param) labels
      | RFunConst :: labels -> inner (increase_rfun_const config.threshold_rfun_const param) labels
      | DiscCoeff :: labels -> inner (increase_disc_coeff config.threshold_disc_coeff param) labels
      | DiscConst :: labels -> inner (increase_disc_const config.threshold_disc_const param) labels
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
      | "increase_rfun_lexicos" -> action (increase_rfun_lexicos param)
      | "increase_rfun_pieces" -> action (increase_rfun_pieces param)
      | "increase_rfun_coeff" -> action (increase_rfun_coeff None param)
      | "increase_rfun_const" -> action (increase_rfun_const None param)
      | "set_inf_rfun_coeff" -> action (set_inf_rfun_coeff param)
      | "set_inf_rfun_const" -> action (set_inf_rfun_const param)
      | "increase_disc_coeff" -> action (increase_disc_coeff None param)
      | "increase_disc_const" -> action (increase_disc_const None param)
      | "set_inf_disc_coeff" -> action (set_inf_disc_coeff param)
      | "set_inf_disc_const" -> action (set_inf_disc_const param)
      | "restart" -> action (restart param)
      | "revert" -> action (revert param)
      | "end" -> param
      | s ->
        let prefix = "increase_disc_conj@" in
        match String.chop_prefix s ~prefix with
        | Some res ->
          action (increase_disc_conj (int_of_string res) param)
        | None -> failwith ("Unknown action: " ^ s)
    in
    param := action !param
  let restart () = param := restart !param

  let sync _thre = ()
  (*let np, ndc, nl, ubrc, ubrd, ubdc, ubdd, ds = !param in
    let mx = max nl np
           |> max @@ Z.to_int (match ubrc with None -> Z.zero | Some n -> n)
           |> max @@ Z.to_int (match ubrd with None -> Z.zero | Some n -> n)
           |> max ndc
           |> max @@ Z.to_int (match ubdc with None -> Z.zero | Some n -> n)
           |> max @@ Z.to_int (match ubdd with None -> Z.zero | Some n -> n) in
    let mn = mx - thre in
    let param' = (max np mn), (max ndc mn), (max nl mn),
               Option.map ubrc ~f:(Z.max (Z.of_int mn)),
               Option.map ubrd ~f:(Z.max (Z.of_int mn)),
               Option.map ubdc ~f:(Z.max (Z.of_int mn)),
               Option.map ubdd ~f:(Z.max (Z.of_int mn)),
               ds in
    param := param'*)

  let in_space () = true

  let str_of () =
    let shp, nl, ubrc, ubrd, ubdc, ubdd, ds = !param in
    Printf.sprintf
      ("shape : [%s]\n" ^^
       "number of lexicographic : %d\n" ^^
       "upper bound of the sum of the abs of ranking function coefficients : %s\n" ^^
       "upper bound of the abs of ranking function constant : %s\n" ^^
       "upper bound of the sum of the abs of discriminator coefficients : %s\n" ^^
       "upper bound of the abs of discriminator constant : %s\n" ^^
       "seeds : %s")
      (String.concat_map_list ~sep:";" shp ~f:string_of_int) nl
      (match ubrc with None -> "N/A" | Some ubrc -> Z.to_string ubrc)
      (match ubrd with None -> "N/A" | Some ubrd -> Z.to_string ubrd)
      (match ubdc with None -> "N/A" | Some ubdc -> Z.to_string ubdc)
      (match ubdd with None -> "N/A" | Some ubdd -> Z.to_string ubdd)
      (String.concat_set ~sep:"," @@ Set.Poly.map ds ~f:Z.to_string)

  let _ =
    Debug.print @@ lazy ("************* initializing " ^ Ident.name_of_tvar Arg.name ^ " ***************");
    Debug.print @@ lazy (str_of ())
end
