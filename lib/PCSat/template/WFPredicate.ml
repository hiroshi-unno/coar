open Core
open Common.Util
open Ast
open Ast.LogicOld
open Function

module Config = struct
  type t = {
    verbose: bool;

    number_of_rfun_lexicos: int;
    number_of_rfun_pieces: int;
    upper_bound_rfun_coeff: int option;
    upper_bound_rfun_const: int option;
    number_of_disc_conj: int;
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
            "Invalid WFPredicate Configuration (%s): %s" filename msg
      end
    | Instance x -> Ok (Instance x)
end

module type ArgType = sig
  val name  : Ident.tvar
  val sorts : Sort.t list
end

type parameter = int * int * Z.t option * Z.t option * int * Z.t option * Z.t option * Z.t Set.Poly.t
type parameter_update_type +=
  | LexicoPieceConj
  | RFunCoeff
  | RFunConst
  | DiscCoeff
  | DiscConst

module Make (Cfg : Config.ConfigType) (Arg : ArgType) : Function.Type = struct
  let config = Cfg.config

  module Debug =
    Common.Debug.Make
      (val (Common.Debug.Config.(if config.verbose then enable else disable)))

  let param : parameter ref =
    ref (config.number_of_rfun_lexicos, config.number_of_rfun_pieces,
         (Option.map config.upper_bound_rfun_coeff ~f:Z.of_int),
         (Option.map config.upper_bound_rfun_const ~f:Z.of_int),
         config.number_of_disc_conj,
         (Option.map config.upper_bound_disc_coeff ~f:Z.of_int),
         (Option.map config.upper_bound_disc_const ~f:Z.of_int),
         (match config.disc_seeds with
          | None -> Set.Poly.singleton (Z.of_int 0)
          | Some ds -> List.map ds ~f:Z.of_int |> Set.Poly.of_list))

  let params_of () = SortEnv.of_sorts Arg.sorts
  let adjust_quals quals =
    let params = SortEnv.list_of @@ params_of () in
    let params_x, params_y = List.split_n params (List.length params / 2) in
    let rename_x_y = Formula.rename (SortEnv.from_to (SortEnv.of_list params_x) (SortEnv.of_list params_y)) in
    let rename_y_x = Formula.rename (SortEnv.from_to (SortEnv.of_list params_y) (SortEnv.of_list params_x)) in
    let fenv = Set.Poly.empty in (*TODO:generate fenv*)
    let quals =
      Set.Poly.fold quals ~init:Set.Poly.empty ~f:(fun quals phi ->
          let qual1 = Z3Smt.Z3interface.qelim fenv @@ Formula.exists (SortEnv.of_list params_y) phi in
          let qual2 = rename_y_x @@ Z3Smt.Z3interface.qelim fenv @@ Formula.exists (SortEnv.of_list params_x) phi in
          let quals = (*ToDo*)if Formula.is_bind qual1 || Set.Poly.is_empty (Formula.fvs_of qual1) then quals else Set.Poly.add quals qual1 in
          let quals = (*ToDo*)if Formula.is_bind qual2 || Set.Poly.is_empty (Formula.fvs_of qual2) then quals else Set.Poly.add quals qual2 in
          quals) in
    Set.Poly.union quals (Set.Poly.map quals ~f:rename_x_y)
  let gen_quals_terms (_old_depth, quals, terms) =
    (*TODO: generate quals and terms*)
    0, quals, terms
  let gen_template quals terms =
    let params = params_of () in
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
        (SortEnv.list_of params) in
    (*Debug.print @@ lazy (Formula.str_of tmpl);*)
    let tmpl =
      Logic.Term.mk_lambda (Logic.SortEnv.of_old_sort_env Logic.ExtTerm.of_old_sort params) @@
      Logic.ExtTerm.of_old_formula tmpl in
    (LexicoPieceConj, tmpl),
    ([(RFunCoeff, cnstr_of_rfun_coeffs |> Logic.ExtTerm.of_old_formula);
      (RFunConst, cnstr_of_rfun_const |> Logic.ExtTerm.of_old_formula);
      (DiscCoeff, cnstr_of_disc_coeffs |> Logic.ExtTerm.of_old_formula);
      (DiscConst, cnstr_of_disc_const |> Logic.ExtTerm.of_old_formula)]),
    temp_params, hole_qualifiers_map

  let restart (_nl, _np, _ubrc, _ubrd, _ndc, _ubdc, _ubdd, _ds) =
    Debug.print @@ lazy ("************* restarting " ^ Ident.name_of_tvar Arg.name ^ "***************");
    1, 1, Some Z.one, Some Z.zero, 0, Some Z.one, Some Z.zero, Set.Poly.singleton (Z.of_int 0)

  let update_lexico_piece_conj (nl, np, ubrc, ubrd, ndc, ubdc, ubdd, ds) =
    let nl', np', ndc' =
      if nl >= np then begin
        Debug.print @@ lazy ("************* updating number_of_rfun_pieces of " ^ Ident.name_of_tvar Arg.name ^ "***************");
        (*Debug.print @@ lazy ("************* updating number_of_disc_conj of " ^ Ident.name_of_tvar Arg.name ^ "***************");*)
        1, np+1, ndc+1
      end else begin
        Debug.print @@ lazy ("************* updating number_of_rfun_lexicos of " ^ Ident.name_of_tvar Arg.name ^ "***************");
        nl+1, np, ndc
      end
    in
    nl', np', ubrc, ubrd, ndc', ubdc, ubdd, ds

  let update_rfun_coeff (nl, np, ubrc, ubrd, ndc, ubdc, ubdd, ds) =
    Debug.print @@ lazy ("************* updating upper_bound_rfun_coeff of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    let ubrc' =
      match ubrc, config.threshold_rfun_coeff with
      | Some ubrc, Some thr when Z.Compare.(ubrc >= Z.of_int thr) -> None
      | _, _ -> Option.map ubrc ~f:(fun ubrc -> Z.(+) ubrc (Z.of_int 1))
    in
    nl, np, ubrc', ubrd, ndc, ubdc, ubdd, ds

  let update_rfun_const (nl, np, ubrc, ubrd, ndc, ubdc, ubdd, ds) =
    Debug.print @@ lazy ("************* updating upper_bound_rfun_const of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    let ubrd' =
      match ubrd, config.threshold_rfun_const with
      | Some ubrd, Some thr when Z.Compare.(ubrd >= Z.of_int thr) -> None
      | _, _ -> Option.map ubrd ~f:(fun ubrd -> Z.(+) ubrd (Z.of_int 1))
    in
    nl, np, ubrc, ubrd', ndc, ubdc, ubdd, ds

  let update_disc_coeff (nl, np, ubrc, ubrd, ndc, ubdc, ubdd, ds) =
    Debug.print @@ lazy ("************* updating upper_bound_disc_coeff of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    let ubdc' =
      match ubdc, config.threshold_disc_coeff with
      | Some ubdc, Some thr when Z.Compare.(ubdc >= Z.of_int thr) -> None
      | _, _ -> Option.map ubdc ~f:(fun ubdc -> Z.(+) ubdc (Z.of_int 1))
    in
    nl, np, ubrc, ubrd, ndc, ubdc', ubdd, ds

  let update_disc_const (nl, np, ubrc, ubrd, ndc, ubdc, ubdd, ds) =
    Debug.print @@ lazy ("************* updating upper_bound_disc_const of " ^ Ident.name_of_tvar Arg.name ^ "***************");
    let ubdd' =
      match ubdd, config.threshold_disc_const with
      | Some ubdd, Some thr when Z.Compare.(ubdd >= Z.of_int thr) -> None
      | _, _ -> Option.map ubdd ~f:(fun ubdd -> Z.(+) ubdd (Z.of_int 1))
    in
    nl, np, ubrc, ubrd, ndc, ubdc, ubdd', ds

  let next () = param := !param |> update_lexico_piece_conj |> update_rfun_coeff |> update_rfun_const |> update_disc_coeff |> update_disc_const

  let update_with_solution _ = assert false

  let update_with_labels labels =
    let rec inner param = function
      | [] -> param
      | LexicoPieceConj :: labels -> inner (update_lexico_piece_conj param) labels
      | RFunCoeff :: labels -> inner (update_rfun_coeff param) labels
      | RFunConst :: labels -> inner (update_rfun_const param) labels
      | DiscCoeff :: labels -> inner (update_disc_coeff param) labels
      | DiscConst :: labels -> inner (update_disc_const param) labels
      | TimeOut :: _labels -> param(* z3 may unexpectedly time out*)
      | _ -> assert false
    in
    param := inner !param @@ Set.Poly.to_list labels
  let rl_action _labels = assert false
  let restart () = param := restart !param

  let sync thre =
    let nl, np, ubrc, ubrd, ndc, ubdc, ubdd, ds = !param in
    let mx = max nl np
             |> max @@ Z.to_int (match ubrc with None -> Z.zero | Some n -> n)
             |> max @@ Z.to_int (match ubrd with None -> Z.zero | Some n -> n)
             |> max ndc
             |> max @@ Z.to_int (match ubdc with None -> Z.zero | Some n -> n)
             |> max @@ Z.to_int (match ubdd with None -> Z.zero | Some n -> n) in
    let mn = mx - thre in
    let param' = (max nl mn), (max np mn),
                 Option.map ubrc ~f:(Z.max (Z.of_int mn)),
                 Option.map ubrd ~f:(Z.max (Z.of_int mn)),
                 (max ndc mn),
                 Option.map ubdc ~f:(Z.max (Z.of_int mn)),
                 Option.map ubdd ~f:(Z.max (Z.of_int mn)),
                 ds in
    param := param'

  let str_of () =
    let nl, np, ubrc, ubrd, ndc, ubdc, ubdd, ds = !param in
    Printf.sprintf
      ("number of lexicographic : %d\n" ^^
       "number of piecewise : %d\n" ^^
       "upper bound of the sum of the abs of ranking function coefficients : %s\n" ^^
       "upper bound of the abs of ranking function constant : %s\n" ^^
       "number of discriminator conjuncts : %d\n" ^^
       "upper bound of the sum of the abs of discriminator coefficients : %s\n" ^^
       "upper bound of the abs of discriminator constant : %s\n" ^^
       "seeds : %s")
      nl np
      (match ubrc with None -> "N/A" | Some ubrc -> Z.to_string ubrc)
      (match ubrd with None -> "N/A" | Some ubrd -> Z.to_string ubrd)
      ndc
      (match ubdc with None -> "N/A" | Some ubdc -> Z.to_string ubdc)
      (match ubdd with None -> "N/A" | Some ubdd -> Z.to_string ubdd)
      (String.concat ~sep:"," @@ Set.Poly.to_list @@ Set.Poly.map ds ~f:Z.to_string)

  let _ =
    Debug.print @@ lazy ("************* initializing " ^ Ident.name_of_tvar Arg.name ^ " ***************");
    Debug.print @@ lazy (str_of ())
end
