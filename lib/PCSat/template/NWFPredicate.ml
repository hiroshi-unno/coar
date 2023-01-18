open Core
open Common
open Common.Ext
open Ast
open Ast.LogicOld
open Function
module type ArgType = sig
  val public_name  : Ident.tvar
  val dtenv : LogicOld.DTEnv.t
  val fenv : LogicOld.FunEnv.t
  val id    : int option
  val parameter_sorts : Sort.t list
  val tag_infos : (Ident.tvar, Sort.t list) Hashtbl.Poly.t
end

type parameter = int * int * int * int * Z.t option * Z.t option * Z.t option * Z.t option * Z.t Set.Poly.t
type parameter_update_type +=
  | LexicoPieceConj
  | RFunCoeff
  | RFunConst
  | DiscCoeff
  | DiscConst

type state = int * int * int * int * int option * int option * int option * int option * bool * bool * bool * bool * bool * bool [@@deriving to_yojson]
let state_of ((np, ndc, nl, depth, ubrc, ubrd, ubdc, ubdd, _ds) : parameter) labels : state =
  (np, ndc, nl, depth, Option.map ~f:Z.to_int ubrc, Option.map ~f:Z.to_int ubrd, Option.map ~f:Z.to_int ubdc, Option.map ~f:Z.to_int ubdd,
   Set.Poly.mem labels LexicoPieceConj (* ToDo: this is always true *),
   Set.Poly.mem labels RFunCoeff,
   Set.Poly.mem labels RFunConst,
   Set.Poly.mem labels DiscCoeff,
   Set.Poly.mem labels DiscConst,
   Set.Poly.mem labels TimeOut)

module Make (Cfg : WFPredicate.Config.ConfigType) (Arg : ArgType): Function.Type = struct
  let config = Cfg.config
  let id = Arg.id

  module Debug = Debug.Make (val (Debug.Config.(if config.verbose then enable else disable)))
  let _ = Debug.set_id id

  let param : parameter ref =
    ref (config.number_of_rfun_pieces, config.number_of_disc_conj, config.number_of_rfun_lexicos, config.depth,
         (Option.map config.upper_bound_rfun_coeff ~f:Z.of_int),
         (Option.map config.upper_bound_rfun_const ~f:Z.of_int),
         (Option.map config.upper_bound_disc_coeff ~f:Z.of_int),
         (Option.map config.upper_bound_disc_const ~f:Z.of_int),
         (match config.disc_seeds with
          | None -> Set.Poly.singleton (Z.of_int 0)
          | Some ds -> List.map ds ~f:Z.of_int |> Set.Poly.of_list))

  let parameter_params_of () =
    LogicOld.sort_env_list_of_sorts ~pre:"" @@ Arg.parameter_sorts
  let params_of_idx (tag_l, tag_r) =
    let sorts_l = Hashtbl.Poly.find_exn Arg.tag_infos tag_l in
    let sorts_r = Hashtbl.Poly.find_exn Arg.tag_infos tag_r in
    LogicOld.sort_env_list_of_sorts ~pre:"" @@ Arg.parameter_sorts @ sorts_l @ sorts_r
  let params_of_idx_l tag_l =
    let sorts_l = Hashtbl.Poly.find_exn Arg.tag_infos tag_l in
    LogicOld.sort_env_list_of_sorts ~pre:"" @@ Arg.parameter_sorts @ sorts_l
    |> (fun l -> List.drop l (List.length Arg.parameter_sorts))

  let params_of_idx_r tag_l tag_r =
    let sorts_l = Hashtbl.Poly.find_exn Arg.tag_infos tag_l in
    let sorts_r = Hashtbl.Poly.find_exn Arg.tag_infos tag_r in
    LogicOld.sort_env_list_of_sorts ~pre:"" @@ Arg.parameter_sorts @ sorts_l @ sorts_r
    |> (fun l -> List.drop l (List.length Arg.parameter_sorts + List.length sorts_l))

  let lr_tag_of tag : (Ident.tvar * Ident.tvar) =
    Option.value_exn tag
  let params_of ~tag = params_of_idx @@ lr_tag_of tag
  let depth_of ((_, _, _, depth, _, _, _, _, _): parameter) = depth

  let init_qualmap () =
    Hashtbl.Poly.map Arg.tag_infos ~f:(fun _ -> (Set.Poly.empty: Formula.t Set.Poly.t))

  let rcs, dcs, qds, qualmapl, qualmapr =
    Hashtbl.Poly.create (), Hashtbl.Poly.create (), Hashtbl.Poly.create (),
    init_qualmap (), init_qualmap ()
  let quals_with quals params =
    Set.Poly.filter quals ~f:(fun q ->
        let tvs = Formula.tvs_of q in
        let vs = List.map params ~f:fst |> Set.Poly.of_list in
        Set.Poly.for_all tvs ~f:(Set.Poly.mem vs))
  let adjust_quals ~tag quals =
    let idxl, idxr = lr_tag_of tag in
    let quals = Qualifier.AllTheory.add_quals_form_affine_eq_quals quals in
    if Stdlib.(idxl <> idxr) then quals
    else
      let fenv = Arg.fenv in
      let params_x, params_y =
        params_of_idx_l idxl, params_of_idx_r idxl idxr
      in
      let rename_x_y = Formula.rename (tvar_map_of_sort_env_list params_x params_y) in
      let rename_y_x = Formula.rename (tvar_map_of_sort_env_list params_y params_x) in
      let quals =
        Set.Poly.fold quals ~init:Set.Poly.empty ~f:(fun quals phi ->
            let qual1 = Z3Smt.Z3interface.qelim ~id fenv @@ Formula.exists params_y phi in
            let qual2 = rename_y_x @@ Z3Smt.Z3interface.qelim ~id fenv @@ Formula.exists params_x phi in
            let quals = (*ToDo*)if Formula.is_bind qual1 || Set.Poly.is_empty (Formula.fvs_of qual1) then quals else Set.Poly.add quals qual1 in
            let quals = (*ToDo*)if Formula.is_bind qual2 || Set.Poly.is_empty (Formula.fvs_of qual2) then quals else Set.Poly.add quals qual2 in
            quals) in
      Set.Poly.union quals (Set.Poly.map quals ~f:rename_x_y)
  let x_i i = Ident.Tvar (sprintf "x%d" (i + 1))
  let find_qualsr tag =
    let tag_l, tag_r = lr_tag_of tag in
    let qualsr =
      Hashtbl.Poly.find_exn qualmapr tag_r
    in
    let sorts_l = Hashtbl.Poly.find_exn Arg.tag_infos tag_l in
    let sorts_r = Hashtbl.Poly.find_exn Arg.tag_infos tag_r in
    let subst =
      List.mapi (Arg.parameter_sorts @ sorts_r) ~f:(fun i _ -> 
          if i < List.length Arg.parameter_sorts then
            x_i i, x_i i
          else
            x_i i, x_i (i + List.length sorts_l))
      |> Map.Poly.of_alist_exn
    in
    Set.Poly.map qualsr ~f:(Formula.rename subst)

  let rec init_quals tag quals =
    let idxl, idxr = lr_tag_of tag in
    let params = parameter_params_of () in
    let params_x, params_y =
      params_of_idx_l idxl, params_of_idx_r idxl idxr
    in
    let quals = adjust_quals ~tag quals in
    let qualsl, qualsr =
      quals_with quals (params @ params_x),
      quals_with quals (params @ params_y)
    in
    let subst_y =
      (params @ params_y)
      |> List.mapi ~f:(fun i (x, _) -> x, Ident.Tvar (sprintf "x%d" (i+1)))
      |> Map.Poly.of_alist_exn
    in
    let qualsr = Set.Poly.map ~f:(Formula.rename subst_y) qualsr in
    if Stdlib.(idxl <> idxr) then begin
      init_quals (Some (idxl, idxl)) qualsl;
      init_quals (Some (idxr, idxr)) qualsr;
    end;
    Hashtbl.Poly.update qualmapl idxl
      ~f:(function Some quals -> Set.Poly.union quals qualsl | _ -> qualsl);
    Hashtbl.Poly.update qualmapr idxr
      ~f:(function Some quals -> Set.Poly.union quals qualsr | _ -> qualsr)

  let gen_quals_terms ~tag (old_depth, _old_quals, old_qdeps, old_terms) =
    let params = params_of ~tag in
    let depth = depth_of !param in
    let idxl, _ = lr_tag_of tag in
    let qualsl, qualsr =
      Hashtbl.Poly.find_exn qualmapl idxl,
      find_qualsr tag
    in
    let quals, qdeps, terms =
      Qualifier.AllTheory.qualifiers_of
        ~fenv:Arg.fenv depth old_depth params Set.Poly.empty old_qdeps old_terms
    in
    depth, Set.Poly.union_list [quals; qualsl; qualsr], qdeps, terms

  let reset_paramvars () = Hashtbl.Poly.clear rcs; Hashtbl.Poly.clear dcs; Hashtbl.Poly.clear qds
  let gen_template ~tag quals _ctls terms =
    let idxl, idxr = lr_tag_of tag in
    let real_name = Ident.mk_nwf_tvar Arg.public_name idxl idxr in
    Debug.print @@ lazy
      (sprintf "[%s] quals:\n" (Ident.name_of_tvar real_name) ^
       String.concat_map_list ~sep:"\n" quals ~f:Formula.str_of);
    Debug.print @@ lazy
      (sprintf "[%s] terms:\n" (Ident.name_of_tvar real_name) ^
       String.concat_map_list ~sep:"\n" terms ~f:Term.str_of);
    let temp_params, hole_qualifiers_map, tmpl,
        cnstr_of_rfun_coeffs, cnstr_of_rfun_const, cnstr_of_disc_coeffs, cnstr_of_disc_const =
      let (np, ndc, nl, _depth, ubrc, ubrd, ubdc, ubdd, ds) = !param in
      Generator.gen_simplified_nwf_predicate
        (*config.use_ifte*)
        (List.dedup_and_sort ~compare:Stdlib.compare quals)
        (List.dedup_and_sort ~compare:Stdlib.compare terms)
        (rcs, dcs, qds)
        (List.init np ~f:(fun _ -> ndc), nl, ubrc, ubrd, ubdc, ubdd, ds)
        (config.norm_type,
         Option.map config.lower_bound_rfun_coeff ~f:Z.of_int,
         Option.map config.lower_bound_disc_coeff ~f:Z.of_int,
         Option.map config.bound_each_rfun_coeff ~f:Z.of_int,
         Option.map config.bound_each_disc_coeff ~f:Z.of_int)
        (parameter_params_of (),
         idxl, params_of_idx_l idxl,
         idxr, params_of_idx_r idxl idxr) in
    Debug.print @@ lazy (sprintf "[%s] predicate template:\n  " (Ident.name_of_tvar real_name) ^ Formula.str_of tmpl);
    Debug.print @@ lazy (sprintf "[%s] cnstr_of_rfun_coeffs:\n  " (Ident.name_of_tvar real_name) ^ Formula.str_of cnstr_of_rfun_coeffs);
    Debug.print @@ lazy (sprintf "[%s] cnstr_of_rfun_const:\n  " (Ident.name_of_tvar real_name) ^ Formula.str_of cnstr_of_rfun_const);
    Debug.print @@ lazy (sprintf "[%s] cnstr_of_disc_coeffs:\n  " (Ident.name_of_tvar real_name) ^ Formula.str_of cnstr_of_disc_coeffs);
    Debug.print @@ lazy (sprintf "[%s] cnstr_of_disc_const:\n  " (Ident.name_of_tvar real_name) ^ Formula.str_of cnstr_of_disc_const);
    let tmpl =
      Logic.Term.mk_lambda
        (Logic.of_old_sort_env_list Logic.ExtTerm.of_old_sort @@ params_of ~tag) @@
      Logic.ExtTerm.of_old_formula tmpl in
    (LexicoPieceConj, tmpl),
    ([(RFunCoeff, cnstr_of_rfun_coeffs |> Logic.ExtTerm.of_old_formula);
      (RFunConst, cnstr_of_rfun_const |> Logic.ExtTerm.of_old_formula);
      (DiscCoeff, cnstr_of_disc_coeffs |> Logic.ExtTerm.of_old_formula);
      (DiscConst, cnstr_of_disc_const |> Logic.ExtTerm.of_old_formula);]),
    temp_params, hole_qualifiers_map

  let restart (_np, _ndc, _nl, _depth, _ubrc, _ubrd, _ubdc, _ubdd, _ds) =
    Debug.print @@ lazy ("************* restarting " ^ Ident.name_of_tvar Arg.public_name ^ "***************");
    1, 0, 1, 0, Some Z.one, Some Z.zero, Some Z.one, Some Z.zero, Set.Poly.singleton (Z.of_int 0)

  let last_non_timeout_param = ref !param
  let revert (_np, _ndc, _nl, _depth, _ubrc, _ubrd, _ubdc, _ubdd, _ds) =
    Debug.print @@ lazy ("************* reverting " ^ Ident.name_of_tvar Arg.public_name ^ "***************");
    !last_non_timeout_param

  let increase_rfun_pieces (np, ndc, nl, depth, ubrc, ubrd, ubdc, ubdd, ds) =
    Debug.print @@ lazy ("************* increasing number_of_rfun_pieces of " ^ Ident.name_of_tvar Arg.public_name ^ "***************");
    np+1, ndc, nl, depth, ubrc, ubrd, ubdc, ubdd, ds

  let increase_disc_conj (np, ndc, nl, depth, ubrc, ubrd, ubdc, ubdd, ds) =
    Debug.print @@ lazy ("************* increasing number_of_disc_conj of " ^ Ident.name_of_tvar Arg.public_name ^ "***************");
    np, ndc+1, nl, depth, ubrc, ubrd, ubdc, ubdd, ds

  let increase_rfun_lexicos (np, ndc, nl, depth, ubrc, ubrd, ubdc, ubdd, ds) =
    Debug.print @@ lazy ("************* increasing number_of_rfun_lexicos of " ^ Ident.name_of_tvar Arg.public_name ^ "***************");
    np, ndc, nl+1, depth, ubrc, ubrd, ubdc, ubdd, ds

  let increase_lexico_piece_conj (np, ndc, nl, depth, ubrc, ubrd, ubdc, ubdd, ds) =
    if nl >= np then begin
      Debug.print @@ lazy ("************* restarting number_of_rfun_lexicos of " ^ Ident.name_of_tvar Arg.public_name ^ "***************");
      Debug.print @@ lazy ("************* increasing number_of_rfun_pieces of " ^ Ident.name_of_tvar Arg.public_name ^ "***************");
      Debug.print @@ lazy ("************* increasing number_of_disc_conj of " ^ Ident.name_of_tvar Arg.public_name ^ "***************");
      Debug.print @@ lazy ("************* increasing depth of " ^ Ident.name_of_tvar Arg.public_name ^ "***************");
      np+1, ndc+1, 1, depth + 1, ubrc, ubrd, ubdc, ubdd, ds
    end else begin
      increase_rfun_lexicos (np, ndc, nl, depth, ubrc, ubrd, ubdc, ubdd, ds)
    end

  let increase_rfun_coeff threshold (np, ndc, nl, depth, ubrc, ubrd, ubdc, ubdd, ds) =
    Debug.print @@ lazy ("************* increasing upper_bound_rfun_coeff of " ^ Ident.name_of_tvar Arg.public_name ^ "***************");
    let ubrc' =
      match ubrc, threshold with
      | Some ubrc, Some thr when Z.Compare.(ubrc >= Z.of_int thr) -> None
      | _, _ -> Option.map ubrc ~f:(fun ubrc -> Z.(+) ubrc (Z.of_int 1))
    in
    np, ndc, nl, depth, ubrc', ubrd, ubdc, ubdd, ds

  let increase_rfun_const threshold (np, ndc, nl, depth, ubrc, ubrd, ubdc, ubdd, ds) =
    Debug.print @@ lazy ("************* increasing upper_bound_rfun_const of " ^ Ident.name_of_tvar Arg.public_name ^ "***************");
    let ubrd' =
      match ubrd, threshold with
      | Some ubrd, Some thr when Z.Compare.(ubrd >= Z.of_int thr) -> None
      | _, _ -> Option.map ubrd ~f:(fun ubrd -> Z.(+) ubrd (Z.of_int 1))
    in
    np, ndc, nl, depth, ubrc, ubrd', ubdc, ubdd, ds

  let increase_disc_coeff threshold (np, ndc, nl, depth, ubrc, ubrd, ubdc, ubdd, ds) =
    Debug.print @@ lazy ("************* increasing upper_bound_disc_coeff of " ^ Ident.name_of_tvar Arg.public_name ^ "***************");
    let ubdc' =
      match ubdc, threshold with
      | Some ubdc, Some thr when Z.Compare.(ubdc >= Z.of_int thr) -> None
      | _, _ -> Option.map ubdc ~f:(fun ubdc -> Z.(+) ubdc (Z.of_int 1))
    in
    np, ndc, nl, depth, ubrc, ubrd, ubdc', ubdd, ds

  let increase_disc_const threshold (np, ndc, nl, depth, ubrc, ubrd, ubdc, ubdd, ds) =
    Debug.print @@ lazy ("************* increasing upper_bound_disc_const of " ^ Ident.name_of_tvar Arg.public_name ^ "***************");
    let ubdd' =
      match ubdd, threshold with
      | Some ubdd, Some thr when Z.Compare.(ubdd >= Z.of_int thr) -> None
      | _, _ -> Option.map ubdd ~f:(fun ubdd -> Z.(+) ubdd (Z.of_int 1))
    in
    np, ndc, nl, depth, ubrc, ubrd, ubdc, ubdd', ds

  let set_inf_rfun_coeff (np, ndc, nl, depth, _ubrc, ubrd, ubdc, ubdd, ds) =
    Debug.print @@ lazy ("************* setting upper_bound_rfun_coeff of " ^ Ident.name_of_tvar Arg.public_name ^ " to infinity ***************");
    let ubrc' = None in
    np, ndc, nl, depth, ubrc', ubrd, ubdc, ubdd, ds

  let set_inf_rfun_const (np, ndc, nl, depth, ubrc, _ubrd, ubdc, ubdd, ds) =
    Debug.print @@ lazy ("************* setting upper_bound_rfun_const of " ^ Ident.name_of_tvar Arg.public_name ^ " to infinity ***************");
    let ubrd' = None in
    np, ndc, nl, depth, ubrc, ubrd', ubdc, ubdd, ds

  let set_inf_disc_coeff (np, ndc, nl, depth, ubrc, ubrd, _ubdc, ubdd, ds) =
    Debug.print @@ lazy ("************* setting upper_bound_disc_coeff of " ^ Ident.name_of_tvar Arg.public_name ^ " to infinity ***************");
    let ubdc' = None in
    np, ndc, nl, depth, ubrc, ubrd, ubdc', ubdd, ds

  let set_inf_disc_const (np, ndc, nl, depth, ubrc, ubrd, ubdc, _ubdd, ds) =
    Debug.print @@ lazy ("************* setting upper_bound_disc_const of " ^ Ident.name_of_tvar Arg.public_name ^ " to infinity ***************");
    let ubdd' = None in
    np, ndc, nl, depth, ubrc, ubrd, ubdc, ubdd', ds

  let next () = 
    reset_paramvars ();
    param :=
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
      | QDep :: labels -> inner param labels
      | _ -> assert false
    in
    reset_paramvars ();
    param := inner !param @@ Set.Poly.to_list labels
  let show_state show_num_args labels =
    if show_num_args then
      Out_channel.print_endline
        (Format.sprintf "#args: %d|%s"
           (List.length Arg.parameter_sorts)
         @@ String.concat_map_list ~sep:"," ~f:(fun (tag, sorts) ->
             sprintf "%s:(%d)" (Ident.name_of_tvar tag) (List.length sorts))
         @@ Hashtbl.Poly.to_alist Arg.tag_infos);
    Out_channel.print_endline ("state of " ^ Ident.name_of_tvar Arg.public_name ^ ": " ^ Yojson.Safe.to_string @@ state_to_yojson @@ state_of !param labels);
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
      | "increase_disc_conj" -> action (increase_disc_conj param)
      | "increase_disc_coeff" -> action (increase_disc_coeff None param)
      | "increase_disc_const" -> action (increase_disc_const None param)
      | "set_inf_disc_coeff" -> action (set_inf_disc_coeff param)
      | "set_inf_disc_const" -> action (set_inf_disc_const param)
      | "restart" -> action (restart param)
      | "revert" -> action (revert param)
      | "end" -> param
      | s -> failwith ("Unknown action: " ^ s)
    in
    param := action !param
  let restart () = param := restart !param

  let sync thre =
    let np, ndc, nl, depth, ubrc, ubrd, ubdc, ubdd, ds = !param in
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
    param := param'

  let str_of () =
    let np, ndc, nl, depth, ubrc, ubrd, ubdc, ubdd, ds = !param in
    Printf.sprintf
      ("number of piecewise : %d\n" ^^
       "number of discriminator conjuncts : %d\n" ^^
       "number of lexicographic : %d\n" ^^
       "depth : %d\n" ^^
       "upper bound of the sum of the abs of ranking function coefficients : %s\n" ^^
       "upper bound of the abs of ranking function constant : %s\n" ^^
       "upper bound of the sum of the abs of discriminator coefficients : %s\n" ^^
       "upper bound of the abs of discriminator constant : %s\n" ^^
       "seeds : %s")
      np ndc nl depth
      (match ubrc with None -> "N/A" | Some ubrc -> Z.to_string ubrc)
      (match ubrd with None -> "N/A" | Some ubrd -> Z.to_string ubrd)
      (match ubdc with None -> "N/A" | Some ubdc -> Z.to_string ubdc)
      (match ubdd with None -> "N/A" | Some ubdd -> Z.to_string ubdd)
      (String.concat_set ~sep:"," @@ Set.Poly.map ds ~f:Z.to_string)

  let _ =
    Debug.print @@ lazy ("************* initializing " ^ Ident.name_of_tvar Arg.public_name ^ " ***************");
    Debug.print @@ lazy (str_of ())

  let in_space () = true (* TODO *)
end

let modules = Hashtbl.Poly.create ()

let make ~(id:int option) ~(public_name:Ident.tvar) config arg =
  match Hashtbl.Poly.find modules (id, public_name) with
  | Some m -> m
  | None ->
    let (module Config : WFPredicate.Config.ConfigType) = config in
    let (module Arg : ArgType) = arg in
    (module Make(Config)(Arg) : Function.Type)
    |>(fun m -> Hashtbl.Poly.add_exn modules ~key:(id, public_name) ~data:m; m)
