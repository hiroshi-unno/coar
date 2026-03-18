open Core
open Common
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld
open Function

module type ArgType = sig
  val name : Ident.tvar
  val fenv : LogicOld.FunEnv.t
  val id : int option
  val nwf_tag : (Kind.nwf * (Ident.tvar * Ident.tvar)) option
end

open PCSatCommon.VersionSpace

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

  let nwf, (tag_l, tag_r) =
    match Arg.nwf_tag with
    | Some (nwf, tag) -> (nwf, tag)
    | None -> assert false

  let _ = List.is_empty nwf.sorts_shared

  let sorts_map : (Ident.tvar, Sort.t list) Hashtbl.Poly.t =
    Hashtbl.Poly.map nwf.sorts_map ~f:(List.map ~f:Logic.ExtTerm.to_old_sort)

  let (param, last_non_timeout_param), (templ, qual_term_map) =
    match Hashtbl.Poly.find shared_info (id, nwf.name) with
    | Some m -> m
    | _ ->
        let m =
          let param =
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
          in
          ( (ref param, ref param),
            Hashtbl.Poly.
              ( Parity (create (), create (), create ()),
                map sorts_map ~f:(fun _ -> (Set.Poly.empty, Set.Poly.empty)) )
          )
        in
        Hashtbl.Poly.add_exn shared_info ~key:(id, nwf.name) ~data:m;
        m

  let rcs, dcs, qds =
    match templ with
    | Parity (rcs, dcs, qds) -> (rcs, dcs, qds)
    | _ -> assert false

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
  let kind_of () = Kind.str_of (Kind.Parity (nwf, (tag_l, tag_r)))
  let sorts_of = Hashtbl.Poly.find_exn sorts_map
  let sorts_l = sorts_of tag_l
  let sorts_r = sorts_of tag_r
  let sort_of () = Sort.mk_fun @@ sorts_l @ sorts_r @ [ T_bool.SBool ]
  let params_left = LogicOld.sort_env_list_of_sorts ~pre:"" sorts_l

  let params_right =
    LogicOld.sort_env_list_of_sorts ~pre:"" ~start:(List.length sorts_l) sorts_r

  let params_of () = LogicOld.sort_env_list_of_sorts ~pre:"" (sorts_l @ sorts_r)

  let show_state ?(config = PCSatCommon.RLConfig.disabled) labels =
    if config.show_num_args then
      Debug.print_stdout
      @@ lazy
           (sprintf "args: %s"
           @@ String.concat_map_list ~sep:"," ~f:(fun (tag, sorts) ->
               sprintf "%s:(%d)" (Ident.name_of_tvar tag) (List.length sorts))
           @@ Hashtbl.Poly.to_alist sorts_map);
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
      (String.concat_map_set ~sep:"," !param.ds ~f:Z.to_string)

  let in_space () = true (* TODO *)

  let adjust_quals_terms (quals, terms) =
    ( Set.Poly.filter_map quals ~f:(fun phi ->
          if Formula.is_ground phi then None
          else
            let fvs = Formula.fvs_of phi in
            if
              Set.is_subset fvs
                ~of_:(Set.Poly.of_list @@ List.map ~f:fst params_left)
            then Some phi
            else if
              Set.is_subset fvs
                ~of_:(Set.Poly.of_list @@ List.map ~f:fst params_right)
            then Some phi
            else (* ToDo: use the information about transition predicates *)
              None),
      terms )

  let update_hspace hspace =
    HypSpace.qualifiers_of ~fenv:Arg.fenv !param.depth hspace

  let gen_template ~ucore:_ (hspace : HypSpace.hspace) =
    let template =
      let quals_x, terms_x = Hashtbl.find_exn qual_term_map tag_l in
      let quals_y, terms_y =
        let quals_y, terms_y = Hashtbl.find_exn qual_term_map tag_r in
        let ren =
          ren_of_sort_env_list
            (LogicOld.sort_env_list_of_sorts ~pre:"" sorts_r)
            (LogicOld.sort_env_list_of_sorts ~pre:""
               ~start:(List.length sorts_l) sorts_r)
        in
        ( Set.Poly.map quals_y ~f:(Formula.rename ren),
          Set.Poly.map terms_y ~f:(Term.rename ren) )
      in
      if true then (
        Debug.print @@ lazy "qualifiers and terms for template generation:";
        Debug.print
        @@ lazy
             (sprintf "quals: %s"
             @@ String.concat_map_set ~sep:"," hspace.quals ~f:Formula.str_of);
        Debug.print
        @@ lazy
             (sprintf "terms: %s"
             @@ String.concat_map_set ~sep:"," hspace.terms ~f:Term.str_of);
        Debug.print
        @@ lazy
             (sprintf "quals_x for %s: %s" (Ident.name_of_tvar tag_l)
             @@ String.concat_map_set ~sep:"," quals_x ~f:Formula.str_of);
        Debug.print
        @@ lazy
             (sprintf "terms_x for %s: %s" (Ident.name_of_tvar tag_l)
             @@ String.concat_map_set ~sep:"," terms_x ~f:Term.str_of);
        Debug.print
        @@ lazy
             (sprintf "quals_y for %s: %s" (Ident.name_of_tvar tag_r)
             @@ String.concat_map_set ~sep:"," quals_y ~f:Formula.str_of);
        Debug.print
        @@ lazy
             (sprintf "terms_y for %s: %s" (Ident.name_of_tvar tag_r)
             @@ String.concat_map_set ~sep:"," terms_y ~f:Term.str_of));
      Templ.gen_simplified_parity_predicate
        (*config.use_ifte*)
        (rcs, dcs, qds)
        (nwf.max_pri, nwf.sigma, nwf.trunc, nwf.acc_set)
        {
          consts = Set.to_list hspace.consts;
          terms = [] (*Set.to_list hspace.terms*);
          quals = [] (*Set.to_list hspace.quals*);
          shp = List.init !param.np ~f:(fun _ -> !param.ndc);
          nl = !param.nl;
          ubrc = !param.ubrc;
          ubrd = !param.ubrd;
          ubdc = !param.ubdc;
          ubdd = !param.ubdd;
          ds = !param.ds;
        }
        {
          norm_type = config.norm_type;
          lbrc = Option.map config.lower_bound_rfun_coeff ~f:Z.of_int;
          lbdc = Option.map config.lower_bound_disc_coeff ~f:Z.of_int;
          berc = Option.map config.bound_each_rfun_coeff ~f:Z.of_int;
          bedc = Option.map config.bound_each_disc_coeff ~f:Z.of_int;
        }
        (tag_l, params_left, tag_r, params_right)
        (Set.to_list quals_x, Set.to_list terms_x)
        (Set.to_list quals_y, Set.to_list terms_y)
    in
    Debug.print
    @@ lazy
         (sprintf "[%s] predicate template:\n  %s"
            (Ident.name_of_tvar Arg.name)
            (Formula.str_of template.pred));
    Debug.print
    @@ lazy
         (sprintf "[%s] rfun_selectors_bounds:\n  %s"
            (Ident.name_of_tvar Arg.name)
            (Formula.str_of template.rfun_selectors_bounds));
    Debug.print
    @@ lazy
         (sprintf "[%s] rfun_coeffs_bounds:\n  %s"
            (Ident.name_of_tvar Arg.name)
            (Formula.str_of template.rfun_coeffs_bounds));
    Debug.print
    @@ lazy
         (sprintf "[%s] rfun_const_bounds:\n  %s"
            (Ident.name_of_tvar Arg.name)
            (Formula.str_of template.rfun_const_bounds));
    Debug.print
    @@ lazy
         (sprintf "[%s] disc_coeffs_bounds:\n  %s"
            (Ident.name_of_tvar Arg.name)
            (Formula.str_of template.disc_coeffs_bounds));
    Debug.print
    @@ lazy
         (sprintf "[%s] disc_const_bounds:\n  %s"
            (Ident.name_of_tvar Arg.name)
            (Formula.str_of template.disc_const_bounds));
    let pred =
      Logic.(Term.mk_lambda (of_old_sort_env_list hspace.params))
      @@ Logic.ExtTerm.of_old_formula template.pred
    in
    ( (LexicoPieceConj, pred),
      [
        ( false,
          RFunCoeff,
          Logic.ExtTerm.of_old_formula template.rfun_coeffs_bounds );
        ( false,
          RFunConst,
          Logic.ExtTerm.of_old_formula template.rfun_const_bounds );
        ( false,
          DiscCoeff,
          Logic.ExtTerm.of_old_formula template.disc_coeffs_bounds );
        ( false,
          DiscConst,
          Logic.ExtTerm.of_old_formula template.disc_const_bounds );
        ( true,
          LexicoPieceConj,
          Logic.ExtTerm.of_old_formula template.rfun_selectors_bounds );
      ],
      template.templ_params,
      template.hole_quals_map )

  let restart (_param, actions) =
    Debug.print
    @@ lazy
         ("************* restarting "
         ^ Ident.name_of_tvar Arg.name
         ^ "***************");
    (init, actions @ [ "restart" ])

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
    if param.nl <= 1 && param.np <= 1 then
      increase_disc_conj @@ increase_rfun_pieces
      @@ increase_rfun_lexicos (param, actions)
    else
      (if param.nl >= 3 * (param.depth + 1) then increase_depth else Fn.id)
      @@ (if param.nl >= 2 * param.np then
            increase_rfun_pieces >> increase_disc_conj
          else Fn.id)
      @@ increase_rfun_lexicos (param, actions)

  let rec inner param_actions = function
    | [] -> param_actions
    | (LexicoPieceConj | Shape) :: labels ->
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
    | QualDep :: labels -> inner param_actions labels
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
