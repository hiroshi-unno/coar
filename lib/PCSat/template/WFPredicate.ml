(* Template for a well-founded predicate [WF(x, y)] over a relation whose
   arguments split in half into a source [x] and a destination [y].

   The template states that a piecewise lexicographic ranking function
   decreases from [x] to [y] and stays bounded below: [number_of_rfun_pieces]
   pieces selected by discriminators of [number_of_disc_conj] conjuncts each,
   [number_of_rfun_lexicos] lexicographic components, affine terms over the
   hypothesis space's terms with coefficient and constant bounds.  Every
   instance is well-founded by construction, which is what makes a candidate
   of this kind sound without a separate well-foundedness check; the ranking
   function chosen is kept as a certificate ([kind_cert_template]).
   [gen_template] returns the template with its bound constraints, each
   labelled so that an unsat core says which bound to raise; a shape label
   grows pieces, components and depth ([increase_lexico_piece_conj], in the
   order [Config.shape_growth] chooses), and [restart] returns to one piece
   and the smallest bounds. *)
open Core
open Common
open Common.Ext
open Common.Util
open Common.Combinator
open Ast
open Ast.LogicOld
open Function

module Config = struct
  (* the coefficient bounds of the synthesized templates, by role *)
  type coeff_bound = {
    initial : int option; [@default Some 1]
        (** the starting bound on the sum of the absolute values of the coefficients
            ([None]: unbounded); a failure can raise it *)
    lower : int option; [@default None]
        (** a lower bound on the sum of the absolute values of the coefficients *)
    per_coefficient : int option; [@default None]
        (** a bound on the absolute value of each coefficient *)
    unbounded_above : int option; [@default Some 3]
        (** once the coefficient bound has reached this value, raising it drops it
            altogether ([None]: it is raised by one each time) *)
  }
  [@@deriving yojson]

  type rfun_const_bound = {
    initial : int option; [@default Some 0]
        (** the starting bound on the sum of the absolute values of the constants
            ([None]: unbounded); a failure can raise it *)
    unbounded_above : int option; [@default Some 3]
        (** once the constant bound has reached this value, raising it drops it
            altogether ([None]: it is raised by one each time) *)
  }
  [@@deriving yojson]

  type disc_const_bound = {
    initial : int option; [@default Some 0]
        (** the starting bound on the sum of the absolute values of the constants
            ([None]: unbounded); a failure can raise it *)
    unbounded_above : int option; [@default Some 3]
        (** once the constant bound has reached this value, raising it drops it
            altogether ([None]: it is raised by one each time) *)
    seeds : int list option; [@default None]
        (** the seed constants of the template ([None]: zero alone) *)
  }
  [@@deriving yojson]

  type rfun_bounds = {
    coeff : coeff_bound; [@default Common.Util.config_default coeff_bound_of_yojson "{}"]
    const : rfun_const_bound; [@default Common.Util.config_default rfun_const_bound_of_yojson "{}"]
  }
  [@@deriving yojson]

  type disc_bounds = {
    coeff : coeff_bound; [@default Common.Util.config_default coeff_bound_of_yojson "{}"]
    const : disc_const_bound; [@default Common.Util.config_default disc_const_bound_of_yojson "{}"]
  }
  [@@deriving yojson]

  type bounds = {
    rfun : rfun_bounds; [@default Common.Util.config_default rfun_bounds_of_yojson "{}"]
        (** the bounds on the ranking functions' coefficients and constants *)
    disc : disc_bounds; [@default Common.Util.config_default disc_bounds_of_yojson "{}"]
        (** the bounds on the discriminators' coefficients and constants *)
  }
  [@@deriving yojson]

  (** How a shape failure grows the template.  Every shape can express what
      a shape smaller in both [nl] and [np] can (a further component can be
      constant, a further piece can repeat another), so each policy below
      only decides in which order shapes are tried, and each eventually
      tries a shape at least as large as any given one; none changes what a
      candidate is checked against. *)
  type shape_growth =
    | Diagonal
        (** one more component on every failure, and a piece and a
            discriminator conjunct with it once [nl >= 2 * np] (the first
            failure takes both to two), a level of depth once
            [nl >= 3 * (depth + 1)].  After the first failure [nl >= np]
            holds for good, so a ranking that needs many pieces and one
            component (a rank constant on each of four regions) is only
            reachable inside a shape whose synthesis query grows with
            [nl * np] and is then too large to solve *)
    | Cost_ordered_lexicos_first
        (** each failure moves to the next shape in increasing order of
            [nl * np] (the factor the synthesis query grows with), over the
            shapes at least as large as the configured one, the shape with
            more components first among those of equal product: from one
            component and one piece, [(2,1)], [(1,2)], [(3,1)], [(1,3)],
            [(4,1)], [(2,2)], [(1,4)], ...  The discriminator conjuncts
            follow the pieces (one per piece beyond the configured count) and
            the depth follows the components as in [Diagonal]; the depth
            never decreases *)
    | Cost_ordered_pieces_first
        (** as [Cost_ordered_lexicos_first] with the shape with more pieces
            first among those of equal product: [(1,2)], [(2,1)], [(1,3)],
            [(3,1)], [(1,4)], [(2,2)], [(4,1)], ... *)
    | Orthant_pieces
        (** the first growth from one component and one piece goes to one
            component and [2^k] pieces with no discriminator conjunct, [k]
            the number of real-sorted state coordinates of the template (at
            most three, so at most eight pieces), and every other growth is
            [Diagonal]'s.  Over the reals the decrease a template states is
            the bounded [r(x) >= r(y) + 1], and under a linear update that
            commutes with scaling (a rotation, a reflection) every affine
            rank changes by an amount that shrinks to zero near the origin,
            so a rank must be piecewise with pieces bounded by hyperplanes
            through the origin; the coordinate orthants are the coarsest such
            partition that the qualifiers [v >= 0] and [v <= 0] (reflected
            halfspaces) name without an affine discriminator conjunct.  In
            the well-founded template, a core blaming the orthant shape
            raises the ranking function's coefficient and constant bounds
            instead until both are unbounded ([held_labels]).  A template
            with no real-sorted coordinate grows as [Diagonal] *)
  [@@deriving yojson]

  type t = {
    verbose : bool; [@default false]
    number_of_rfun_pieces : int; [@default 1]
    number_of_disc_conj : int; [@default 0]
    number_of_rfun_lexicos : int; [@default 1]
    term_depth : int; [@default 0]
    bounds : bounds; [@default Common.Util.config_default bounds_of_yojson "{}"]
        (** the coefficient bounds of the synthesized templates *)
    ranking_extra_terms : Ast.Templ.ranking_extra_terms;
        [@default
          Common.Util.config_default Ast.Templ.ranking_extra_terms_of_yojson
            "{}"]
        (** the terms the simplified ranking-function templates are offered
            beyond the parameters (absolute differences, the wrap-around
            distance, constants); the default is the measured selection *)
    norm_type : Ast.Templ.norm_type; [@default Ast.Templ.L1]
        (** the norm the ranking functions' coefficient bounds constrain *)
    use_ifte : bool; [@default false]
    branch_on_bool_args : bool; [@default false]
        (** read by nothing here: the ranking-function template builds no
            boolean branch (the field keeps the term templates' spelling) *)
    fix_shape : bool; [@default false]
    shape_growth : shape_growth; [@default Diagonal]
        (** the order in which a shape failure (an unsat core naming the
            template's shape) grows the number of lexicographic components
            [nl] and of pieces [np]; read by the well-founded, the
            nested-well-founded and the parity-predicate templates alike *)
  }
  [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end

  let instantiate_ext_files cfg = Ok cfg

  include MakeExtFile (struct
    type nonrec t = t

    let of_yojson = of_yojson
    let to_yojson = to_yojson
    let name = "WFPredicate"
    let instantiate = instantiate_ext_files
  end)
end

(* The shape-growth policies of [Config.shape_growth] other than [Diagonal],
   as functions of the shape alone, shared by the well-founded,
   nested-well-founded and parity-predicate templates (each moves its own
   parameter record with its own named actions, which the
   reinforcement-learning interface reads). *)
module ShapeGrowth = struct
  (* [next_by_cost ~lexicos_first ~nl0 ~np0 (nl, np)] is the least shape
     [(l, p)] with [l >= nl0], [p >= np0] whose key [(l * p, tie)] is
     greater than the key of [(nl, np)], where [tie] is [-l] when
     [lexicos_first] (more components first among equal products) and [l]
     otherwise.  Requires [nl >= 1], [np >= 1], [nl0 >= 1], [np0 >= 1].
     Guarantees: the result's key is greater than the argument's, so
     iterating from any shape enumerates, in key order, every shape of the
     quadrant whose key is greater; and no shape of the quadrant has a key
     strictly between the two.  [(nl + 1, np)] has a greater key (its
     product is larger), so the least lies at product at most
     [(nl + 1) * np] and the search below is finite. *)
  let next_by_cost ~lexicos_first ~nl0 ~np0 (nl, np) =
    let key (l, p) = (l * p, if lexicos_first then -l else l) in
    let lt (a1, b1) (a2, b2) = a1 < a2 || (a1 = a2 && b1 < b2) in
    let cur = key (nl, np) in
    let cap = (nl + 1) * np in
    let best = ref (nl + 1, np) in
    for l = max 1 nl0 to cap do
      for p = max 1 np0 to cap / l do
        let k = key (l, p) in
        if lt cur k && lt k (key !best) then best := (l, p)
      done
    done;
    !best

  (* the depth the cost-ordered policies give [nl] components: as
     [Diagonal], which adds a level each time [nl] passes [3 * (depth + 1)],
     and never below the current depth *)
  let depth_for ~depth0 ~cur_depth nl = max cur_depth (depth0 + ((nl - 1) / 3))

  (* the discriminator conjuncts the cost-ordered policies give [np] pieces:
     one per piece beyond the configured count, as [Diagonal] adds one with
     each piece *)
  let disc_conj_for ~ndc0 ~np0 np = max 0 (ndc0 + np - np0)

  (* [orthant_pieces sorts] is [Some (2^k)] for the [k >= 1] real-sorted
     sorts among [sorts] (a template's state coordinates), [k] capped at 3,
     and [None] when there is none *)
  let orthant_pieces sorts =
    let k =
      List.count sorts ~f:(function T_real.SReal -> true | _ -> false)
    in
    if k = 0 then None else Some (1 lsl Int.min k 3)

  (* [move ~inc ~dec cur target pa] applies [inc] [target - cur] times or
     [dec] [cur - target] times, so that a template moves to a shape through
     its named single-step actions *)
  let move ~inc ~dec cur target pa =
    if target >= cur then Fn.apply_n_times ~n:(target - cur) inc pa
    else Fn.apply_n_times ~n:(cur - target) dec pa
end

module type ArgType = sig
  val name : Ident.tvar
  val sorts : Sort.t list
  val fenv : LogicOld.FunEnv.t
  val sol_space : SolSpace.t
  val id : int option
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
    (* [Z.to_int] is safe: the bounds are the template's configured
       coefficient and constant bounds, grown by one step at a time, never a
       model integer *)
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
        np = config.number_of_rfun_pieces;
        ndc = config.number_of_disc_conj;
        nl = config.number_of_rfun_lexicos;
        depth = config.term_depth;
        ubrc = Option.map config.bounds.rfun.coeff.initial ~f:Z.of_int;
        ubrd = Option.map config.bounds.rfun.const.initial ~f:Z.of_int;
        ubdc = Option.map config.bounds.disc.coeff.initial ~f:Z.of_int;
        ubdd = Option.map config.bounds.disc.const.initial ~f:Z.of_int;
        ds =
          (match config.bounds.disc.const.seeds with
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
  let kind = Kind.WF
  let flexible = false
  let sort_of () = Sort.mk_fun @@ Arg.sorts @ [ T_bool.SBool ]
  let params_of () = sort_env_list_of_sorts Arg.sorts

  let show_state ?(config = PCSatCommon.RLConfig.disabled) labels =
    ignore config;
    Debug.print_stdout
    @@ lazy
         (sprintf "state of %s: %s" (Ident.name_of_tvar (name_of ()))
         @@ Yojson.Safe.to_string @@ state_to_yojson @@ state_of !param labels);
    Out_channel.flush Out_channel.stdout

  let str_of () =
    sprintf
      ("number of piecewise (max: %s) : %d\n"
     ^^ "number of discriminator conjuncts (max: %s) : %d\n"
     ^^ "number of lexicographic (max: %s) : %d\n" ^^ "depth (max: %s) : %d\n"
     ^^ "upper bound of the sum of the abs of ranking function coefficients : %s\n"
     ^^ "upper bound of the abs of ranking function constant : %s\n"
     ^^ "upper bound of the sum of the abs of discriminator coefficients : %s\n"
     ^^ "upper bound of the abs of discriminator constant : %s\n"
     ^^ "seeds : %s")
      (SolSpace.str_of_tvar_and_flag Arg.name SolSpace.NP Arg.sol_space)
      !param.np
      (SolSpace.str_of_tvar_and_flag Arg.name SolSpace.NDC Arg.sol_space)
      !param.ndc
      (SolSpace.str_of_tvar_and_flag Arg.name SolSpace.NL Arg.sol_space)
      !param.nl
      (SolSpace.str_of_tvar_and_flag Arg.name SolSpace.Depth Arg.sol_space)
      !param.depth
      (match !param.ubrc with None -> "N/A" | Some ubrc -> Z.to_string ubrc)
      (match !param.ubrd with None -> "N/A" | Some ubrd -> Z.to_string ubrd)
      (match !param.ubdc with None -> "N/A" | Some ubdc -> Z.to_string ubdc)
      (match !param.ubdd with None -> "N/A" | Some ubdd -> Z.to_string ubdd)
      (String.concat_map_set ~sep:"," !param.ds ~f:Z.to_string)

  let in_space () =
    SolSpace.in_space Arg.name SolSpace.NP !param.np Arg.sol_space
    && SolSpace.in_space Arg.name SolSpace.NDC !param.ndc Arg.sol_space
    && SolSpace.in_space Arg.name SolSpace.NL !param.nl Arg.sol_space
    && SolSpace.in_space Arg.name SolSpace.Depth !param.depth Arg.sol_space

  let adjust_quals_terms (quals, terms) =
    let params_x, params_y =
      let params = params_of () in
      List.split_n params (List.length params / 2)
    in
    Qual.extract_wf_terms_from_quals_terms
      ~qelim:(Z3Smt.Z3interface.qelim ~timeout:(Some 1000) ~id ~fenv:Arg.fenv)
      params_x params_y (quals, terms)

  let update_hspace hspace =
    HypSpace.qualifiers_of ~fenv:Arg.fenv !param.depth hspace

  let last_cert : Templ.kind_cert_templ option ref = ref None
  let kind_cert_template () = Option.map !last_cert ~f:List.return

  let gen_template ~ucore:_ (hspace : HypSpace.hspace) =
    assert (List.length hspace.params mod 2 = 0);
    if true then (
      Debug.print @@ lazy "qualifiers and terms for template generation:";
      Debug.print
      @@ lazy
           (sprintf "quals: %s"
           @@ String.concat_map_set ~sep:"," hspace.quals ~f:Formula.str_of);
      Debug.print
      @@ lazy
           (sprintf "terms: %s"
           @@ String.concat_map_set ~sep:"," hspace.terms ~f:Term.str_of));
    let template =
      Templ.gen_simplified_wf_predicate ~print:Debug.print
        (*config.use_ifte*)
        {
          consts = Set.to_list hspace.consts;
          terms = Set.to_list hspace.terms;
          quals = Set.to_list hspace.quals;
          shp = List.init !param.np ~f:(fun _ -> !param.ndc);
          nl = !param.nl;
          ubrc = !param.ubrc;
          ubrd = !param.ubrd;
          ubdc = !param.ubdc;
          ubdd = !param.ubdd;
          ds = !param.ds;
        }
        {
          extra_terms = config.ranking_extra_terms;
          norm_type = config.norm_type;
          lbrc = Option.map config.bounds.rfun.coeff.lower ~f:Z.of_int;
          lbdc = Option.map config.bounds.disc.coeff.lower ~f:Z.of_int;
          berc = Option.map config.bounds.rfun.coeff.per_coefficient ~f:Z.of_int;
          bedc = Option.map config.bounds.disc.coeff.per_coefficient ~f:Z.of_int;
        }
        hspace.params
    in
    last_cert := Some template.Templ.cert;
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

  (*let try_then f g =
    let res = f () in
    let backup = !param in
    param := fst res;
    if in_space () then (
      param := backup;
      res)
    else g ()*)

  let diagonal_step (param, actions) =
    if param.nl <= 1 && param.np <= 1 then
      increase_disc_conj @@ increase_rfun_pieces
      @@ increase_rfun_lexicos (param, actions)
    else
      (if param.nl >= 3 * (param.depth + 1) then increase_depth else Fn.id)
      @@ (if param.nl >= 2 * param.np then
            increase_rfun_pieces >> increase_disc_conj
          else Fn.id)
      @@ increase_rfun_lexicos (param, actions)

  (* moves to the shape [(nl, np, ndc, depth)] by single-step actions *)
  let move_shape (nl, np, ndc, depth) ((param, _) as pa) =
    let open ShapeGrowth in
    pa
    |> move ~inc:increase_rfun_lexicos ~dec:decrease_rfun_lexicos param.nl nl
    |> move ~inc:increase_rfun_pieces ~dec:decrease_rfun_pieces param.np np
    |> move ~inc:increase_disc_conj ~dec:decrease_disc_conj param.ndc ndc
    |> move ~inc:increase_depth ~dec:decrease_depth param.depth depth

  let cost_step ~lexicos_first ((param, _) as pa) =
    let nl, np =
      ShapeGrowth.next_by_cost ~lexicos_first
        ~nl0:config.number_of_rfun_lexicos ~np0:config.number_of_rfun_pieces
        (param.nl, param.np)
    in
    move_shape
      ( nl,
        np,
        ShapeGrowth.disc_conj_for ~ndc0:config.number_of_disc_conj
          ~np0:config.number_of_rfun_pieces np,
        ShapeGrowth.depth_for ~depth0:config.term_depth ~cur_depth:param.depth
          nl )
      pa

  (* the source half of the arguments are the state coordinates *)
  let orthant_pieces =
    ShapeGrowth.orthant_pieces
    @@ fst
    @@ List.split_n Arg.sorts (List.length Arg.sorts / 2)

  let increase_lexico_piece_conj ((param, _) as pa) =
    match config.shape_growth with
    | Diagonal -> diagonal_step pa
    | Cost_ordered_lexicos_first -> cost_step ~lexicos_first:true pa
    | Cost_ordered_pieces_first -> cost_step ~lexicos_first:false pa
    | Orthant_pieces -> (
        match orthant_pieces with
        | Some n when param.nl <= 1 && param.np <= 1 && n > param.np ->
            Debug.print
            @@ lazy
                 (sprintf "************* orthant pieces for %s: %d pieces"
                    (Ident.name_of_tvar Arg.name)
                    n);
            move_shape (param.nl, n, param.ndc, param.depth) pa
        | _ -> diagonal_step pa)

  let rec inner param_actions = function
    | [] -> param_actions
    | (LexicoPieceConj | Shape) :: labels ->
        inner
          (if config.fix_shape then param_actions
           else increase_lexico_piece_conj param_actions)
          labels
    | RFunCoeff :: labels ->
        inner
          (increase_rfun_coeff config.bounds.rfun.coeff.unbounded_above param_actions)
          labels
    | RFunConst :: labels ->
        inner
          (increase_rfun_const config.bounds.rfun.const.unbounded_above param_actions)
          labels
    | DiscCoeff :: labels ->
        inner
          (increase_disc_coeff config.bounds.disc.coeff.unbounded_above param_actions)
          labels
    | DiscConst :: labels ->
        inner
          (increase_disc_const config.bounds.disc.const.unbounded_above param_actions)
          labels
    | TimeOut :: _labels -> param_actions (* z3 may unexpectedly time out*)
    | QualDep :: labels -> inner param_actions labels
    | _ ->
        (* another template module's label: excluded by the contract of
           [Function.Type.update_with_labels] *)
        assert false

  let coeff_labels = [ RFunCoeff; DiscCoeff ]
  let const_labels = [ RFunConst; DiscConst ]

  (* Under [Orthant_pieces], at the orthant shape (one component, [2^k]
     pieces), a core that names the shape grows the ranking function's
     coefficient and constant bounds instead, as long as either is finite.
     The orthant certificate (a rank constant on each orthant, 3/2/1/0 for
     a rotation by a quarter turn) needs constants up to the number of
     pieces minus one, and the shape is blamed before they are reached: a
     core names the shape together with the constant bound, or the shape
     alone when the examples that refute the candidate are disjunctions with
     another unknown whose own template is still too weak (an invariant that
     has not yet excluded the origin, where no rank decreases).  Growing the
     shape there left the orthant shape for a larger one with the bounds
     still too small, where the synthesis query is too large to solve.
     Terminates: each bound reaches its threshold and becomes unbounded
     after finitely many raises ([increase_rfun_coeff], [increase_rfun_const]),
     after which the shape grows as [Diagonal]'s.  Every other policy and
     shape reads the labels unchanged. *)
  let held_labels param labels =
    let is_shape = function LexicoPieceConj | Shape -> true | _ -> false in
    match (config.shape_growth, orthant_pieces) with
    | Orthant_pieces, Some n
      when param.nl <= 1 && param.np = n
           && (Option.is_some param.ubrc || Option.is_some param.ubrd)
           && List.exists labels ~f:is_shape ->
        let rest = List.filter labels ~f:(Fn.non is_shape) in
        let add_if finite l acc =
          if finite && not (List.mem acc l ~equal:Stdlib.( == )) then
            l :: acc
          else acc
        in
        rest
        |> add_if (Option.is_some param.ubrc) RFunCoeff
        |> add_if (Option.is_some param.ubrd) RFunConst
    | _ -> labels

  let actions_of labels =
    (snd @@ inner (!param, []) @@ held_labels !param @@ Set.to_list labels)
    @ [ "end" ]

  let update_with_labels labels =
    param := fst @@ inner (!param, []) @@ held_labels !param
      @@ Set.to_list labels

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
