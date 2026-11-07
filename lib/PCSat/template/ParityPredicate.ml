(* Template for a parity-condition predicate ([Kind.Parity]): like the tagged
   well-founded family, its unknowns relate a state of tag [l] to a state of
   tag [r] and share one ranking function per tag, but the required decrease
   depends on the priorities the kind carries (maximum priority, the priority
   of each tag, the truncation and the accepting set): there is one ranking
   level per truncated priority, and at an accepting priority a non-strict
   decrease is admitted too.  Uses the well-founded template's
   configuration for its shape and bounds, and [Config] below for the growth
   rules only this template has. *)
open Core
open Common
open Common.Ext
open Common.Combinator
open Ast
open Ast.LogicOld
open Function

module Config = struct
  (** what the parity-predicate template's first shape growth after its
      lexicographic-only phase is (see [lexico_only_growth_until] below) *)
  type lexico_exhausted_growth =
    | Compound
        (** the default growth from the current shape: one more component,
            and with it a piece, a discriminator conjunct and a level of
            depth at once *)
    | Restart_lexicos
        (** back to one component, then the growth a family takes from one
            component and one piece: two components, two pieces and a
            discriminator conjunct.  The lexicographic-only phase is a guess
            that the ranking needs components before pieces; on a loop with
            no lexicographic linear ranking (a counter that wraps around to a
            constant, so every linear component increases on one of its two
            steps) the components it added are dead weight, and the compound
            step from three components asks for four components times two
            pieces at depth one, a query Z3 did not decide in 300 s where the
            two-by-two shape answers in seconds *)
    | Restart_all
        (** as [Restart_lexicos], and the coefficient and constant bounds go
            back to their initial values too: a failure in the
            lexicographic-only phase also raises the bounds its unsat core
            names, so after three failures the two-by-two shape is asked with
            bounds of three where the shape grown directly from one component
            is asked with bounds of one *)
    | Pieces_only
        (** keep the components, add a piece and a discriminator conjunct *)
    | Restart_all_if_no_lex_ranking
        (** [Restart_all] when the component provably has no lexicographic
            linear ranking function, [Compound] otherwise.  The test reads the
            transitions the problem's clauses force into the family's unknowns
            (a clause whose only head is one of them and whose body is
            linear) and decides over the rationals whether one tuple of affine
            functions per head ranks them lexicographically; it runs once per
            problem and family, when the phase is first exhausted.  The
            restart helps exactly where the lexicographic-only phase was
            futile (a counter that wraps around to a constant), and costs the
            answer where the compound step from three components is what
            ranks the component (a triply nested loop); the test tells the two
            apart before the step.  Undecided (a non-linear body, a body over
            other unknowns that cannot be dropped, too many disjuncts) keeps
            [Compound]. *)
  [@@deriving yojson]

  type t = {
    lexico_only_growth_until : int; [@default 3]
        (** while the template has one piece and fewer lexicographic components
            than this, a shape growth adds a lexicographic component alone,
            instead of a component, a piece and a discriminator conjunct
            together.  [1] restores the growth of every family at once; the
            default 3 lets a family grow to three components before it takes
            pieces, which over the termination-competition integer transition
            systems answered twenty more inputs under the parity reduction than
            [1] and lost one.  A parity progress measure must decrease on every
            call inside a component, so a nested loop needs a second
            lexicographic component at its outer head before it needs pieces,
            and pieces multiply the template by the square of their number on
            every unknown of the family.  Applied only to a family with two or
            more recursive tags (tags on a cycle of the family's call graph:
            a component with two or more heads); a family of one
            self-recursive head grows as by default, whatever non-recursive
            tags the family also holds. *)
    lexico_exhausted_growth : lexico_exhausted_growth; [@default Restart_all_if_no_lex_ranking]
        (** the growth taken once the lexicographic-only phase has reached
            [lexico_only_growth_until] components with one piece *)
    lexico_only_max_tags : int option; [@default None]
        (** [Some m]: the lexicographic-only phase (and the growth taken when
            it is exhausted) applies only to a family of at most [m] recursive
            tags; a larger family grows as a family of one tag does.  [None]
            (the default) applies it to every family of two or more recursive
            tags.  A search
            change, off by default: on a family of five tags the phase's
            three-component shape was seen to be asked one query Z3 did not
            decide within the run, the template being one ranking tuple per
            tag compared on every pair of tags. *)
    exists_unbounds_const : bool; [@default true]
        (** with [lexico_exhausted_growth = Restart_all_if_no_lex_ranking],
            when the lexicographic ranking test answers that a lexicographic
            linear ranking exists, a shape failure at the exhausted phase
            raises the ranking functions' constant bound (by the ordinary
            step, which ends in no bound at all once the configured
            [unbounded_above] is passed) instead of taking the compound step,
            and takes the compound step only once that bound is gone.  A
            search change, on by default: over 1,424 termination inputs
            under the two parity-reduction configurations measured it
            answered more runs and changed no verdict.  Why: the ranking the
            test finds
            may need a constant far above the bound the phase reached (a loop
            bounded by 255 ranked by [255 - j]), and the compound step from
            three components asks four components times two pieces with an
            unbounded coefficient, a query Z3 was seen not to decide in the
            run.  Like every growth here it is taken once per unknown of the
            family labelled in the failing round. *)
    timeout_as_shape_failure_after : int option; [@default None]
        (** [Some n]: the synthesis query's own timeout, which labels every
            unknown [TimeOut], is read as a failure of the template's shape
            (the growth a shape label asks for, the priority switch included)
            once it is the [n+1]-th consecutive timeout at the same template
            state (shape and bounds): the first [n] are left to the budget
            doubling, so the same query is re-asked at twice, ..., [2^n] times
            the budget, and the next timeout grows the shape instead.  [None]
            (the default) ignores [TimeOut], as every template does, and the
            same query is re-asked at a doubled budget up to
            [max_synthesis_timeout].  A search change: a timeout is not a
            proof that the shape has no solution, so a solution this shape
            would have reached with a longer budget may be passed over; it
            is off by default.  With [fix_shape] nothing grows and [TimeOut]
            stays ignored. *)
    nested_levels : bool; [@default false]
        (** write each relation's lexicographic comparison of its [L] ranking
            components in the nested form, which builds [2L - 1] decrease
            templates ([2L] at an accepting priority) instead of the level
            disjunction's [L(L+1)/2] ([+ L]); see
            [Templ.gen_simplified_parity_predicate].  Exact: the same relation
            over the same parameters, so the same candidates satisfy every
            example; each example's constraint is smaller (on a loop hierarchy
            five deep, 9 decrease templates instead of 15), and fresh names are
            drawn in another order, which moves single runs. *)
  }
  [@@deriving yojson]

  module type ConfigType = sig
    val config : t
  end
end

module type ArgType = sig
  val name : Ident.tvar
  val fenv : LogicOld.FunEnv.t
  val id : int option
  val nwf_tag : (Kind.nwf * (Ident.tvar * Ident.tvar)) option

  (* the tag pairs [(l, r)] of every member [R_(l,r)] of this unknown's
     family; the parity reduction makes a member for each call from the
     predicate [l] to the predicate [r] inside the family, so these are the
     edges of the family's call graph *)
  val family_calls : (Ident.tvar * Ident.tvar) list

  (* the problem's clauses; forced only by the lexicographic-ranking test *)
  val problem_clauses : ClauseOld.t list Lazy.t
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

(* The lexicographic-ranking test's verdict per solver instance and family,
   with the clause list it was computed from (compared physically, so a new
   problem under the same instance and family name is tested afresh).  The
   test is a function of the clauses and the family, so the memo only saves
   repeating it for each unknown of the family.  The key also says whether the
   priorities read are the switch's target (taken or asked about before it is
   taken) or the initial ones, since which transitions must be ranked
   strictly follows from the priorities. *)
let lex_ranking_memo :
    ( int option * Ident.tvar * bool,
      ClauseOld.t list Lazy.t
      * [ `Exists of int | `None_exists of int | `Undecided of string ] )
    Hashtbl.Poly.t =
  Hashtbl.Poly.create ()

let lex_ranking_memo_lock = Stdlib.Mutex.create ()

(* A family's run of consecutive synthesis timeouts, for
   [Config.timeout_as_shape_failure_after]: the template state the run is at
   ([None]: no run), how many timeouts it has counted there, and whether the
   timeout of the query last built has been counted yet. *)
type timeout_run = {
  mutable run_state : string option;
  mutable run_count : int;
  mutable counted : bool;
}

(* per solver instance and family, with the clause list the run was counted
   under (compared physically, as in [lex_ranking_memo]) *)
let timeout_runs :
    (int option * Ident.tvar, ClauseOld.t list Lazy.t * timeout_run) Hashtbl.Poly.t
    =
  Hashtbl.Poly.create ()

let timeout_runs_lock = Stdlib.Mutex.create ()

(* [dnf_atoms ~limit phi]: the disjunctive normal form of the
   negation-normal-form formula [phi] as a list of conjunctions of atoms, a
   negated atom pushed into its predicate symbol and [t1 <> t2] over numbers
   split into [t1 < t2] and [t1 > t2]; [None] when [phi] is not of that shape
   (a binder, a let, an atom whose negation has no symbol) or when the form
   would have more than [limit] disjuncts, which is decided while building it,
   before any solver is asked.  Exact: the result's disjunction is
   equivalent to [phi]. *)
let dnf_atoms ~limit phi =
  let open LogicOld in
  let exception Out in
  let cap l = if List.length l > limit then raise Out else l in
  let neg_atom = function
    | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _) ->
        let s = Term.sort_of t1 in
        if Term.is_int_sort s then
          [ [ T_int.mk_lt t1 t2 ]; [ T_int.mk_gt t1 t2 ] ]
        else if Term.is_real_sort s then
          [ [ T_real.mk_rlt t1 t2 ]; [ T_real.mk_rgt t1 t2 ] ]
        else raise Out
    | a -> ( match Atom.negate a with Some a' -> [ [ a' ] ] | None -> raise Out)
  in
  let rec go = function
    | Formula.Atom (Atom.True _, _) -> [ [] ]
    | Formula.Atom (Atom.False _, _) -> []
    | Formula.Atom (a, _) -> [ [ a ] ]
    | Formula.UnaryOp (Formula.Not, Formula.Atom (a, _), _) -> neg_atom a
    | Formula.BinaryOp (Formula.And, p1, p2, _) ->
        let d1 = go p1 and d2 = go p2 in
        if List.length d1 * List.length d2 > limit then raise Out
        else
          List.concat_map d1 ~f:(fun c1 -> List.map d2 ~f:(fun c2 -> c1 @ c2))
    | Formula.BinaryOp (Formula.Or, p1, p2, _) -> cap (go p1 @ go p2)
    | _ -> raise Out
  in
  try Some (go phi) with Out -> None

module Make
    (Cfg : WFPredicate.Config.ConfigType)
    (PCfg : Config.ConfigType)
    (Arg : ArgType) : Function.Type = struct
  let config = Cfg.config
  let parity_config = PCfg.config
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
    find_or_add_shared_info (id, nwf.name) ~create:(fun () ->
          let param =
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
          in
          ( (ref param, ref param),
            Hashtbl.Poly.
              ( Parity (create (), create (), create ()),
                map sorts_map ~f:(fun _ -> (Set.Poly.empty, Set.Poly.empty)) )
          )
    )

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
  let kind = Kind.Parity (nwf, (tag_l, tag_r))
  let flexible = false
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

  let last_cert : Templ.kind_cert_templ option ref = ref None
  let kind_cert_template () = Option.map !last_cert ~f:List.return

  let gen_template ~ucore:_ (hspace : HypSpace.hspace) =
    let template =
      let quals_x, terms_x = Hashtbl.find_exn qual_term_map tag_l in
      let quals_x = Set.to_list quals_x in
      let terms_x = Set.to_list terms_x in
      let quals_y, terms_y =
        let quals_y, terms_y = Hashtbl.find_exn qual_term_map tag_r in
        let quals_y = Set.to_list quals_y in
        let terms_y = Set.to_list terms_y in
        let ren =
          ren_of_sort_env_list
            (LogicOld.sort_env_list_of_sorts ~pre:"" sorts_r)
            (LogicOld.sort_env_list_of_sorts ~pre:""
               ~start:(List.length sorts_l) sorts_r)
        in
        (* print ren *)
        Map.Poly.iteri ren ~f:(fun ~key ~data ->
            Debug.print
            @@ lazy
                 (sprintf "renaming %s to %s" (Ident.name_of_tvar key)
                    (Ident.name_of_tvar data)));
        ( List.map quals_y ~f:(Formula.rename ren),
          List.map terms_y ~f:(Term.rename ren) )
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
             @@ String.concat_map_list ~sep:"," quals_x ~f:Formula.str_of);
        Debug.print
        @@ lazy
             (sprintf "terms_x for %s: %s" (Ident.name_of_tvar tag_l)
             @@ String.concat_map_list ~sep:"," terms_x ~f:Term.str_of);
        Debug.print
        @@ lazy
             (sprintf "quals_y for %s: %s" (Ident.name_of_tvar tag_r)
             @@ String.concat_map_list ~sep:"," quals_y ~f:Formula.str_of);
        Debug.print
        @@ lazy
             (sprintf "terms_y for %s: %s" (Ident.name_of_tvar tag_r)
             @@ String.concat_map_list ~sep:"," terms_y ~f:Term.str_of));
      Templ.gen_simplified_parity_predicate
        ~nested_levels:parity_config.nested_levels ~print:Debug.print
        (*config.use_ifte*)
        (rcs, dcs, qds)
        (* the switch, when the family has one and has taken it, changes the
           priorities between two rounds and never within one, and every
           unknown's template is generated afresh after a template update, so
           every template of a family in one round reads the same priorities *)
        (Kind.active_priorities nwf)
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
          extra_terms = config.ranking_extra_terms;
          norm_type = config.norm_type;
          lbrc = Option.map config.bounds.rfun.coeff.lower ~f:Z.of_int;
          lbdc = Option.map config.bounds.disc.coeff.lower ~f:Z.of_int;
          berc = Option.map config.bounds.rfun.coeff.per_coefficient ~f:Z.of_int;
          bedc = Option.map config.bounds.disc.coeff.per_coefficient ~f:Z.of_int;
        }
        (tag_l, params_left, tag_r, params_right)
        (quals_x, terms_x) (quals_y, terms_y)
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

  (* While the template has one piece and fewer than
     [lexico_only_growth_until] lexicographic components, a growth adds a
     component only; from there on it is the default growth.  Only a family
     with two or more recursive tags grows this way: the measure must decrease on every
     call between the heads of one component, so a nested loop needs a second
     component (or a coefficient as large as the inner trip count), while a
     single self-recursive head needs no second component and reaches the
     pieces it may need later by this route, two inputs of that shape having
     been lost to it.  A family with one recursive tag grows as by default,
     and so does a family of more recursive tags than [lexico_only_max_tags]
     when that is set.

     Only recursive tags are counted: a tag is recursive when it lies on a
     cycle of the family's call graph ([Arg.family_calls]).  A tag on no
     cycle is never ranked (no call from it returns to it), so it cannot ask
     for a second component, and the route must depend on the ranking the
     family needs, not on how the reduction grouped its predicates: without
     the decomposition into strongly connected components, a one-loop
     program's family also holds its entry predicate, which calls the loop
     head once, and counting that tag sent the single loop down the
     lexicographic-only route where the decomposed family of the same loop
     takes the default one.  With the decomposition a family of two or more
     tags is a strongly connected component, every tag of which is
     recursive, so there the count is the number of tags. *)
  let recursive_tags =
    let succs t =
      List.filter_map Arg.family_calls ~f:(fun (l, r) ->
          if Ident.tvar_equal l t then Some r else None)
    in
    (* [t] lies on a cycle iff [t] is reachable from a successor of [t] *)
    let on_cycle t =
      let seen = Hash_set.Poly.create () in
      let rec reach = function
        | [] -> false
        | u :: rest ->
            if Ident.tvar_equal u t then true
            else if Hash_set.mem seen u then reach rest
            else (
              Hash_set.add seen u;
              reach (succs u @ rest))
      in
      reach (succs t)
    in
    List.filter (Hashtbl.Poly.keys nwf.sorts_map) ~f:on_cycle

  let multi_tag_family =
    let route_of n =
      n >= 2
      &&
      match parity_config.lexico_only_max_tags with
      | None -> true
      | Some m -> n <= m
    in
    let n_tags = Hashtbl.Poly.length nwf.sorts_map in
    let n_rec = List.length recursive_tags in
    let route = route_of n_rec in
    let name_of_route b = if b then "lexicographic-first" else "default" in
    Debug.print
    @@ lazy
         (sprintf
            "parity growth route of %s (%s): tags %d, recursive tags %d [%s], \
             route %s (counting every tag: %s)"
            (Ident.name_of_tvar nwf.name)
            (Ident.name_of_tvar Arg.name)
            n_tags n_rec
            (String.concat_map_list ~sep:"," recursive_tags
               ~f:Ident.name_of_tvar)
            (name_of_route route)
            (name_of_route (route_of n_tags)));
    route

  (* The transitions the clauses force into the family's unknowns, as
     regions for [RankingCheck.multi_location_llrf].  A clause whose only
     positive atom is a family unknown [R_(l,r)(s, t)] contributes, for each
     disjunct of its negated pure part, the region of [(x, y)] with
     [x = s], [y = t] (numeric positions only) and the disjunct; every other
     variable is a further, existential column.  A negative atom of an
     unknown outside the family is dropped, which enlarges the region: the
     clause forces [R] on the region only where that unknown holds, so the
     test then reads a relation larger than the one forced, and a [None]
     verdict can be wrong where only an invariant makes the component
     rankable (recorded with the test's theory).  Undecided: a family
     unknown in a body or beside another positive atom, a disjunct over a
     non-numeric variable, or a non-linear one.  A transition from a tag of
     accepting priority is weak: the template admits a non-strict decrease
     there, so it need not be ranked.  [priorities] are the ones whose
     acceptance decides that. *)
  let lex_ranking_regions (priorities : Kind.priorities) =
    let open LogicOld in
    let exception Undecided of string in
    let family =
      Hashtbl.Poly.keys nwf.sorts_map
      |> List.concat_map ~f:(fun l ->
          List.map (Hashtbl.Poly.keys nwf.sorts_map) ~f:(fun r ->
              (Ident.name_of_tvar (Kind.parity_tvar_of_nwf nwf l r), (l, r))))
    in
    let family_of = function
      | Atom.App (Predicate.Var (Ident.Pvar p, _), args, _) ->
          Option.map (List.Assoc.find family p ~equal:String.equal)
            ~f:(fun lr -> (lr, args))
      | _ -> None
    in
    let numeric s = Term.is_int_sort s || Term.is_real_sort s in
    let num_positions tag =
      List.filter_mapi (Hashtbl.Poly.find_exn sorts_map tag) ~f:(fun i s ->
          if numeric s then Some (i, s) else None)
    in
    let dropped = ref 0 in
    try
      let transitions =
        List.filter_map (Lazy.force Arg.problem_clauses)
          ~f:(fun (_, ps, ns, phi) ->
            if Set.exists ns ~f:(fun a -> Option.is_some (family_of a)) then
              raise (Undecided "a family unknown in a body");
            match List.filter_map (Set.to_list ps) ~f:family_of with
            | [] -> None
            | [ ((l, r), args) ] when Set.length ps = 1 ->
                dropped := !dropped + Set.length ns;
                let n_l = List.length (Hashtbl.Poly.find_exn sorts_map l) in
                let side tag offset =
                  List.map (num_positions tag) ~f:(fun (i, s) ->
                      let v = Ident.mk_fresh_tvar ~prefix:(Some "LLRFs_") () in
                      ( (v, s),
                        Formula.eq (Term.mk_var v s)
                          (List.nth_exn args (offset + i)) ))
                in
                let xs = side l 0 and ys = side r n_l in
                let eqs = List.map (xs @ ys) ~f:snd in
                let xs = List.map xs ~f:fst and ys = List.map ys ~f:fst in
                let body =
                  Formula.nnf_of @@ Formula.elim_neq @@ Formula.elim_ite
                  @@ Formula.mk_neg phi
                in
                let disjuncts =
                  match dnf_atoms ~limit:64 body with
                  | Some d -> d
                  | None -> raise (Undecided "a body outside the shape")
                in
                let regions =
                  List.map disjuncts ~f:(fun atoms ->
                      let region =
                        Formula.and_of (eqs @ List.map atoms ~f:Formula.mk_atom)
                      in
                      let others =
                        Set.to_list (Formula.term_sort_env_of region)
                        |> List.filter ~f:(fun (v, _) ->
                            not
                              (List.exists (xs @ ys) ~f:(fun (w, _) ->
                                   Ident.tvar_equal v w)))
                      in
                      match
                        PCSatCommon.RankingCheck.region_rows_over (xs @ ys @ others) region
                      with
                      | Some rows -> rows
                      | None -> raise (Undecided "a region that is not linear"))
                in
                let strict =
                  let _, sigma, _, acc_set = priorities in
                  not (Set.mem acc_set (Map.Poly.find_exn sigma l))
                in
                Some (l, r, strict, regions)
            | _ -> raise (Undecided "a family unknown beside another head"))
      in
      Ok
        ( transitions,
          (fun tag -> List.length (num_positions tag)),
          !dropped )
    with Undecided reason -> Error reason

  (* the test's verdict for this family, computed once per clause list, with
     the strictness of the active priorities, or of the switch's target with
     [~target:true] (the family's priorities, when it has no switch) *)
  let lex_ranking_verdict ?(target = false) () =
    let target_priorities =
      match nwf.priority_switch with
      | Some { target = p; _ } when target -> Some p
      | _ -> None
    in
    let priorities =
      match target_priorities with
      | Some p -> p
      | None -> Kind.active_priorities nwf
    in
    let key =
      ( id,
        nwf.name,
        Option.is_some target_priorities || Kind.priority_switched nwf )
    in
    let cached =
      Stdlib.Mutex.protect lex_ranking_memo_lock (fun () ->
          match Hashtbl.Poly.find lex_ranking_memo key with
          | Some (cls, v) when phys_equal cls Arg.problem_clauses -> Some v
          | _ -> None)
    in
    match cached with
    | Some v -> v
    | None ->
        let v =
          Common.PhaseTime.with_phase "lex-ranking-test" @@ fun () ->
          match lex_ranking_regions priorities with
          | Error reason -> `Undecided reason
          | Ok (transitions, dims, dropped) ->
              Debug.print
              @@ lazy
                   (sprintf
                      "lexicographic ranking test: %d transitions, %d body \
                       atoms of other unknowns dropped, %d regions"
                      (List.length transitions) dropped
                      (List.sum (module Int) transitions ~f:(fun (_, _, _, rs) ->
                           List.length rs)));
              PCSatCommon.RankingCheck.multi_location_llrf ~id ~dims transitions
        in
        Stdlib.Mutex.protect lex_ranking_memo_lock (fun () ->
            Hashtbl.Poly.set lex_ranking_memo ~key ~data:(Arg.problem_clauses, v));
        Debug.print
        @@ lazy
             (sprintf "************* lexicographic ranking test for %s: %s"
                (Ident.name_of_tvar nwf.name)
                (match v with
                | `Exists k -> sprintf "exists (%d rounds)" k
                | `None_exists m -> sprintf "none (%d regions unranked)" m
                | `Undecided r -> "undecided: " ^ r));
        v

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
    let open WFPredicate.ShapeGrowth in
    pa
    |> move ~inc:increase_rfun_lexicos ~dec:decrease_rfun_lexicos param.nl nl
    |> move ~inc:increase_rfun_pieces ~dec:decrease_rfun_pieces param.np np
    |> move ~inc:increase_disc_conj ~dec:decrease_disc_conj param.ndc ndc
    |> move ~inc:increase_depth ~dec:decrease_depth param.depth depth

  let cost_step ~lexicos_first ((param, _) as pa) =
    let nl, np =
      WFPredicate.ShapeGrowth.next_by_cost ~lexicos_first
        ~nl0:config.number_of_rfun_lexicos ~np0:config.number_of_rfun_pieces
        (param.nl, param.np)
    in
    move_shape
      ( nl,
        np,
        WFPredicate.ShapeGrowth.disc_conj_for ~ndc0:config.number_of_disc_conj
          ~np0:config.number_of_rfun_pieces np,
        WFPredicate.ShapeGrowth.depth_for ~depth0:config.term_depth
          ~cur_depth:param.depth nl )
      pa

  (* the growth that [Config.shape_growth] takes where the parity template
     has no growth of its own (outside the lexicographic-only phase and its
     exhaustion) *)
  let generic_step pa =
    match config.shape_growth with
    | Diagonal | Orthant_pieces -> diagonal_step pa
    | Cost_ordered_lexicos_first -> cost_step ~lexicos_first:true pa
    | Cost_ordered_pieces_first -> cost_step ~lexicos_first:false pa

  (* one shape for the whole family: the most real-sorted coordinates any
     of its heads has *)
  let orthant_pieces =
    Hashtbl.Poly.fold sorts_map ~init:None ~f:(fun ~key:_ ~data acc ->
        match (WFPredicate.ShapeGrowth.orthant_pieces data, acc) with
        | Some n, Some m -> Some (Int.max n m)
        | Some n, None | None, Some n -> Some n
        | None, None -> None)

  let increase_lexico_piece_conj (param, actions) =
    match (config.shape_growth, orthant_pieces) with
    | Orthant_pieces, Some n
      when param.nl <= 1 && param.np <= 1 && n > param.np ->
        (* before the lexicographic-only phase: a family over real-sorted
           coordinates takes its orthant pieces first *)
        Debug.print
        @@ lazy
             (sprintf "************* orthant pieces for %s: %d pieces"
                (Ident.name_of_tvar Arg.name)
                n);
        move_shape (param.nl, n, param.ndc, param.depth) (param, actions)
    | _ ->
    let exhausted =
      multi_tag_family && param.np <= 1
      && parity_config.lexico_only_growth_until > init.nl
      && param.nl >= parity_config.lexico_only_growth_until
    in
    if
      multi_tag_family && param.np <= 1
      && param.nl < parity_config.lexico_only_growth_until
    then
      increase_rfun_lexicos (param, actions)
    else if
      (* [exists_unbounds_const]: at the exhausted phase, while the ranking
         functions' constant bound is still a bound and the test says a
         lexicographic linear ranking exists, the bound grows in place of the
         compound step; [increase_rfun_const] turns it into no bound once it
         reaches [unbounded_above], so this is taken finitely often between
         two restarts; the synthesizer's restart of every template (after
         [restart_threshold] iterations with no template update, which the
         unbounded shape reaches when its candidates keep being refuted)
         brings the bound back, and the phase, and this step with it, run
         again *)
      exhausted && parity_config.exists_unbounds_const
      && Option.is_some param.ubrd
      && (match parity_config.lexico_exhausted_growth with
         | Restart_all_if_no_lex_ranking -> (
             match lex_ranking_verdict () with
             | `Exists _ -> true
             | `None_exists _ | `Undecided _ -> false)
         | _ -> false)
    then (
      Debug.print
      @@ lazy
           ("************* lexicographic-only phase exhausted for "
           ^ Ident.name_of_tvar Arg.name
           ^ " with a lexicographic ranking: raising the constant bound \
              before the compound step ***************");
      increase_rfun_const config.bounds.rfun.const.unbounded_above
        (param, actions))
    else if
      exhausted
      && (match parity_config.lexico_exhausted_growth with
         | Compound -> false
         | Restart_lexicos | Restart_all | Pieces_only -> true
         | Restart_all_if_no_lex_ranking -> (
             (* the step is the restart only when no lexicographic linear
                ranking exists; otherwise the compound step below *)
             Debug.print
             @@ lazy
                  ("************* lexicographic-only phase exhausted for "
                  ^ Ident.name_of_tvar Arg.name
                  ^ " (testing for a lexicographic ranking) ***************");
             match lex_ranking_verdict () with
             | `None_exists _ -> true
             | `Exists _ | `Undecided _ -> false))
    then
      (* the lexicographic-only phase is exhausted: [Restart_lexicos] drops
         its components and takes the step from one component and one piece,
         [Restart_all] also drops the bounds raised meanwhile, and
         [Pieces_only] keeps the components and adds a piece and a conjunct *)
      let () =
        Debug.print
        @@ lazy
             ("************* lexicographic-only phase exhausted for "
             ^ Ident.name_of_tvar Arg.name
             ^ " ***************")
      in
      match parity_config.lexico_exhausted_growth with
      | Restart_lexicos ->
          increase_disc_conj @@ increase_rfun_pieces
          @@ increase_rfun_lexicos @@ init_rfun_lexicos (param, actions)
      | Restart_all | Restart_all_if_no_lex_ranking ->
          increase_disc_conj @@ increase_rfun_pieces
          @@ increase_rfun_lexicos
          @@ restart (param, actions)
      | Pieces_only | Compound ->
          increase_disc_conj @@ increase_rfun_pieces (param, actions)
    else generic_step (param, actions)

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

  let actions_of labels =
    (snd @@ inner (!param, []) @@ Set.to_list labels) @ [ "end" ]

  (* [take_switch ()]: takes the family's priority switch if it has one not
     yet taken (see [Kind.priority_switch]), and says whether it did.  The
     coefficient arrays cached per tag are dropped with it: their number of
     ranking components is the old priorities' and the switch may change it. *)
  let take_switch () =
    if Kind.take_priority_switch nwf then (
      Hashtbl.Poly.clear rcs;
      Hashtbl.Poly.clear dcs;
      Hashtbl.Poly.clear qds;
      let max_pri, _, _, _ = Kind.active_priorities nwf in
      Debug.print
      @@ lazy
           (sprintf
              "************* switching the priorities of %s (at %s, %d ranking \
               components) ***************"
              (Ident.name_of_tvar nwf.name)
              (Ident.name_of_tvar Arg.name)
              max_pri);
      true)
    else false

  let is_shape_label = function LexicoPieceConj | Shape -> true | _ -> false

  (* Whether the switch's gate lets a shape failure take it now (see
     [Kind.switch_gate]): with [Rankable_shape_failure], not when the
     family's transitions are known to have no lexicographic linear ranking
     function under the target's strictness; an undecided test is no such
     knowledge.  Asked only on a shape failure that finds the switch untaken,
     and memoised per clause list. *)
  let gate_open () =
    match nwf.priority_switch with
    | Some { gate = Kind.Rankable_shape_failure; switched; _ }
      when not (Stdlib.Atomic.get switched) -> (
        match lex_ranking_verdict ~target:true () with
        | `None_exists _ ->
            Debug.print
            @@ lazy
                 (sprintf
                    "************* not switching the priorities of %s: its \
                     transitions have no lexicographic linear ranking \
                     ***************"
                    (Ident.name_of_tvar nwf.name));
            false
        | `Exists _ | `Undecided _ -> true)
    | Some { gate = Kind.Unrankable_at_start; _ } -> false
    | _ -> true

  (* With the gate [Unrankable_at_start] the switch is decided before the
     family's first template: taken (the family moves to the target's
     priorities for the run) exactly when the lexicographic ranking test,
     read with the initial priorities' strictness, answers [None_exists].
     Every unknown of the family asks before generating its first template
     and the answer is memoised per family, so no template of the family is
     ever generated from priorities the decision then changes.
     [decided_at_start] makes it once per unknown. *)
  let decided_at_start = ref false

  let decide_switch_at_start () =
    if not !decided_at_start then (
      decided_at_start := true;
      match nwf.priority_switch with
      | Some { gate = Kind.Unrankable_at_start; switched; _ }
        when not (Stdlib.Atomic.get switched) -> (
          match lex_ranking_verdict () with
          | `None_exists _ -> ignore (take_switch () : bool)
          | `Exists _ | `Undecided _ -> ())
      | _ -> ())

  (* A shape failure that finds the switch untaken and its gate open takes it
     (with the default gate, the family's first shape failure); the switch
     then takes the place of the shape growth that failure asks for (the
     bounds still grow as their labels say).  Another unknown of the family
     labelled in the same update finds the switch taken and grows the shape
     as usual, as two unknowns of a family labelled in one update always grow
     it twice. *)
  (* [timeout_as_shape_failure_after]: the family's run of consecutive
     timeouts (see [timeout_runs]).  A run belongs to a clause list (compared
     physically, so a new problem under the same instance and family name
     starts afresh). *)
  let timeout_run () =
    Stdlib.Mutex.protect timeout_runs_lock (fun () ->
        let key = (id, nwf.name) in
        match Hashtbl.Poly.find timeout_runs key with
        | Some (cls, run) when phys_equal cls Arg.problem_clauses -> run
        | _ ->
            let run = { run_state = None; run_count = 0; counted = false } in
            Hashtbl.Poly.set timeout_runs ~key ~data:(Arg.problem_clauses, run);
            run)

  (* [labels] with [TimeOut] replaced by a shape label when it is the
     [n+1]-th consecutive timeout at the family's current template state
     ([timeout_as_shape_failure_after = Some n]); [labels] itself otherwise,
     and always with the field [None] or with [fix_shape].

     One timeout labels every unknown of the family, and they share one
     shape, so the timeout is counted once, by the first unknown of the
     family that is updated after it ([counted], cleared when the next
     template is generated, that is, when the next query is built); the
     other unknowns labelled by the same timeout leave [TimeOut] as it is,
     which changes nothing.  So one timeout grows the family's shape at most
     once.  A round whose labels have no [TimeOut] ends the run.  The state
     compared is [str_of], which shows the shape and every bound. *)
  let timeout_as_shape_label labels =
    match parity_config.timeout_as_shape_failure_after with
    | None -> labels
    | Some _ when config.fix_shape -> labels
    | Some n ->
        let run = timeout_run () in
        if not (Set.mem labels TimeOut) then (
          run.run_state <- None;
          run.run_count <- 0;
          labels)
        else if run.counted then labels
        else (
          run.counted <- true;
          let state = str_of () in
          let count =
            match run.run_state with
            | Some s when String.equal s state -> run.run_count + 1
            | _ -> 1
          in
          if count > n then (
            run.run_state <- None;
            run.run_count <- 0;
            Debug.print
            @@ lazy
                 (sprintf
                    "************* timeout %d at one shape of %s: read as a \
                     shape failure ***************"
                    count
                    (Ident.name_of_tvar Arg.name));
            Set.add (Set.remove labels TimeOut) LexicoPieceConj)
          else (
            run.run_state <- Some state;
            run.run_count <- count;
            labels))

  let update_with_labels labels =
    let labels = timeout_as_shape_label labels in
    let labels =
      if
        (not config.fix_shape)
        && Set.exists labels ~f:is_shape_label
        && gate_open () && take_switch ()
      then Set.filter labels ~f:(Fn.non is_shape_label)
      else labels
    in
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

  (* every template is generated after the start decision of the switch (a
     no-op for a family without an [Unrankable_at_start] switch) *)
  let gen_template ~ucore hspace =
    decide_switch_at_start ();
    (* a new query is being built: its timeout, if it has one, is counted
       afresh (see [timeout_as_shape_label]) *)
    if Option.is_some parity_config.timeout_as_shape_failure_after then
      (timeout_run ()).counted <- false;
    gen_template ~ucore hspace

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
