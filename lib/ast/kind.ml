open Core
open Common.Ext
open Common.Combinator
open Logic

(* A parity family's priorities: the number of ranking components, the
   priority of each tag, the truncation of a priority to the number of
   components it compares, and the accepting priorities -- the four the
   parity template is generated from. *)
type priorities =
  int * (Ident.tvar, int) Map.Poly.t * (int -> int) * int Set.Poly.t

(* A second priority function a family may take during the search
   ([priority_switch] of [nwf]).  [switched] is false until the search takes
   it, and never returns to false.

   Contract, which the producer of a switch must establish: the family is
   one whose initial priorities and [target] both make every parity
   relation sound (every infinite chain of a relation satisfying either
   condition is accepted by the family's own fixpoint reading), and a closed
   walk of the family's tags (a cycle of its relations' arguments) visits a
   rejecting least priority under the initial priorities exactly when it does
   under [target].  Under that contract a fact learned from the clauses or
   from a refuted cycle before the switch holds after it, so the search may
   keep its examples, and a relation found under either priority function
   proves what the family is to prove.  A loop-hierarchy priority function
   against alternation depth's, on a component with no greatest fixpoint,
   is such a pair. *)
type priority_switch = {
  target : priorities;
  switched : bool Stdlib.Atomic.t;
  gate : switch_gate;
}

(* When a shape failure takes the switch.  [Any_shape_failure]: the family's
   first shape failure does.  [Rankable_shape_failure]: a shape failure does
   only while the family's transitions, read off the clauses with every other
   unknown dropped and ranked with [target]'s strictness, are not known to
   lack a lexicographic linear ranking function; when they are known to lack
   one (the test is exact for its class and depends on the clauses only), no
   shape failure takes the switch and the family keeps its initial
   priorities throughout.  The reason: what [target] adds is a ranking
   component per nested loop, which helps only a ranking those transitions
   can carry; when they carry none, the solution needs invariants the bare
   transitions do not have, or there is none and the run is to end in a
   refutation, and in both cases the wider template only delays the search
   the initial priorities were making.  Soundness does not depend on the
   gate: either priority function's relation proves what the family is to
   prove, and the two refute the same closed walks.
   [Unrankable_at_start]: no shape failure takes the switch; the search takes
   it before the family's first template is generated, exactly when the
   family's transitions (read as for [Rankable_shape_failure]) are known to
   lack a lexicographic linear ranking function under the {e initial}
   priorities' strictness, and never otherwise.  It is meant for a family
   whose initial priorities are the loop-hierarchy ones and whose [target] is
   alternation depth's: the family then searches exactly as without a switch
   unless the test answers no, and then searches with alternation depth's
   single component from its first round.  The decision reads the clauses
   only, so it is the same for every unknown of the family and every
   round. *)
and switch_gate =
  | Any_shape_failure
  | Rankable_shape_failure
  | Unrankable_at_start

type nwf = {
  name : Ident.tvar;
  sorts_shared : Sort.t list;
  sorts_map : (Ident.tvar, Sort.t list) Hashtbl.Poly.t;
  max_pri : int; (* maximum priority *)
  sigma : (Ident.tvar, int) Map.Poly.t; (* priority function *)
  trunc : int -> int; (* truncation function *)
  acc_set : int Set.Poly.t (* accepting states I *);
  priority_switch : priority_switch option;
      (* the priorities the family may move to during the search (at a
         shape failure, or before its first template; see [switch_gate]);
         [max_pri], [sigma], [trunc] and [acc_set] above stay the initial
         ones, and the unknowns' names are made from [sigma] *)
}

let dummy_nwf =
  {
    name = Ident.Tvar "";
    sorts_shared = [];
    sorts_map = Hashtbl.Poly.create ();
    max_pri = 0;
    sigma = Map.Poly.empty;
    trunc = Fn.id;
    acc_set = Set.Poly.empty;
    priority_switch = None;
  }

(* [active_priorities nwf]: the priorities the family's template is to be
   generated from now: [target] once the switch is taken, the initial ones
   otherwise.  A reader deciding whether a ranking certificate has the shape
   the family requires must use these; a reader deciding whether a closed
   walk is refuted may use either (the switch's contract makes them agree). *)
let active_priorities nwf : priorities =
  match nwf.priority_switch with
  | Some { target; switched; _ } when Stdlib.Atomic.get switched -> target
  | _ -> (nwf.max_pri, nwf.sigma, nwf.trunc, nwf.acc_set)

(* [take_priority_switch nwf]: takes the family's switch if it has one not
   yet taken, and says whether this call took it (at most one call per family
   returns [true], also across domains). *)
let take_priority_switch nwf =
  match nwf.priority_switch with
  | Some { switched; _ } -> Stdlib.Atomic.compare_and_set switched false true
  | None -> false

let priority_switched nwf =
  match nwf.priority_switch with
  | Some { switched; _ } -> Stdlib.Atomic.get switched
  | None -> false

(* A kind is a condition on an individual solution, as against a constraint, which relates
   several.  That is what makes this class an extension of predicate constraint satisfaction
   rather than a fragment of it, and it is why a kind has no clausal form: a constrained Horn
   clause format carries constraints and has nowhere to put a condition on one predicate.

   TWO PAIRS HERE ARE NOT INDEPENDENT, and knowing it saves a reader deriving it twice.

   [Tot] is totality over a set of universally quantified argument positions: [Tot u] demands
   that for every value of the positions in [u] some value of the others makes [P] true.

     Tot []            exists x. P(x)              non-emptiness: no position universal
     Tot (all but j)   forall x. exists y. P(x,y)  the totality half of FN

   Non-emptiness is its empty-set case and is NOT special-cased: one parameterised obligation,
   one template and one simplification serve every position set.  The cheap query survives
   because of the parameter: with no universal position the obligation is closed and has no
   quantifier alternation, while any universal position makes it a forall-exists that a solver
   may not return from -- the checker carries an "undecided" arm for exactly that.  [FN] is
   [Tot] at every position but the last together with [Uniq] at the last, and stays a kind of
   its own: it is what an input states, and its template searches the joint shape, where the
   two halves separately would hand the solver two obligations and no template that knows
   them together.

   [WF] and [DWF] stand in the same relation, with WF the one-element case of a union.  The
   checker already treats them that way -- one rule whose singleton case is WF.

   EVERY KIND IS A SEMANTIC CONDITION AND EVERY ONE IS DISCHARGED SYNTACTICALLY, so
   that is not a way to tell them apart.  A kind constrains what a solution MEANS; a
   template is a syntactic family; and the way this tool discharges a kind is always
   the same -- only ever build candidates from a family whose every member has the
   property.  WF by a ranking function, FN by a functional shape, Tot by a shape that
   defines a witness at every value of its universal positions, Adm by the admissible template, Integ by the affine one.  The
   published source of the last two makes this explicit for admissibility, giving
   syntactic derivation rules, proving them sound rather than complete, and then
   proving that every instantiation of its template is admissible.

   WHAT DOES DIFFER IS WHETHER AN INDEPENDENT RE-CHECK EXISTS, and that follows from
   the SHAPE of the obligation:

     WF, DWF, NWF, Parity   the template records a certificate and the solution is
                            re-verified against it (these four are the only ones
                            whose [kind_cert_template] returns anything)
     FN, Uniq, Tot          no certificate, but the obligation IS a first-order
                            formula about the solution, so it is asked directly
                            (Uniq's is universal only: FN's without totality)
     Adm, Integ             neither, and this is why nothing re-checks them.
                            Admissibility is a closure property of a denotation,
                            quantifying over omega-chains; integrability is a
                            condition on the form together with existence of an
                            integral.  There is no query to build, so the template
                            IS the proof, and widening either shape means redoing
                            the argument that its members have the property.

   NEITHER DECOMPOSITION IS A REASON TO COLLAPSE THE KINDS.  It says what an obligation MEANS,
   not how to search for a solution: the derived kind is what an input states, it has a template
   family that searches its own shape, and rewriting it as "the primitive plus a constraint"
   hands the solver two obligations where the input gave one, with no template that knows their
   joint shape.  Primitive for the semantics, derived for the search. *)
(* How a [Uniq] kind was obtained, which decides what it licenses.
   [Declared]: the input states it, so it is part of the problem.
   [Entailed]: the clauses imply it in every solution, so assuming it restricts
   nothing.  [LeastModel]: the clauses make the predicate single-valued in the
   least model of their definite part, which in a Horn system without kinds is
   a single-valued solution whenever one exists, so restricting to
   single-valued candidates loses no satisfiability, unsat included.  An
   *assumed* uniqueness would license only [sat] and is not a provenance. *)
type provenance = Declared | Entailed | LeastModel

let str_of_provenance = function
  | Declared -> "declared"
  | Entailed -> "entailed"
  | LeastModel -> "least-model"

let provenance_of_string = function
  | "declared" -> Some Declared
  | "entailed" -> Some Entailed
  | "least-model" -> Some LeastModel
  | _ -> None

(* The truth-value domain an admissible unknown's answer value ranges over,
   which decides what admissible means for it (a set containing the domain's
   least element and closed under suprema of omega-chains, in the domain's own
   order) and so which template family has only admissible members.
   - [Adm_expectation]: [0, infinity] with the usual order; fixed points are
     least and the admissible refinements are upper bounds.
   - [Adm_conditional]: pairs, [0, infinity] times [0, 1] with the opposite
     order in the second component (a value and the probability of the valid
     runs).
   - [Adm_probability]: [0, 1] with the usual order; least fixed points, upper
     bounds, every value at most 1.
   - [Adm_liberal]: [0, 1] with the opposite order, whose least element is 1:
     a fixed point is the greatest in the usual order (a liberal
     pre-expectation, divergence counted as success) and the admissible
     refinements are lower bounds closed under infima of descending chains. *)
type adm = Adm_expectation | Adm_conditional | Adm_probability | Adm_liberal

let adm_with_cond = function Adm_conditional -> true | _ -> false

let equal_adm a1 a2 =
  match (a1, a2) with
  | Adm_expectation, Adm_expectation
  | Adm_conditional, Adm_conditional
  | Adm_probability, Adm_probability
  | Adm_liberal, Adm_liberal ->
      true
  | _, _ -> false

type t =
  | Ord
  | FN
      (** functional: the graph of a total function from the other positions
          to the last, i.e. [Uniq] at the last position together with [Tot]
          over all the others.  Stronger than the usual mathematical
          "functional relation", which asks single-valuedness only; the name
          follows the pfwCSP kind of Unno, Terauchi and Koskinen, CAV 2021. *)
  | Uniq of int * provenance
      (** single-valued in argument position [j] (0-based): two tuples that
          agree everywhere else agree at [j]; no totality.  [FN] is [Uniq] at
          the last position together with totality. *)
  | Tot of int list
      (** total over the universally quantified positions listed (0-based,
          sorted, distinct): at every value of those positions some value of
          the others satisfies the predicate.  [Tot []] is non-emptiness. *)
  | WF
  | DWF
  | NWF of nwf * (Ident.tvar * Ident.tvar)
  | Parity of nwf * (Ident.tvar * Ident.tvar)
  | Adm of adm
  | Integ
  | IntFun
  | RealFun
  | RegEx

type map = (Ident.tvar, t) Map.Poly.t

(* [drop_priority_switches kind_map]: [kind_map] with every parity family's
   switch removed, so that each family keeps its initial priorities for the
   whole search, and whether any family had one.  Postcondition: every other
   kind, and every family's name, tags, sorts and initial priorities, are
   unchanged; the relations of one family share one family record afterwards
   as before (one copy per family name), since a reader may key a cache on
   the family.  A family without a switch is returned as it was. *)
let drop_priority_switches (kind_map : map) : map * bool =
  let copies = Hashtbl.Poly.create () in
  let had = ref false in
  let kind_map =
    Map.Poly.map kind_map ~f:(function
      | Parity (({ priority_switch = Some _; _ } as nwf), lr) ->
          had := true;
          Parity
            ( Hashtbl.Poly.find_or_add copies nwf.name ~default:(fun () ->
                  { nwf with priority_switch = None }),
              lr )
      | kind -> kind)
  in
  (kind_map, !had)

let is_ord = function Ord -> true | _ -> false
let is_fn = function FN -> true | _ -> false
let is_uniq = function Uniq _ -> true | _ -> false
let is_tot = function Tot _ -> true | _ -> false
let tot_positions_of = function Tot u -> Some u | _ -> None
let is_wf = function WF -> true | _ -> false
let is_dwf = function DWF -> true | _ -> false
let is_nwf = function NWF _ -> true | _ -> false
let is_parity = function Parity _ -> true | _ -> false
let is_adm = function Adm _ -> true | _ -> false
let is_adm_with_cond = function Adm Adm_conditional -> true | _ -> false
let adm_of = function Adm a -> Some a | _ -> None
let is_integ = function Integ -> true | _ -> false
let is_int_fun = function IntFun -> true | _ -> false
let is_real_fun = function RealFun -> true | _ -> false
let is_regex = function RegEx -> true | _ -> false

let is_pred = function
  (* predicates *)
  | Ord | FN | Uniq _ | Tot _ | WF | DWF | NWF _ | Parity _ | Adm _ | Integ -> true
  (* functions *)
  | IntFun | RealFun | RegEx -> false

let str_of = function
  (* predicates *)
  | Ord -> "ordinary predicate"
  | FN -> "functional predicate (single-valued and total)"
  | Uniq (j, p) ->
      sprintf "single-valued predicate at position %d (%s)" j (str_of_provenance p)
  | Tot u ->
      sprintf "total predicate over universal positions {%s}"
        (String.concat_map_list ~sep:"," u ~f:string_of_int)
  | WF -> "well-founded predicate"
  | DWF -> "disjunctively well-founded predicate"
  | NWF _ -> "global well-founded predicate"
  | Parity _ -> "parity predicate"
  | Adm Adm_conditional -> "admissible predicate w/ conditioning"
  | Adm Adm_expectation -> "admissible predicate w/o conditioning"
  | Adm Adm_probability -> "admissible predicate over [0,1]"
  | Adm Adm_liberal -> "admissible predicate over [0,1]^op"
  | Integ -> "integrable predicate"
  (* functions *)
  | IntFun -> "integer function"
  | RealFun -> "real function"
  | RegEx -> "regular expression"

let short_str_of = function
  (* predicates *)
  | Ord -> "Ord"
  | FN -> "FN"
  | Uniq (j, _) -> sprintf "Uniq%d" j
  | Tot _ -> "Tot"
  | WF -> "WF"
  | DWF -> "DWF"
  | NWF _ -> "NWF"
  | Parity _ -> "Prty"
  | Adm Adm_conditional -> "AdmC"
  | Adm Adm_expectation -> "Adm"
  | Adm Adm_probability -> "AdmP"
  | Adm Adm_liberal -> "AdmL"
  | Integ -> "Itg"
  (* functions *)
  | IntFun -> "Int"
  | RealFun -> "Real"
  | RegEx -> "Reg"

let kind_of (kind_map : map) tv = Map.Poly.find_exn kind_map tv

(* [nwf] carries a closure ([trunc]) and a [Hashtbl], so polymorphic equality
   on a kind raises at run time; an NWF/Parity family is identified by its
   name, as SolutionTemplate does *)
let equal_nwf n1 n2 = Ident.tvar_equal n1.name n2.name

let equal k1 k2 =
  match (k1, k2) with
  | Ord, Ord
  | FN, FN
  | WF, WF
  | DWF, DWF
  | Integ, Integ
  | IntFun, IntFun
  | RealFun, RealFun
  | RegEx, RegEx ->
      true
  | NWF (n1, (l1, r1)), NWF (n2, (l2, r2))
  | Parity (n1, (l1, r1)), Parity (n2, (l2, r2)) ->
      equal_nwf n1 n2 && Ident.tvar_equal l1 l2 && Ident.tvar_equal r1 r2
  | Adm a1, Adm a2 -> equal_adm a1 a2
  | Tot u1, Tot u2 -> List.equal Int.equal u1 u2
  (* the provenance is part of the value: the same position obtained two ways
     licenses different answers, so a predicate declared both ways is a
     conflict [add_kind] reports rather than silently merges *)
  | Uniq (j1, p1), Uniq (j2, p2) -> j1 = j2 && Stdlib.(p1 = p2)
  | _, _ -> false

let add_kind tv kind (kind_map : map) =
  if Map.Poly.mem kind_map tv then
    let kind' = kind_of kind_map tv in
    if equal kind' kind then kind_map
    else
      (* [str_of] is matched on by SolutionTemplate.check_kind, so the family
         name is added here rather than there *)
      let describe = function
        | (NWF (nwf, _) | Parity (nwf, _)) as k ->
            sprintf "%s [%s]" (str_of k) (Ident.name_of_tvar nwf.name)
        | k -> str_of k
      in
      failwith
      @@ sprintf "%s is defined as %s and %s" (Ident.name_of_tvar tv)
           (describe kind) (describe kind')
  else Map.Poly.add_exn kind_map ~key:tv ~data:kind

let add_kinds senv kind (kind_map : map) =
  Set.fold ~init:kind_map senv ~f:(fun kind_map key ->
      add_kind key kind kind_map)

let add_funs (exi_senv, kind_map) kind senv =
  ( Map.force_merge exi_senv senv,
    add_kinds (Map.Poly.key_set senv) kind kind_map )

let add_pred_env_set (exi_senv, kind_map) kind pvs =
  ( Map.force_merge exi_senv
      (Map.of_set_exn
      @@ Set.Poly.map pvs ~f:(fun (pvar, sargs) ->
          ( Ident.pvar_to_tvar pvar,
            Sort.mk_fun (ExtTerm.of_old_sort_list sargs @ [ ExtTerm.SBool ]) ))
      ),
    Map.force_merge kind_map
      (Map.of_set_exn
      @@ Set.Poly.map pvs ~f:(fun (pv, _) -> (Ident.pvar_to_tvar pv, kind))) )

let pred_sort_env_map_of (exi_senv, kind_map) =
  Map.change_keys ~f:Ident.tvar_to_pvar
  @@ Map.Poly.filter_mapi exi_senv ~f:(fun ~key ~data ->
      if is_pred @@ kind_of kind_map key then
        Some (List.map ~f:ExtTerm.to_old_sort @@ Sort.args_of data)
      else None)

let pvars_of (exi_senv, kind_map) =
  Set.Poly.map ~f:Ident.tvar_to_pvar
  @@ Set.filter (Map.Poly.key_set exi_senv) ~f:(kind_of kind_map >> is_pred)

(* NWF related *)

let nwf_tvar_of_nwf name l r =
  Ident.mk_nwf_tvar name
    (Ident.Tvar (Ident.name_of_tvar l))
    (Ident.Tvar (Ident.name_of_tvar r))

let kind_map_of_nwf nwf : map =
  let sorts_map = Hashtbl.Poly.to_alist nwf.sorts_map in
  Map.Poly.of_alist_exn
  @@ List.concat_map sorts_map ~f:(fun (tag_l, _) ->
      List.map sorts_map ~f:(fun (tag_r, _) ->
          (Ident.mk_nwf_tvar nwf.name tag_l tag_r, NWF (nwf, (tag_l, tag_r)))))

let app_nwf_predicate nwf params (tag_l, params_l) (tag_r, params_r) =
  assert (List.length params = List.length nwf.sorts_shared);
  let wfp = Ident.mk_nwf_tvar nwf.name tag_l tag_r in
  assert (Hashtbl.Poly.(mem nwf.sorts_map tag_l && mem nwf.sorts_map tag_r));
  let sorts_l = Hashtbl.Poly.find_exn nwf.sorts_map tag_l in
  let sorts_r = Hashtbl.Poly.find_exn nwf.sorts_map tag_r in
  assert (
    List.length sorts_l = List.length params_l
    && List.length sorts_r = List.length params_r);
  ( wfp,
    Sort.mk_fun @@ nwf.sorts_shared @ sorts_l @ sorts_r @ [ ExtTerm.SBool ],
    ExtTerm.mk_var_app wfp @@ params @ params_l @ params_r )

(*
let app_nwf_predicate_and_add_tag nwf params (tag_l, sorts_l, params_l)
    (tag_r, sorts_r, params_r) =
  Hashtbl.Poly.set nwf.sorts_map ~key:tag_l ~data:sorts_l;
  Hashtbl.Poly.set nwf.sorts_map ~key:tag_r ~data:sorts_r;
  app_nwf_predicate nwf params (tag_l, params_l) (tag_r, params_r)

let app_nwf_predicate_and_add_tag_old nwf params (tag_l, sorts_l, params_l)
    (tag_r, sorts_r, params_r) =
  Hashtbl.Poly.set nwf.sorts_map ~key:tag_l ~data:sorts_l;
  Hashtbl.Poly.set nwf.sorts_map ~key:tag_r ~data:sorts_r;
  let params_new = List.map params ~f:ExtTerm.of_old_term in
  let params_l_new = List.map params_l ~f:ExtTerm.of_old_term in
  let params_r_new = List.map params_r ~f:ExtTerm.of_old_term in
  let wfp, psort, term =
    app_nwf_predicate nwf params_new (tag_l, params_l_new) (tag_r, params_r_new)
  in
  let uni_senv =
    Map.of_set_exn @@ of_old_sort_env_set @@ Set.Poly.union_list
    @@ List.map ~f:LogicOld.Term.sort_env_of (params @ params_l @ params_r)
  in
  ( wfp,
    ExtTerm.to_old_sort psort,
    ExtTerm.to_old_fml (Map.Poly.singleton wfp psort) uni_senv term )
*)

(* Parity related *)

let parity_tvar_of_nwf nwf l r =
  Ident.mk_parity_tvar nwf.name
    (Ident.Tvar
       (Ident.name_of_tvar l ^ "@" ^ string_of_int
       @@ Map.Poly.find_exn nwf.sigma l))
    (Ident.Tvar
       (Ident.name_of_tvar r ^ "@" ^ string_of_int
       @@ Map.Poly.find_exn nwf.sigma r))

let kind_map_of_parity nwf : map =
  let sorts_map = Hashtbl.Poly.to_alist nwf.sorts_map in
  Map.Poly.of_alist_exn
  @@ List.concat_map sorts_map ~f:(fun (tag_l, _) ->
      List.map sorts_map ~f:(fun (tag_r, _) ->
          ( Ident.mk_parity_tvar nwf.name
              (Ident.Tvar
                 (Ident.name_of_tvar tag_l ^ "@" ^ string_of_int
                 @@ Map.Poly.find_exn nwf.sigma tag_l))
              (Ident.Tvar
                 (Ident.name_of_tvar tag_r ^ "@" ^ string_of_int
                 @@ Map.Poly.find_exn nwf.sigma tag_r)),
            Parity (nwf, (tag_l, tag_r)) )))

let app_parity_predicate nwf (tag_l, params_l) (tag_r, params_r) =
  assert (List.is_empty nwf.sorts_shared);
  let wfp = Ident.mk_nwf_tvar nwf.name tag_l tag_r in
  assert (Hashtbl.Poly.(mem nwf.sorts_map tag_l && mem nwf.sorts_map tag_r));
  let sorts_l = Hashtbl.Poly.find_exn nwf.sorts_map tag_l in
  let sorts_r = Hashtbl.Poly.find_exn nwf.sorts_map tag_r in
  assert (
    List.length sorts_l = List.length params_l
    && List.length sorts_r = List.length params_r);
  ( wfp,
    Sort.mk_fun @@ sorts_l @ sorts_r @ [ ExtTerm.SBool ],
    ExtTerm.mk_var_app wfp @@ params_l @ params_r )
