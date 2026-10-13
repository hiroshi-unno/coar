open Core
open Common.Ext
open Common.Combinator
open Logic

type nwf = {
  name : Ident.tvar;
  sorts_shared : Sort.t list;
  sorts_map : (Ident.tvar, Sort.t list) Hashtbl.Poly.t;
  max_pri : int; (* maximum priority *)
  sigma : (Ident.tvar, int) Map.Poly.t; (* priority function *)
  trunc : int -> int; (* truncation function *)
  acc_set : int Set.Poly.t (* accepting states I *);
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
  }

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

type t =
  | Ord
  | FN
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
  | Adm of (* conditioning *) bool
  | Integ
  | IntFun
  | RealFun
  | RegEx

type map = (Ident.tvar, t) Map.Poly.t

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
let is_adm_with_cond = function Adm true -> true | _ -> false
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
  | FN -> "functional predicate"
  | Uniq (j, p) ->
      sprintf "single-valued predicate at position %d (%s)" j (str_of_provenance p)
  | Tot u ->
      sprintf "total predicate over universal positions {%s}"
        (String.concat_map_list ~sep:"," u ~f:string_of_int)
  | WF -> "well-founded predicate"
  | DWF -> "disjunctively well-founded predicate"
  | NWF _ -> "global well-founded predicate"
  | Parity _ -> "parity predicate"
  | Adm true -> "admissible predicate w/ conditioning"
  | Adm false -> "admissible predicate w/o conditioning"
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
  | Adm true -> "AdmC"
  | Adm false -> "Adm"
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
  | Adm b1, Adm b2 -> Bool.equal b1 b2
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
