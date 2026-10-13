(* Clauses over the first-order term language [LogicOld], as the
   preprocessing and the example-based phases of the constraint solver use
   them.

   A clause [(senv, ps, ns, phi)] denotes the universal closure over [senv] of
   [\/ ps \/ \/ (not ns) \/ phi]: [ps] are the positive predicate
   applications, [ns] the negative ones, and [phi] the pure part.  The pure
   part is assumed to mention no unknown: [pvs_of] skips it, and everything
   that decides from the atom sets alone (which unknowns a clause uses, how
   often) inherits that assumption, which a Horn clause meets for free and a
   pfwnCSP premise equating an unknown with a term does not.

   The semantics is per model of the background theory: a clause holds when
   it holds in every model, so a disjunct is dropped on validity, never on
   satisfiability, and "invalid" is read as "false" only for a formula the
   theory fixes ([interpretation_dependent] says which are not, by symbol).
   [simplify] implements that rule.

   The rest shrinks a clause to an equivalent one.  Condensation -- removing
   literals that are renamed or instantiated copies of others, after
   W. H. Joyner, "Resolution strategies as decision procedures", JACM 1976 --
   is [condense] over the atoms, the joint atom-and-pure search seeded by
   [joint_atom_seeds], and [condense_pure] over the disjuncts of the pure
   part; [merge_int_var_equations] removes a disjunct [x != y] by renaming
   [y] into [x].  Each is exact; their budgets bound how much is searched,
   never what a found result means. *)
open Core
open Common.Ext
open Common.Combinator
open LogicOld

type t = Logic.sort_env_map * Atom.t Set.Poly.t * Atom.t Set.Poly.t * Formula.t

let pvs_of (_, ps, ns, _phi) = Set.union ps ns |> Set.concat_map ~f:Atom.pvs_of

let simplify_with positive negative (c_pos, c_neg, c_pure) =
  if Set.are_disjoint c_pos positive && Set.are_disjoint c_neg negative then
    Some (Set.diff c_pos negative, Set.diff c_neg positive, c_pure)
  else None

let rec separate vs phis =
  let phis1, phis2 =
    Set.partition_tf phis ~f:(fun (fvs, _) -> Set.are_disjoint fvs vs)
  in
  let dvs = Set.diff (Set.concat_map ~f:fst phis2) vs in
  if Set.is_empty dvs then (phis1, phis2)
  else
    let phis11, phis12 = separate dvs phis1 in
    (phis11, Set.union phis12 phis2)

(* A formula whose truth value can differ between models of the background
   theory: selectors applied to the wrong constructor ([tl nil]), uninterpreted
   function symbols, division and remainder (division by zero is unspecified,
   integer and real alike) and a sequence read ([seq.nth s i] is unspecified
   when [i] is outside [s]).  For such a formula "invalid" (false in some
   model) is not "false".

   The inventory is by SYMBOL and not by argument, so a division by a nonzero
   literal and a sequence read the theory does fix are reported too.  That is
   the safe direction and it is not free -- see below.  The one exception, when
   [seq_read_range_guard] is on, is a formula whose only open symbol is a
   sequence read and each of whose reads the formula itself puts in range
   ([settle_in_range_seq_reads]); anything the syntactic test cannot show stays
   reported.

   What is NOT here, with the reason: [seq.extract] is total (SMT-LIB makes it
   empty for an offset or length outside the sequence), [seq.len] and
   [seq.++] are total, bit-vector division and remainder are total in SMT-LIB
   (division by zero is all-ones), and an array [select] is total.  A symbol
   added to the term language that is partial in its theory belongs in this
   list: leaving one out is a wrong [unsat], which is how a sequence read got
   here -- eight clauses whose solution is [P(x,k) := x <> 0] answered
   [unsat,0] because a guard over [seq.nth] of the empty sequence was read as
   false rather than as false-in-some-model.

   "Wrong constructor" is the operative word for a selector, and a datatype
   with a single constructor has none: every value of it is that constructor
   applied to its selectors ([v = C (s1 v, ..., sn v)]), so each selector is
   total and its value is fixed by the theory.  Tuples, records and
   reference-like wrappers are all of that shape, and reporting their
   projections as interpretation-dependent is not free: the caller then asks
   whether the *universal closure* is satisfiable, a quantified query that Z3
   answers "unknown" on as soon as arrays are involved and may not answer at
   all -- turning a decided [unsat] into [unknown] or a hang. *)
(* Whether a sequence read proved in range by its own formula counts as fixed.
   A process-wide setting rather than a parameter, because the function is
   called from the preprocessor, the resolver, the qualifier generator, the
   labeler and example construction, none of which carries a configuration the
   others see.  It is set by a solver's construction, before any solving domain
   exists, and only ever from [false] to [true]; an [Atomic] keeps reads from
   parallel domains well defined. *)
let seq_read_range_guard = Atomic.make false
let enable_seq_read_range_guard () = Atomic.set seq_read_range_guard true

(* An integer term as a linear form: the non-arithmetic subterms it is built
   from with their coefficients, and a constant.  A length [seq.len s] is keyed
   by [s], so two occurrences of one length compare equal whatever their
   annotations; any other subterm is an opaque atom compared structurally, and
   a structural mismatch between two spellings of one term only loses a match,
   never invents one. *)
type lin_key = Len of Term.t | Opaque of Term.t

let rec linear_of = function
  | Term.FunApp (T_int.Int n, [], _) -> ([], Q.of_bigint n)
  | Term.FunApp (T_int.Add, [ t1; t2 ], _) ->
      lin_add (linear_of t1) (linear_of t2)
  | Term.FunApp (T_int.Sub, [ t1; t2 ], _) ->
      lin_add (linear_of t1) (lin_scale Q.minus_one @@ linear_of t2)
  | Term.FunApp (T_int.Neg, [ t ], _) -> lin_scale Q.minus_one @@ linear_of t
  | Term.FunApp (T_int.Mul, [ Term.FunApp (T_int.Int n, [], _); t ], _)
  | Term.FunApp (T_int.Mul, [ t; Term.FunApp (T_int.Int n, [], _) ], _) ->
      lin_scale (Q.of_bigint n) @@ linear_of t
  | Term.FunApp (T_seq.SqLen _, [ s ], _) -> ([ (Len s, Q.one) ], Q.zero)
  | t -> ([ (Opaque t, Q.one) ], Q.zero)

and lin_scale k (m, c) =
  if Q.equal k Q.zero then ([], Q.zero)
  else (List.map m ~f:(fun (x, a) -> (x, Q.mul k a)), Q.mul k c)

and lin_add (m1, c1) (m2, c2) =
  let m =
    List.fold m2 ~init:m1 ~f:(fun acc (x, a) ->
        match List.Assoc.find acc x ~equal:Stdlib.( = ) with
        | Some b -> List.Assoc.add acc x (Q.add a b) ~equal:Stdlib.( = )
        | None -> (x, a) :: acc)
  in
  (List.filter m ~f:(fun (_, a) -> not (Q.equal a Q.zero)), Q.add c1 c2)

(* A disjunct as [L >= 0] over the integers, when it is a comparison of two
   integer terms or the negation of one; [None] for anything else.  Strict
   comparisons become non-strict by the integer step, which is exact. *)
let nonneg_form_of phi =
  let of_psym neg psym t1 t2 =
    let diff a b =
      lin_add (linear_of a) (lin_scale Q.minus_one @@ linear_of b)
    in
    let minus_one (m, c) = (m, Q.sub c Q.one) in
    match (neg, psym) with
    | false, T_int.Leq | true, T_int.Gt -> Some (diff t2 t1)
    | false, T_int.Geq | true, T_int.Lt -> Some (diff t1 t2)
    | false, T_int.Lt | true, T_int.Geq -> Some (minus_one @@ diff t2 t1)
    | false, T_int.Gt | true, T_int.Leq -> Some (minus_one @@ diff t1 t2)
    | _ -> None
  in
  match phi with
  | Formula.Atom (Atom.App (Predicate.Psym psym, [ t1; t2 ], _), _) ->
      of_psym false psym t1 t2
  | Formula.UnaryOp
      ( Formula.Not,
        Formula.Atom (Atom.App (Predicate.Psym psym, [ t1; t2 ], _), _),
        _ ) ->
      of_psym true psym t1 t2
  | _ -> None

(* Does [target >= 0] imply [d >= 0]?  Only the certificate [d = k * target + c]
   with [k > 0] and [c >= 0] is looked for; a [false] answer may be wrong, a
   [true] one may not. *)
let lin_implies (mt, ct) (md, cd) =
  match mt with
  | [] -> Q.(lt ct zero) (* the target never holds *)
  | (x, a) :: _ -> (
      match List.Assoc.find md x ~equal:Stdlib.( = ) with
      | None -> false
      | Some b ->
          let k = Q.div b a in
          Q.(gt k zero)
          && List.length md = List.length mt
          && List.for_all mt ~f:(fun (y, a') ->
              match List.Assoc.find md y ~equal:Stdlib.( = ) with
              | Some b' -> Q.equal b' (Q.mul k a')
              | None -> false)
          && Q.(geq (sub cd (mul k ct)) zero))

(* [phi] with every sequence read whose range [phi] itself settles replaced by
   a placeholder.  A read [seq.nth s j] is settled when [phi] has a top-level
   disjunct implied by [j < 0] and one implied by [j >= seq.len s] (or when the
   index is a literal inside a sequence of syntactic length).  Then wherever the
   read is out of range, one of those disjuncts holds and so does [phi], whatever
   the read denotes; wherever it is in range the theory fixes its value.  The
   guards mention only [j] and [s], which are proper subterms of the read, so
   the argument goes through by induction on the reads' nesting: the smallest
   read out of range in one model has the same index and sequence in every
   model, hence is out of range in every model and makes [phi] true in each.

   Reads under a binder are not visited, since a disjunct outside the binder is
   about a different variable of the same name; they stay and are reported.  A
   read whose index or sequence contains another read is compared after that
   inner read has been replaced, so it cannot match a guard written over the
   original, and stays too.  Both are losses in the safe direction. *)
let settle_in_range_seq_reads phi =
  let guards =
    List.filter_map (Formula.disjuncts_list_of phi) ~f:nonneg_form_of
  in
  let implied target = List.exists guards ~f:(lin_implies target) in
  Formula.map_term_no_binders phi ~f:(function
    | Term.FunApp (T_seq.SqNth se, [ s; j ], _) as t ->
        let in_range =
          Option.is_some (Evaluator.seq_index_in_range s j)
          ||
          let lj = linear_of j in
          implied (lin_add (lin_scale Q.minus_one lj) ([], Q.minus_one))
          && implied
               (lin_add lj
                  (lin_scale Q.minus_one @@ linear_of (T_seq.mk_len se s)))
        in
        if in_range then Term.mk_var (Ident.Tvar "#seq_read_in_range") se else t
    | t -> t)

let interpretation_dependent phi =
  let is_seq_read = function T_seq.SqNth _ -> true | _ -> false in
  let open_symbol = function
    | T_dt.DTSel (_, dt, _) -> (
        (* [Datatype.conses_of] raises on a datatype that does not name itself
           (an uninterpreted one); such a selector stays interpretation-dependent *)
        match Datatype.look_up_dt dt @@ Datatype.name_of dt with
        | Some dt -> List.length (Datatype.conses_of_dt dt) > 1
        | None -> true)
    (* Exponentiation is not in the SMT-LIB integer or real theory at all, and
       the solvers do not agree about it: z3 leaves `0 ^ 0` unconstrained --
       it answers `sat` both to `0 ^ 0 = 1` and to its negation, for the
       integer and the real operator alike -- while cvc5 fixes it at 1.  So a
       formula mentioning it can be false in one model and true in another,
       exactly like a division by zero, and "invalid" may not be read as
       "false".  The test is by symbol rather than by the base being provably
       non-zero, which would be tighter: the tighter test needs a traversal
       that does not enter an array lambda, so it could miss an occurrence and
       report a formula as fixed when it is not, which is the direction that
       produces wrong answers rather than lost ones. *)
    | FVar _ | T_int.Div _ | T_int.Rem _ | T_real.RDiv | T_seq.SqNth _
    | T_int.Power | T_real.RPower ->
        true
    | _ -> false
  in
  let fsyms = Formula.funsyms_of phi in
  if not (Set.exists fsyms ~f:open_symbol) then false
  else if
    Atomic.get seq_read_range_guard
    && Set.for_all fsyms ~f:(fun f -> is_seq_read f || not (open_symbol f))
  then
    (* the only open symbol is a sequence read: report the formula only if a
       read survives that the formula does not itself put in range *)
    Set.exists ~f:is_seq_read @@ Formula.funsyms_of
    @@ settle_in_range_seq_reads phi
  else true

(* A clause holds when it holds in every model of the background theory, so
   the question about a disjunct is validity and not satisfiability.

   [separate] splits the disjuncts into [phis1], whose variables are disjoint
   from those of the predicate applications and of [phis2], and the rest.
   Because the two variable groups are disjoint, [forall xs. (A(ys) \/ B(zs))]
   is [(forall ys. A) \/ (forall zs. B)], so the clause is equivalent to
   "[forall ys. phi1] holds, or the rest does" -- in each model separately.
   Hence:

   - the clause may be dropped when [phi1] is valid, since then
     [forall ys. phi1] is true in every model;
   - [phi1] may be dropped when [forall ys. phi1] is false in *every* model,
     which is [check_sat_forall (forall ys. phi1) = `Unsat];
   - otherwise both must stay.  Dropping [phi1] merely because it is invalid
     demands the rest of the clause in the models where [phi1] does hold,
     which is strictly stronger than the clause and once produced a wrong
     [unsat].

   For a formula over interpreted symbols only, [`Invalid] already means
   [forall ys. phi1] is false -- one model, one truth value -- so the extra
   query is issued only for a formula with a term the theory leaves open, and
   the Z3 query sequence on interpreted problems is unchanged.  An undecided
   check (Z3 timeout/unknown, e.g. on arrays or datatypes) keeps every
   disjunct. *)
let simplify ?(check_sat_forall = fun _ -> `Unknown) unknowns check_valid
    (senv, pos, neg, phi) =
  let phi = Evaluator.simplify phi in
  let phis =
    Set.Poly.map (Formula.disjuncts_of phi) ~f:(fun phi ->
        (Formula.fvs_of phi, phi))
  in
  if Set.are_disjoint pos neg then
    let fvs_phi = Set.concat_map ~f:fst phis in
    if Set.are_disjoint fvs_phi unknowns then
      let fvs_pos_neg = Set.concat_map (Set.union pos neg) ~f:Atom.fvs_of in
      let phis1, phis2 = separate fvs_pos_neg phis in
      let or_of phis =
        Formula.or_of @@ Set.to_list (Set.Poly.map ~f:snd phis)
      in
      let phi1 = or_of phis1 in
      let keep_all () = Some (senv, pos, neg, or_of (Set.union phis1 phis2)) in
      match check_valid phi1 with
      | `Valid -> None
      | `Invalid -> (
          if not (interpretation_dependent phi1) then
            Some (senv, pos, neg, or_of phis2)
          else
            let bounds =
              Set.to_list
              @@ Set.filter (Formula.term_sort_env_of phi1) ~f:(fun (x, _) ->
                  not (Set.mem unknowns x))
            in
            match check_sat_forall (Formula.forall bounds phi1) with
            | `Unsat -> Some (senv, pos, neg, or_of phis2)
            | `Sat | `Unknown -> keep_all ())
      | `Unknown -> keep_all ()
    else Some (senv, pos, neg, phi)
  else None

let resolve_one_step mode (papp : Atom.t) (c_pos, c_neg, c_pure) =
  let open Option in
  Set.Poly.filter_map ~f:(fun papp' ->
      Atom.unify Set.Poly.empty (*ToDo: is it OK with function varibles?*) papp'
        papp
      >>= fun theta ->
      let c_pos' =
        Set.Poly.map ~f:(Atom.subst theta >> Normalizer.normalize_atom)
        @@ if Stdlib.(mode = `Backward) then Set.remove c_pos papp' else c_pos
      in
      let c_neg' =
        Set.Poly.map ~f:(Atom.subst theta >> Normalizer.normalize_atom)
        @@ if Stdlib.(mode = `Forward) then Set.remove c_neg papp' else c_neg
      in
      let c_pure' = Evaluator.simplify @@ Formula.subst theta c_pure in
      Some (c_pos', c_neg', c_pure'))
  @@ if Stdlib.(mode = `Forward) then c_neg else c_pos

(* val resolve: Atom.t Set.Poly.t -> Atom.t Set.Poly.t -> t -> t Set.Poly.t *)
let resolve_one_step_all positive negative c =
  let cs_b =
    Set.Poly.map negative ~f:(fun neg -> resolve_one_step `Backward neg c)
  in
  let cs_f =
    Set.Poly.map positive ~f:(fun pos -> resolve_one_step `Forward pos c)
  in
  Set.union cs_b cs_f |> Set.concat
  |> Set.filter ~f:(trd3 >> Stdlib.( <> ) (Formula.mk_true ()))

let has_only_pure (pos, neg, _) = Set.is_empty pos && Set.is_empty neg

let is_query wfpvs fnpvs (pos, _, _) =
  Set.for_all pos ~f:(fun atm ->
      Atom.is_pvar_app atm
      &&
      let p = Atom.pvar_of atm in
      Set.mem wfpvs p || Set.mem fnpvs p)

let is_initializer (pos, _, _) = Set.is_empty pos

(*val refresh_tvar: (Atom.t list * Atom.t list * t) -> (Atom.t list * Atom.t list * t)*)
let refresh_tvar (senv, ps, ns, phi) =
  (*let map =
    (Formula.fvs_of phi ::
     ((ps |> Set.to_list |> List.map ~f:Atom.fvs_of) @
      (ns |> Set.to_list |> List.map ~f:Atom.fvs_of)))
    |> Set.Poly.union_list
    |> Set.Poly.map ~f:(fun x -> x, Ident.mk_fresh_tvar ())
    |> Map.of_set_exn
    in*)
  let map =
    Map.Poly.of_alist_exn @@ Map.Poly.to_alist
    @@ Map.Poly.map senv ~f:(fun _ -> Ident.mk_fresh_tvar ())
  in
  ( Map.rename_keys_map map senv,
    Set.Poly.map ~f:(Atom.rename map) ps,
    Set.Poly.map ~f:(Atom.rename map) ns,
    Formula.rename map phi )

let refresh_pvar_args ((senv, ps, ns, phi) : t) =
  let ps', pres =
    Set.unzip
    @@ Set.Poly.map ps ~f:(fun atm ->
        let pvar, sorts, args, info = Atom.let_pvar_app atm in
        let env = mk_fresh_sort_env_list sorts in
        let args' = Term.of_sort_env env in
        ( Atom.pvar_app_of_senv ~info pvar env,
          (env, List.map2_exn args args' ~f:Formula.neq) ))
  in
  let xss1, pneqss = Set.unzip pres in
  let ns', nres =
    Set.unzip
    @@ Set.Poly.map ns ~f:(fun atm ->
        let pvar, sorts, args, info = Atom.let_pvar_app atm in
        let env = mk_fresh_sort_env_list sorts in
        let args' = Term.of_sort_env env in
        ( Atom.pvar_app_of_senv ~info pvar env,
          (env, List.map2_exn args args' ~f:Formula.neq) ))
  in
  let xss2, nneqss = Set.unzip nres in
  let senv' =
    Map.force_merge senv @@ Map.of_set_exn @@ Logic.of_old_sort_env_set
    @@ Set.concat_map ~f:Set.Poly.of_list (Set.union xss1 xss2)
  in
  ( senv',
    ps',
    ns',
    Formula.or_of
    @@ (phi :: List.concat (Set.to_list pneqss))
    @ List.concat (Set.to_list nneqss) )

let tvs_of ((_senv, ps, ns, phi) : t) =
  Set.union (Formula.tvs_of phi)
  @@ Set.concat_map (Set.union ps ns) ~f:Atom.tvs_of

let fvs_of ((_senv, ps, ns, phi) : t) =
  Set.union (Formula.fvs_of phi)
  @@ Set.concat_map (Set.union ps ns) ~f:Atom.fvs_of

let reduce_sort_map ((senv, ps, ns, phi) : t) =
  let fvs = Set.inter (Map.key_set senv) (fvs_of (senv, ps, ns, phi)) in
  ( Map.of_set_exn
    @@ Set.Poly.map fvs ~f:(fun x -> (x, Map.Poly.find_exn senv x)),
    ps,
    ns,
    phi )

(* Tables keyed by physical identity: a value found is the very value
   stored, so whatever was computed from it applies unchanged.  The hash is
   the address ([Common.Ext.Hashtbl.phys_hash]) and only spreads the buckets
   (equality is [phys_equal]): [Hashtbl.hash] reads ten meaningful nodes,
   which on a formula over datatype sorts are spent inside the sorts, so the
   subformulas of a multiplied clausal form fell into a few buckets. *)
module PhysFormula = Stdlib.Hashtbl.Make (struct
  type t = Formula.t

  let equal = phys_equal
  let hash = Common.Ext.Hashtbl.phys_hash
end)

module PhysAtom = Stdlib.Hashtbl.Make (struct
  type t = Atom.t

  let equal = phys_equal
  let hash = Common.Ext.Hashtbl.phys_hash
end)

(* [reduce_sort_map] for many clauses that share subformulas: the returned
   function gives what [reduce_sort_map] gives on every clause, and keeps,
   for as long as it is held, the free variables of every atom and of every
   maximal non-disjunction subformula of a pure part it has met, by physical
   identity.  Exact: [Formula.fvs_of] of a disjunction is the union of its two
   sides' (both its term and its predicate variables are unions there), and a
   value met again physically is the value whose variables were computed.
   Why: the conjunctive normal form multiplies the alternatives of a
   disjunction of conjunctions, so thousands of clauses can carry the same
   large pure disjuncts as physically shared leaves under freshly built
   disjunctions, and [reduce_sort_map] recomputed their free variables once
   per clause. *)
let reduce_sort_map_shared () =
  let ft = PhysFormula.create 256 and at = PhysAtom.create 256 in
  let rec phi_fvs phi =
    match phi with
    | Formula.BinaryOp (Formula.Or, a, b, _) -> Set.union (phi_fvs a) (phi_fvs b)
    | _ -> (
        match PhysFormula.find_opt ft phi with
        | Some s -> s
        | None ->
            let s = Formula.fvs_of phi in
            PhysFormula.add ft phi s;
            s)
  in
  let atom_fvs a =
    match PhysAtom.find_opt at a with
    | Some s -> s
    | None ->
        let s = Atom.fvs_of a in
        PhysAtom.add at a s;
        s
  in
  fun ((senv, ps, ns, phi) : t) ->
    let fvs =
      Set.union (phi_fvs phi) @@ Set.concat_map (Set.union ps ns) ~f:atom_fvs
    in
    let fvs = Set.inter (Map.key_set senv) fvs in
    ( Map.of_set_exn
      @@ Set.Poly.map fvs ~f:(fun x -> (x, Map.Poly.find_exn senv x)),
      ps,
      ns,
      phi )

let to_formula (senv, ps, ns, phi) =
  ( senv,
    Formula.or_of
    @@ phi
       :: (Set.to_list
          @@ Set.union
               (Set.Poly.map ps ~f:Formula.mk_atom)
               (Set.Poly.map ns ~f:(Formula.mk_atom >> Formula.mk_neg))) )

let str_of cls = Formula.str_of @@ snd @@ to_formula cls

let subst_aux sub atoms phi is_pos : Atom.t Set.Poly.t * Formula.t * bool =
  Set.fold atoms ~init:(Set.Poly.empty, phi, false)
    ~f:(fun (atoms, phi, changed) -> function
    | Atom.App (Predicate.Var (pvar, _), _, _) as atom -> (
        match Map.Poly.find sub pvar with
        | None -> (Set.add atoms atom, phi, changed)
        | Some (params, phi_pos, phi_neg, keep) ->
            let psub =
              Map.Poly.singleton pvar
                (params, if is_pos then phi_pos else phi_neg)
            in
            ( (if keep then Set.add atoms atom else atoms),
              Formula.mk_or phi @@ Atom.subst_preds psub atom,
              true ))
    | _ -> failwith "Invalid pattern of Atom")

let subst_preds psub (senv, ps, ns, phi) =
  let ps', phi, changed1 = subst_aux psub ps phi true in
  let ns', phi, changed2 = subst_aux psub ns phi false in
  ((senv, ps', ns', phi), changed1 || changed2)

(* Condensation of a clause: drop a literal that is an instance-generalisation
   of another literal of the same polarity.

   [match_private priv sub pat t] extends [sub] to a substitution for the
   variables in [priv] under which [pat] is syntactically [t] -- with
   [condense_up_to_linear] set, up to integer subterms whose difference
   normalises to the linear term [0]; every other
   variable, symbol and sort must agree exactly, and a variable in [priv] is
   bound only to a term of its own sort.  A subterm under a binder (an
   embedded formula, an array lambda, a [let]) is matched only when it
   mentions no variable of [priv], and then only by syntactic equality, so the
   answer is conservative: [Some] only when [pat] really becomes [t]. *)
(* Whether [match_private] (so [condense]) compares integer subterms up to
   their linear normal form and descends into constructor applications that
   mention no private variable.  Off by default: subterms without a private
   variable then match only when syntactically equal.  Either way a match is
   an instance relation that holds in every model, so condensation stays
   exact.  Process-wide; the PCSat preprocessor sets it from its
   configuration when a solve starts. *)
let condense_up_to_linear = ref false

let match_private priv sub pat t =
  let same a b = try Stdlib.(a = b) with Invalid_argument _ -> false in
  let sort_of t =
    try Some (Term.sort_of t)
    with e when not (Common.Timer.is_async e) -> None
  in
  (* Two integer terms whose difference has the linear normal form [0] are
     equal in every model, whatever their spelling.  Substitutions during
     predicate elimination produce both [-1 + x] and [-(1 - x)] for one value;
     with syntactic equality only, an argument spelled each way kept a premise
     copy from being dropped, so a one-premise step clause stayed a
     two-premise one.  A term the normaliser does not support is compared
     syntactically only, which is the conservative answer. *)
  let equal_int a b =
    !condense_up_to_linear
    &&
    match (sort_of a, sort_of b) with
    | Some T_int.SInt, Some T_int.SInt -> (
        try
          Map.Poly.for_all
            (Normalizer.linear_int_monomials_of (Value.Int Z.one)
               (T_int.mk_sub a b))
            ~f:(function Value.Int c -> Z.equal c Z.zero | _ -> false)
        with e when not (Common.Timer.is_async e) -> false)
    | _ -> false
  in
  let rec go sub pat t =
    let closed = Set.are_disjoint (Term.tvs_of pat) priv in
    if closed && (same pat t || equal_int pat t) then Some sub
    else if closed && not !condense_up_to_linear then None
    else
      (* with the switch set, a constructor application is descended into
         whether or not it mentions a private variable, so that an integer
         field spelled differently inside it is still compared up to its
         normal form *)
      match (pat, t) with
      | Term.Var (x, s, _), _ when Set.mem priv x -> (
          match Map.Poly.find sub x with
          | Some t' -> if same t' t || equal_int t' t then Some sub else None
          | None -> (
              match sort_of t with
              | Some s' when same s s' -> Some (Map.Poly.set sub ~key:x ~data:t)
              | _ -> None))
      | Term.FunApp (f1, a1, _), Term.FunApp (f2, a2, _) -> (
          match f1 with
          | T_bool.Formula _ | T_array.ALambda _ -> None
          | _ ->
              if same f1 f2 && List.length a1 = List.length a2 then
                List.fold2_exn a1 a2 ~init:(Some sub) ~f:(fun acc p u ->
                    Option.bind acc ~f:(fun sub -> go sub p u))
              else None)
      | _ -> None
  in
  go sub pat t

let match_private_atom priv pat t =
  match (pat, t) with
  | ( Atom.App (Predicate.Var (p1, s1), a1, _),
      Atom.App (Predicate.Var (p2, s2), a2, _) )
    when Ident.pvar_equal p1 p2
         && (try Stdlib.(s1 = s2) with Invalid_argument _ -> false)
         && List.length a1 = List.length a2 ->
      List.fold2_exn a1 a2 ~init:(Some Map.Poly.empty) ~f:(fun acc p u ->
          Option.bind acc ~f:(fun sub -> match_private priv sub p u))
  | _ -> None

(* [condense ~unknowns (ps, ns, phi)] removes, one at a time until none is
   left, a literal [L2] (a head atom in [ps] or a premise in [ns]) for which
   another literal [L1] OF THE SAME POLARITY is [L2 sigma], where [sigma]
   substitutes only variables that occur in [L2] and nowhere else in the
   clause -- not in [L1], not in any other atom, not in [phi] -- and are not
   unknowns (the keys of [unknowns]: predicate and function variables being
   solved for, which are not universally quantified by the clause).

   Why this is exact.  Read the clause as the universal closure of the
   disjunction [L1 \/ L2 \/ R], where [R] is every other literal and [phi].
   Let [v'] be the variables private to [L2].  Since [v'] occurs nowhere but
   in [L2], the quantifier moves inward:
     [forall v v'. (L1 \/ L2 \/ R)]  =  [forall v. (L1 \/ R \/ forall v'. L2)].
   [forall v'. L2] implies its instance [L2 sigma = L1], so the disjunction
   [L1 \/ forall v'. L2] is just [L1], and the clause equals
   [forall v. (L1 \/ R)].  This holds in every model and for every
   interpretation of the unknowns, so it is an equivalence of the clause and
   not only of the system -- no solution or refutation is gained or lost, and
   no predicate kind is affected.  Nothing in the argument depends on the
   polarity, so it holds for a premise (a negative literal: the copy asserts
   only that SOME instance of the premise holds, which [L1] witnesses) and for
   a head atom (a positive literal: the copy is a disjunct demanding the atom
   at EVERY value of its private variables, which implies the kept one) alike.
   A literal is never matched against one of the opposite polarity, because
   then [L2 sigma] would be the complement of [L1] and the step would not
   apply.

   What it does not do: it never removes the last occurrence of a predicate
   from the clause (the kept [L1] is an atom of the same predicate), never
   touches [phi], and never binds a variable that the rest of the clause reads.
   Preserves: [phi] and every literal not removed. *)
let condense ~unknowns (ps, ns, phi) =
  let condense_side side other =
    let rec loop side =
      let found =
        Set.find side ~f:(fun n ->
            let rest = Set.remove side n in
            let others =
              Set.Poly.union_list
                [
                  Formula.fvs_of phi;
                  Set.concat_map other ~f:Atom.fvs_of;
                  Set.concat_map rest ~f:Atom.fvs_of;
                ]
            in
            let priv =
              Set.filter (Atom.tvs_of n) ~f:(fun x ->
                  (not (Set.mem others x)) && not (Set.mem unknowns x))
            in
            (not (Set.is_empty priv))
            && Set.exists rest ~f:(fun m ->
                Option.is_some (match_private_atom priv n m)))
      in
      match found with Some n -> loop (Set.remove side n) | None -> side
    in
    loop side
  in
  let ns = condense_side ns ps in
  let ps = condense_side ps ns in
  (ps, ns, phi)

(* [merge_int_var_equations ~unknowns (ps, ns, phi)] removes a disjunct of
   [phi] that says two distinct integer variables differ -- [x != y], or any
   atom whose two sides differ by the linear term [x - y], such as
   [0 != y - x] -- and replaces [y] by [x] everywhere in the clause, until no
   such disjunct is left.  [phi] is read as the pure part of the clause
   [ps \/ not ns \/ phi]; the variables are its universally quantified ones,
   so an unknown (a key of [unknowns]) is never replaced.

   Exact for the universal closure, in every model:
   [forall x y. (x != y \/ C(x, y))] is [forall x. C(x, x)].  Only a renaming
   of one variable into another is made, never a variable into a compound
   term, so no argument of an unknown becomes an arithmetic term it was not
   already.  What it is for: an equation that the normal form writes as
   [0 != x - y] is not a definition [x != t] to the rules that substitute
   those, so the two names survive, and a premise copy that differs from the
   kept premise only by that renaming is not dropped by [condense]. *)
let merge_int_var_equations ~unknowns (ps, ns, phi) =
  let var_pair = function
    | Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _) -> (
        try
          if not (Term.is_int_sort (Term.sort_of t1)) then None
          else
            let monos =
              Normalizer.linear_int_monomials_of (Value.Int Z.one)
                (T_int.mk_sub t1 t2)
            in
            let monos =
              Map.Poly.filter monos ~f:(function
                | Value.Int c -> not (Z.equal c Z.zero)
                | _ -> true)
            in
            match Map.Poly.to_alist monos with
            | [
             (Some (Term.Var (x, _, _)), Value.Int c1);
             (Some (Term.Var (y, _, _)), Value.Int c2);
            ]
              when Z.equal (Z.add c1 c2) Z.zero
                   && Z.equal (Z.abs c1) Z.one
                   && (not (Ident.tvar_equal x y))
                   && (not (Set.mem unknowns x))
                   && not (Set.mem unknowns y) ->
                Some (x, y)
            | _ -> None
        with e when not (Common.Timer.is_async e) -> None)
    | _ -> None
  in
  let rec loop (ps, ns, phi) =
    let ds = Formula.disjuncts_list_of phi in
    match
      List.find_mapi ds ~f:(fun k d ->
          match d with
          | Formula.Atom (atm, _) -> Option.map (var_pair atm) ~f:(fun p -> (k, p))
          | Formula.UnaryOp
              ( Formula.Not,
                Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, ts, _), _),
                _ ) ->
              Option.map
                (match ts with [ t1; t2 ] -> var_pair (T_bool.mk_neq t1 t2) | _ -> None)
                ~f:(fun p -> (k, p))
          | _ -> None)
    with
    | None -> (ps, ns, phi)
    | Some (k, (x, y)) ->
        let sub = Map.Poly.singleton y (Term.mk_var x T_int.SInt) in
        let phi =
          Formula.or_of
          @@ List.filter_mapi ds ~f:(fun k' d ->
              if k = k' then None else Some (Formula.subst sub d))
        in
        loop
          ( Set.Poly.map ps ~f:(Atom.subst sub),
            Set.Poly.map ns ~f:(Atom.subst sub),
            phi )
  in
  loop (ps, ns, phi)

(* [joint_match_atom ~unknowns (sigma, fixed) pat t] extends a substitution
   [sigma] of variables to variables, with [fixed] the variables decided to be
   mapped to themselves (which include every variable of [sigma]'s range), so
   that [pat sigma] is [t]: [Some] the extension, or [None].  A variable that
   is an unknown (a key of [unknowns]) is never bound, and a subterm carrying
   a binder ([T_bool.Formula], [T_array.ALambda], a [let]) or anything but a
   variable or a function application is matched only syntactically, with its
   variables fixed.  Invariant kept: no variable is both a key of [sigma] and
   in [fixed]; every value of [sigma] is in [fixed]. *)
let joint_match_atom ~unknowns (sigma, fixed) pat t =
  let same a b = try Stdlib.(a = b) with Invalid_argument _ -> false in
  let fix_all st vs =
    Set.fold vs ~init:(Some st) ~f:(fun acc x ->
        Option.bind acc ~f:(fun (sigma, fixed) ->
            if Map.Poly.mem sigma x then None
            else Some (sigma, Set.add fixed x)))
  in
  let rec go ((sigma, fixed) as st) pat t =
    match (pat, t) with
    | Term.Var (x, s, _), _ when not (Set.mem unknowns x) -> (
        match Map.Poly.find sigma x with
        | Some y -> (
            match t with
            | Term.Var (y', _, _) when Ident.tvar_equal y y' -> Some st
            | _ -> None)
        | None -> (
            match t with
            | Term.Var (y, s', _) when same s s' ->
                if Ident.tvar_equal x y then Some (sigma, Set.add fixed x)
                else if Set.mem fixed x || Map.Poly.mem sigma y then None
                else Some (Map.Poly.set sigma ~key:x ~data:y, Set.add fixed y)
            | _ -> None))
    | Term.FunApp (f1, a1, _), Term.FunApp (f2, a2, _) -> (
        match f1 with
        | T_bool.Formula _ | T_array.ALambda _ ->
            if same pat t then fix_all st (Term.tvs_of pat) else None
        | _ ->
            if same f1 f2 && List.length a1 = List.length a2 then
              List.fold2_exn a1 a2 ~init:(Some st) ~f:(fun acc p u ->
                  Option.bind acc ~f:(fun st -> go st p u))
            else None)
    | _ -> if same pat t then fix_all st (Term.tvs_of pat) else None
  in
  match (pat, t) with
  | ( Atom.App (Predicate.Var (p1, s1), a1, _),
      Atom.App (Predicate.Var (p2, s2), a2, _) )
    when Ident.pvar_equal p1 p2 && same s1 s2
         && List.length a1 = List.length a2 ->
      List.fold2_exn a1 a2 ~init:(Some (sigma, fixed)) ~f:(fun acc p u ->
          Option.bind acc ~f:(fun st -> go st p u))
  | _ -> None

(* [joint_atom_seeds ~unknowns ~max_seeds ~f ps ns] calls [f] on candidate
   seeds of a joint condensation, in order, and returns the first [Some] it
   answers ([None] when none does).  A seed is [(dps, dns, binds, fixed)], a set of head atoms
   [dps] of [ps] and premises [dns] of [ns] to drop, and a substitution of
   variables to variables ([binds]; [fixed] the variables it maps to
   themselves, its range included) such that
   - every dropped atom becomes, under [binds], an atom of its own polarity
     that is not dropped;
   - no atom that is not dropped mentions a variable of [binds]' domain, no
     domain variable is in [fixed] or an unknown.
   A seed starts from a pair of atoms of one predicate and polarity, the first
   matched onto the second, and closes over every other atom that mentions a
   bound variable, each matched onto a kept atom of its predicate and
   polarity, tried in order with backtracking; an atom whose variables share
   a disjunct of [pure] (the variable sets of the pure part's disjuncts) with
   a bound variable is tried dropped, then kept.  Every complete closure that
   passes the two conditions above is handed to [f], and the search goes on
   while [f] answers [None], so the search's choices and its bound of
   [closure_steps] atom matches per seed affect only which seeds are found,
   never what a seed claims.  At most [max_seeds] pairs are tried.

   [doomed (sigma, fixed)] is asked of every partial closure before it is
   extended; when it answers [true] the closures extending it are not
   enumerated.  It must answer [true] only when [f] would answer [None] for
   every complete closure extending the partial one (bindings and fixed
   variables only grow along a closure). *)
(* [COAR_JOINT_TRACE] (instrument only): at most [COAR_JOINT_TRACE] lines
   (default 200) on stderr saying why each joint seed failed *)
let joint_trace_left =
  lazy
    (ref
       (match Stdlib.Sys.getenv_opt "COAR_JOINT_TRACE" with
       | None -> 0
       | Some n -> Option.value ~default:200 (int_of_string_opt n)))

let joint_trace msg =
  let left = Lazy.force joint_trace_left in
  if !left > 0 then (
    decr left;
    eprintf "[joint] %s\n%!" (msg ()))

let joint_atom_seeds ~unknowns ~max_seeds ?(closure_steps = 2_000) ?(pure = [])
    ?(doomed = fun _ -> false) ~f ps ns =
  let same a b = try Stdlib.(a = b) with Invalid_argument _ -> false in
  let lits =
    List.map (Set.to_list ps) ~f:(fun a -> (true, a))
    @ List.map (Set.to_list ns) ~f:(fun a -> (false, a))
  in
  let lits = Array.of_list lits in
  let nl = Array.length lits in
  let pred_of = function
    | Atom.App (Predicate.Var (p, _), _, _) -> Some (Ident.name_of_pvar p)
    | _ -> None
  in
  let key i =
    let pos, a = lits.(i) in
    Option.map (pred_of a) ~f:(fun p -> (pos, p))
  in
  let keys = Array.init nl ~f:key in
  let tvs = Array.map lits ~f:(fun (_, a) -> Atom.tvs_of a) in
  let same_key i j =
    match (keys.(i), keys.(j)) with
    | Some k1, Some k2 -> Stdlib.(k1 = k2)
    | _ -> false
  in
  let verify (dropped, (sigma, fixed)) =
    let kept =
      List.filter (List.init nl ~f:Fn.id) ~f:(fun k -> not (Set.mem dropped k))
    in
    let sub_atom a =
      let m =
        Set.fold (Atom.term_sort_env_of a) ~init:Map.Poly.empty
          ~f:(fun acc (x, s) ->
            match Map.Poly.find sigma x with
            | Some y -> Map.Poly.set acc ~key:x ~data:(Term.mk_var y s)
            | None -> acc)
      in
      Atom.subst m a
    in
    (not (Map.Poly.is_empty sigma))
    && (not
          (Map.Poly.existsi sigma ~f:(fun ~key ~data:_ ->
               Set.mem fixed key || Set.mem unknowns key)))
    && List.for_all kept ~f:(fun k ->
           not (Set.exists tvs.(k) ~f:(fun x -> Map.Poly.mem sigma x)))
    && Set.for_all dropped ~f:(fun k ->
           let pos, a = lits.(k) in
           let a' = sub_atom a in
           List.exists kept ~f:(fun j ->
               let pos', b = lits.(j) in
               Bool.(pos = pos') && same a' b))
  in
  let to_seed (dropped, (sigma, fixed)) =
    let pick pos =
      Set.Poly.of_list
        (List.filter_map (Set.to_list dropped) ~f:(fun k ->
             if Bool.(fst lits.(k) = pos) then Some (snd lits.(k)) else None))
    in
    (pick true, pick false, Map.Poly.to_alist sigma, Set.to_list fixed)
  in
  (* [linked k sigma fixed]: atom [k] has a variable that is neither bound
     nor fixed and shares a disjunct of the pure part with a bound variable.
     Such an atom is not forced into the closure, but if it stays, that
     variable stays read by an atom and the disjunct's image keeps it: a copy
     of a callee precondition applied at a copied argument that a linking
     equation ties to the bound variables is only dropped together with the
     rest of its copy. *)
  let linked k (sigma, fixed) =
    let free = Set.filter tvs.(k) ~f:(fun x ->
        (not (Map.Poly.mem sigma x)) && not (Set.mem fixed x))
    in
    (not (Set.is_empty free))
    && List.exists pure ~f:(fun vs ->
           Set.exists vs ~f:(fun x -> Map.Poly.mem sigma x)
           && not (Set.are_disjoint vs free))
  in
  let steps = ref 0 in
  (* a depth-first search over the closures of the seed [i -> j]: an atom
     mentioning a bound variable must be dropped, onto a kept image of its
     predicate and polarity (each image tried in turn: the first that fits is
     not always the one the rest agrees with, a callee precondition applied
     at several arguments offering several of one shape); an atom [linked]
     to the bound variables is first tried dropped, then kept.  Each complete
     closure that passes [verify] is handed to [f], and the search goes on
     when [f] answers [None].  At most [closure_steps] atom matches per
     seed. *)
  let close i j =
    match
      joint_match_atom ~unknowns (Map.Poly.empty, Set.Poly.empty) (snd lits.(i))
        (snd lits.(j))
    with
    | None -> None
    | Some st ->
        steps := 0;
        let images c dropped st k =
          List.find_map (List.init nl ~f:Fn.id) ~f:(fun d ->
              if
                d = c || Set.mem dropped d || (not (same_key c d))
                || !steps >= closure_steps
              then None
              else (
                incr steps;
                match joint_match_atom ~unknowns st (snd lits.(c)) (snd lits.(d)) with
                | None -> None
                | Some st' -> k st'))
        in
        let rec loop dropped keep ((sigma, _) as st) =
          if doomed st then None else
          let dom_hit k =
            Set.exists tvs.(k) ~f:(fun x -> Map.Poly.mem sigma x)
          in
          let open_ k = (not (Set.mem dropped k)) && not (Set.mem keep k) in
          match List.find (List.init nl ~f:Fn.id) ~f:(fun k -> (not (Set.mem dropped k)) && dom_hit k) with
          | Some c -> (
              match images c dropped st (loop (Set.add dropped c) keep) with
              | Some _ as r -> r
              | None ->
                  joint_trace (fun () ->
                      sprintf "closure: no kept image for %s (seed %s -> %s)"
                        (Atom.str_of (snd lits.(c)))
                        (Atom.str_of (snd lits.(i)))
                        (Atom.str_of (snd lits.(j))));
                  None)
          | None -> (
              match
                List.find (List.init nl ~f:Fn.id) ~f:(fun k -> open_ k && linked k st)
              with
              | Some c -> (
                  match images c dropped st (loop (Set.add dropped c) keep) with
                  | Some _ as r -> r
                  | None -> loop dropped (Set.add keep c) st)
              | None ->
                  let r = (dropped, st) in
                  if verify r then f (to_seed r) else None)
        in
        loop (Int.Set.singleton i) Int.Set.empty st
  in
  let tried = ref 0 in
  let result = ref None in
  (try
     for i = 0 to nl - 1 do
       for j = 0 to nl - 1 do
         if i <> j && same_key i j && !tried < max_seeds then (
           incr tried;
           match close i j with
           | Some _ as r ->
               result := r;
               raise_notrace Exit
           | None -> ())
       done
     done
   with Exit -> ());
  !result

(* [condense_profile] (instrument only): where the last calls of
   [condense_pure] spent their time, accumulated until [condense_profile_reset].
   Phase 0 is the set-up (the input's own normal forms and the candidate
   tables), 1 the joint rounds, 2 the passes.  Per phase: normalisations and
   their seconds, [compute_incl] calls and their seconds, search calls; for the
   joint rounds also the seeds handed to the pure-part search, the seconds
   spent inside that hand-over, and the seconds of the whole rounds (the rest
   being the atom-closure enumeration of [joint_atom_seeds]).  Reading the
   clock changes no result. *)
type condense_profile = {
  nf_n : int array;
  nf_s : float array;
  incl_n : int array;
  incl_s : float array;
  search_n : int array;
  phase_s : float array;
  mutable seeds : int;
  mutable seeds_searched : int;
  mutable seed_f_s : float;
  mutable refused_budget : int;
  mutable refused_binds : int;
  mutable refused_ok : int;
  mutable refused_ok_shape : int;
}

let condense_profile =
  {
    nf_n = Array.create ~len:3 0;
    nf_s = Array.create ~len:3 0.;
    incl_n = Array.create ~len:3 0;
    incl_s = Array.create ~len:3 0.;
    search_n = Array.create ~len:3 0;
    phase_s = Array.create ~len:3 0.;
    seeds = 0;
    seeds_searched = 0;
    seed_f_s = 0.;
    refused_budget = 0;
    refused_binds = 0;
    refused_ok = 0;
    refused_ok_shape = 0;
  }

let condense_profile_reset () =
  let p = condense_profile in
  Array.fill p.nf_n ~pos:0 ~len:3 0;
  Array.fill p.nf_s ~pos:0 ~len:3 0.;
  Array.fill p.incl_n ~pos:0 ~len:3 0;
  Array.fill p.incl_s ~pos:0 ~len:3 0.;
  Array.fill p.search_n ~pos:0 ~len:3 0;
  Array.fill p.phase_s ~pos:0 ~len:3 0.;
  p.seeds <- 0;
  p.seeds_searched <- 0;
  p.seed_f_s <- 0.;
  p.refused_budget <- 0;
  p.refused_binds <- 0;
  p.refused_ok <- 0;
  p.refused_ok_shape <- 0

let condense_profile_str () =
  let p = condense_profile in
  let ph k name =
    sprintf "%s: %.2fs nf=%d/%.2fs incl=%d/%.2fs search=%d" name p.phase_s.(k)
      p.nf_n.(k) p.nf_s.(k) p.incl_n.(k) p.incl_s.(k) p.search_n.(k)
  in
  sprintf
    "%s | %s seeds=%d searched=%d in-f=%.2fs refused: budget=%d binds=%d ok=%d \
     (no same-shaped live disjunct=%d) | %s"
    (ph 0 "setup") (ph 1 "joint") p.seeds p.seeds_searched p.seed_f_s
    p.refused_budget p.refused_binds p.refused_ok p.refused_ok_shape (ph 2 "passes")

(* [condense_pure ~unknowns ?max_checks (ps, ns, phi)] is condensation of a
   clause (Joyner) applied to the literals of its pure part: it looks for a
   substitution [sigma] of variables to variables, defined on a set [D] of
   variables that occur in [phi] and in no atom of [ps] or [ns] and are not
   unknowns, with no variable of [D] in its range, under which every disjunct
   [l] of [phi] that mentions [D] becomes ([Evaluator.simplify] then
   [Normalizer.normalize], both meaning-preserving, compared syntactically) a
   disjunct of [phi] that does not mention [D]; it then drops every disjunct
   that mentions [D], and repeats until no such substitution is found.

   Why this is exact.  Write the clause as the universal closure of [R \/ T],
   where [T] is the disjuncts mentioning [D] and [R] everything else.
   Dropping [T] gives the closure of [R], which implies the clause.
   Conversely, the clause's variables are universally quantified, so it
   implies its instance [(R \/ T) sigma = R \/ T sigma] ([R] does not mention
   [D]), and every disjunct of [T sigma] is equivalent to one of [R], so the
   instance is [R].  So the two are equivalent in every model and for every
   interpretation of the unknowns.

   Why it is wanted.  Resolving away a predicate that some later premise is
   applied to inlines that predicate's definition once per occurrence, with
   fresh copies of the definition's private variables.  When a chain of
   definitions each mention all earlier ones (a straight-line program whose
   every step refines every earlier local), the same constraints arrive once
   directly and once through every later definition, and the pure part of
   each resolvent doubles with each predicate eliminated.  The copies differ
   only by a renaming of their private variables, which is the substitution
   this finds.

   The search is a depth-first extension of a seed binding [x -> y] to every
   further variable of [D] that a touched disjunct forces, bounded by
   [max_checks] normalisations per call; past the bound the clause is
   returned with the condensations found so far, which is still exact.
   Everything outside [phi]'s disjuncts is returned as it was.

   A seed [x -> y] takes [y] from a live disjunct shaped like [x]'s first
   one (see [bag_ids]) that does not mention [x], or that mentions [x] and
   has at most [merge_seed_nodes] nodes.  The first kind is what a renamed
   copy needs: under a renaming that merges no two variables of [x]'s
   disjunct its image has the same shape and must be a live disjunct free
   of the domain, which holds [x].  The second kind can succeed only by
   merging [x] into a variable it shares a disjunct with, so that the image
   normalises to some other disjunct; that is cheap to try on a small
   disjunct and is not tried on a large one, where it was the whole cost: a
   390-node disjunct with ten private variables and no partner of its shape
   seeded searches over renamings of its own variables that ended only at
   the budget, 18,000 normalisations and half a minute on a single
   resolvent.  The condensations this is wanted for are between disjuncts
   of at most 15 nodes, which are searched exactly as before.

   [max_search_nodes] bounds the calls of the search in one condensation,
   over all seeds and passes ([None], the default: no bound).  The
   normalisation budgets do not bound them: an image already normalised is
   answered from the caches without a check, so a seed whose candidates all
   lead to remembered images backtracks through every binding of the private
   variables of the same sort at no cost to either budget.  On a Rust-derived
   input with arity-27 loop invariants one condensation of one resolvent ran that
   way for more than two minutes, all of it in [search] and [cands]; a bound
   per seed did not help, since such a resolvent has hundreds of seeds.  Past
   the bound the search fails, as at the budgets, and the result is still
   exact.

   With [~memo_failures:true] a call of the search that fails, with no
   budget cut below it, is remembered with its touched disjuncts, the
   variable it chose, and the state at entry of every variable its whole
   execution read, at the precision each read looked at (decided or not;
   bound, fixed or neither; bound to what).  A later call with the same
   touched disjuncts that agrees on all of those is answered as failed
   without being searched.  This is exact and keeps the result: the search
   is deterministic, and what it does at a call is a function of the touched
   disjuncts, the live ones (the memo is cleared when they change), the
   remembered normal forms (a function of the image asked for) and the
   variables' states it reads, so a call agreeing on those executes the same
   way and fails too (a remembered failure answering inside it changes no
   result, by induction).  So within the budgets the same condensation is
   found after no more search calls; where a budget cuts the search short
   it can find more, still exactly.  Why it is wanted: a failure in one
   group of variables (a variable none of whose candidates fits, so that
   fixing it fails too) was rediscovered under every combination of
   bindings of unrelated variables chosen before it.  On one resolvent of a
   Rust-derived input with arity-28 loop invariants (128 disjuncts, 81 private
   variables) the search without it ran past 300,000 calls (12 s, and
   minutes uncapped); with it, it ended after 13,190 calls in 1 s and
   dropped 55 disjuncts where the capped search had dropped 2, and on two
   neighbours of 113 and 114 disjuncts it took 6,434 and 7,057 calls where
   it had taken 26,709 and 27,353, with the same result.

   With [~atom_free:false] a clause with no atom (neither in [ps] nor in
   [ns]) is returned as it is: there every variable is one no atom reads,
   so what a condensation does is replace variables of the clause by
   copies of them, which is exact but changes the clause a later solver
   is asked about, not only its size.

   With [~shape_candidates:true] a variable [u] of the search is bound only
   to a variable that every live disjunct holding [u] can line up with (see
   [shape_cands]): where a renamed copy is being dropped, the variable
   printed at [u]'s place in a disjunct of the same normal-form shape.
   Without it every variable of [u]'s sort is tried, and a failure shows
   only once a touched disjunct has all its variables decided, so on a
   clause of many same-shaped disjuncts linked by shared variables (one
   Rust-derived loop resolvent: 24 disjuncts of 3-58 nodes, 22 private variables,
   one condensation to find) the search spent its whole budget of 20,000
   normalisations over 20,000 nodes, 4-6 s, and 17 such calls took 18-80 s
   of one run depending on load; with the restriction the same 17 calls
   took under a second together.  The result is exact either way (a found
   renaming is checked by normalisation as before) but not always the
   same: a renaming that merges two variables of a disjunct onto a third
   variable it does not mention, or whose image normalises to another
   shape without a merge, is no longer found.

   With [~shape_commutative:true] (meaningful with [~shape_candidates]) a
   same-shaped disjunct also offers every variable that plays [u]'s role
   there up to the order of the printed summands (see [roles]).  Without it
   the restriction misses a renamed copy whose variables cross a variable of
   the same coefficient in name order: the normal form sorts a sum's
   summands by name, so the copy prints with the same shape and two
   summands swapped, the printed alignment offers only the wrong partner,
   and since the shapes are equal no other variable of that disjunct is
   offered.  On a straight-line program of 32 contract calls every
   condensation from the 13th elimination on was lost that way, and the
   resolvents kept doubling.  The extension only adds candidates, so the
   result stays exact.

   With [~inclusion_candidates:true] the restriction of [shape_candidates]
   is replaced by a relation computed once per pass from the live disjuncts
   and read by no search call's bindings (see [incl]): [y] is a candidate of
   [u] while every live disjunct holding [u] holds [y] or has a partner in
   which [y] plays [u]'s role up to the order of summands and every other
   variable a partner among its own candidates.  It reads no names, so the
   crossing in name order that defeats the printed alignment does not
   matter, and it contains every binding of a renaming the shape
   restriction looks for.  On the 226 resolvents of a 32-step straight-line
   program it leaves at most seven candidates per variable.  The result
   stays exact.

   With [~joint:true] the substitution may also bind variables of atoms: a
   set [S] of atoms (head atoms and premises) is dropped together with the
   disjuncts [T] of [phi] that mention the bound variables, when one
   substitution [sigma] of variables to variables, with no bound variable in
   its range and no unknown bound, maps every atom of [S] onto a kept atom
   of the same polarity and every disjunct of [T] onto a kept disjunct or
   onto [false] (up to the normal form, and with [joint] up to the names of
   bound variables), and no kept atom mentions a bound variable.  Exact by
   the argument above: the clause [A \/ S \/ T \/ R] implies its instance
   [A \/ S sigma \/ T sigma \/ R], which is [A \/ R] since [A] and [R] do
   not mention the domain and each disjunct of [T sigma] is one of [R] or
   [false], and [A \/ R] implies the clause.  An image [false] is what the
   equation linking a copy to its original becomes ([f(x') != f(x)] under
   [x' -> x]); with [joint] it is accepted by the passes' search as well,
   which is exact by the same argument.  Why it is wanted: inlining a
   definition whose body applies predicates the use clause applies too (a
   straight-line chain of contexts, each premising every earlier one) brings
   a copy of those atoms with private variables AND the pure constraints over
   them; [condense] refuses the atoms because the variables occur in [phi],
   and the search above refuses the disjuncts because the variables occur in
   atoms, so the clause doubled with each predicate eliminated.  The seeds
   are [joint_atom_seeds]'s, at most [joint_max_seeds] pairs per round, each
   searched with [joint_seed_checks] normalisations under the call's
   [max_checks]; the joint rounds run before [passes].  [joint_dropped]
   receives the number of atoms dropped.

   [joint_incl_before_refusal] (for tests only) computes the inclusion
   filter for every joint seed before its refusal test, as the first version
   did, rather than only for a seed that reaches the search; the result is
   the same either way.

   [joint_prune_doomed] prunes a partial joint closure once a live disjunct
   over its bound and fixed variables has no live image (see [doomed]
   below).  Every closure it skips would be refused, so every result is
   still an exact condensation; it need not be the same one, since the
   steps saved under [joint_atom_seeds]' per-pair bound reach other
   closures.

   [checks_used], when given, receives the number of normalisations the
   call charged against its budget, and [nodes_used] the number of search
   calls it made. *)
let condense_pure ~unknowns ?(max_checks = 20_000) ?(seed_checks = 500)
    ?(merge_seed_nodes = 16) ?(atom_free = true) ?(shape_candidates = false)
    ?(shape_commutative = false) ?(inclusion_candidates = false)
    ?max_search_nodes ?(memo_failures = false) ?checks_used ?nodes_used
    ?(joint = false) ?(joint_seed_checks = 5_000) ?(joint_max_seeds = 2_000)
    ?joint_dropped ?(joint_incl_before_refusal = false)
    ?(joint_prune_doomed = false) (ps, ns, phi) =
  if (not atom_free) && Set.is_empty ps && Set.is_empty ns then (ps, ns, phi)
  else
  let lits_a = Array.of_list (Formula.disjuncts_list_of phi) in
  let n = Array.length lits_a in
  (* The variables are numbered in the order of their names and the
     disjuncts by position.  The search keeps its bindings, decisions and
     caches over these numbers, and builds a formula only for an image it has
     not seen; which variable or disjunct it visits first is the same as when
     it kept them over names (see [lvars_t] below). *)
  let senv =
    Array.fold lits_a ~init:Map.Poly.empty ~f:(fun acc l ->
        Set.fold (Formula.term_sort_env_of l) ~init:acc ~f:(fun acc (x, s) ->
            Map.Poly.set acc ~key:x ~data:s))
  in
  let vars = Array.of_list (Map.Poly.to_alist senv) in
  let nv = Array.length vars in
  let index =
    Map.Poly.of_alist_exn (Array.to_list (Array.mapi vars ~f:(fun k (x, _) -> (x, k))))
  in
  let same_sort a b = try Stdlib.(a = b) with Invalid_argument _ -> false in
  (* [sort_class.(k)]: the first variable with [k]'s sort, so two variables
     have one sort exactly when their classes are equal *)
  let sort_class =
    Array.init nv ~f:(fun k ->
        let s = snd vars.(k) in
        let rec first j = if same_sort (snd vars.(j)) s then j else first (j + 1) in
        first 0)
  in
  (* the atoms kept so far: all of them, until a joint condensation drops
     some (only with [joint]) *)
  let kept_ps = ref ps and kept_ns = ref ns in
  let priv_of ps ns =
    let anchored =
      Set.union
        (Set.concat_map ps ~f:Atom.tvs_of)
        (Set.concat_map ns ~f:Atom.tvs_of)
    in
    Array.map vars ~f:(fun (x, _) ->
        (not (Set.mem anchored x)) && not (Set.mem unknowns x))
  in
  let is_priv = priv_of ps ns in
  (* Base's [Set.find], [find_map] and [for_all] visit a set's elements in
     an order that depends on the shape of its tree, and which variable or
     disjunct the search tries first decides, where the budgets cut it short,
     what it finds.  So the sets whose visiting order matters are built by
     the same operations from the same sets as the search was first written
     with (the variable sets of [Formula.tvs_of], unions of them, and sets of
     disjunct numbers built by [of_list] and [union]), and each is visited
     with the function the first version used; the numbers stand in only
     where the order cannot show. *)
  let lvars_t = Array.map lits_a ~f:Formula.tvs_of in
  let idx x = Map.Poly.find_exn index x in
  let lvars =
    Array.map lvars_t ~f:(fun vs ->
        Set.fold vs ~init:Int.Set.empty ~f:(fun acc x -> Set.add acc (idx x)))
  in
  (* the variables of each disjunct in the order [Set.find] visits them *)
  let lvars_order =
    Array.map lvars_t ~f:(fun vs ->
        let acc = ref [] in
        ignore
          (Set.find vs ~f:(fun x ->
               acc := idx x :: !acc;
               false));
        Array.of_list (List.rev !acc))
  in
  let checks = ref 0 in
  (* With [joint], a quantified normal form has its binders renamed by a
     counter of its own ([Formula.aconv_tvar_norm]), so that two disjuncts
     that differ only by bound names have one normal form: a copy of a
     closed premise inlined from another clause carries binders of its own.
     Comparing up to bound names is exact.  Not done when a name of the
     counter's spelling occurs in the clause. *)
  let alpha_canon =
    joint
    && not
         (String.is_substring (Formula.str_of phi) ~substring:"#jcb")
  in
  let prof_phase = ref 0 in
  let prof_t0 = Common.Clock.now_s () in
  let nf l =
    let t0 = Common.Clock.now_s () in
    let c = Normalizer.normalize @@ Evaluator.simplify l in
    condense_profile.nf_n.(!prof_phase) <- condense_profile.nf_n.(!prof_phase) + 1;
    condense_profile.nf_s.(!prof_phase) <-
      condense_profile.nf_s.(!prof_phase) +. (Common.Clock.now_s () -. t0);
    if alpha_canon && not (Set.is_empty (Formula.quantified_sort_env_of c))
    then
      let k = ref 0 in
      Formula.aconv_tvar_norm
        (fun () ->
          incr k;
          Ident.Tvar (sprintf "#jcb%d" !k))
        c
    else c
  in
  (* [canon_ids] maps the normal form of each input disjunct to the
     disjuncts that have it *)
  let canon_ids = Common.Ext.Hashtbl.PolyDeep.create () in
  (* the normal form two disjuncts are compared in, remembered per formula
     (an image asked for again by a later seed is not normalised again, and
     is not counted against the budgets); what is kept is the disjuncts with
     that normal form, which is all the search reads of it *)
  let memo = Common.Ext.Hashtbl.PolyDeep.create () in
  let matches_of l =
    match Hashtbl.find memo l with
    | Some is -> is
    | None ->
        incr checks;
        let c = nf l in
        (* with [joint], an image that normalises to [false] stands for the
           pseudo-disjunct [-1], which is always kept (see [live]) *)
        let is =
          if joint && Formula.is_false c then [ -1 ]
          else Option.value ~default:[] (Hashtbl.find canon_ids c)
        in
        Hashtbl.set memo ~key:l ~data:is;
        is
  in
  (* the input's own disjuncts first, in order: each one's normal form is
     registered before any image is compared with it; a formula met twice
     among them is normalised (and counted) once *)
  let canon_of =
    Array.map lits_a ~f:(fun l ->
        match Hashtbl.find memo l with
        | Some _ -> l
        | None ->
            incr checks;
            Hashtbl.set memo ~key:l ~data:[];
            nf l)
  in
  let canon_of =
    let first = Common.Ext.Hashtbl.PolyDeep.create () in
    Array.mapi lits_a ~f:(fun i l ->
        match Hashtbl.find first l with
        | Some c -> c
        | None ->
            Hashtbl.set first ~key:l ~data:canon_of.(i);
            canon_of.(i))
  in
  Array.iteri canon_of ~f:(fun i c ->
      Hashtbl.update canon_ids c ~f:(function
        | None -> [ i ]
        | Some is -> is @ [ i ]));
  Array.iteri lits_a ~f:(fun i l ->
      Hashtbl.set memo ~key:l ~data:(Hashtbl.find_exn canon_ids canon_of.(i)));
  (* the symbols of a disjunct's normal form with its variables erased, as a
     sorted list: a renaming that merges no two variables of a disjunct only
     reorders the summands of its normal form, so a disjunct and its image
     have the same one; used only to choose which seeds to try *)
  let bag_ids =
    let tbl = Hashtbl.Poly.create () in
    Array.map canon_of ~f:(fun c ->
        let erase =
          Map.Poly.of_alist_exn
          @@ List.map (Set.to_list (Formula.term_sort_env_of c)) ~f:(fun (x, s) ->
                 (x, Term.mk_var (Ident.Tvar "_") s))
        in
        let b =
          String.split ~on:' ' (Formula.str_of (Formula.subst erase c))
          |> List.sort ~compare:String.compare
        in
        match Hashtbl.find tbl b with
        | Some id -> id
        | None ->
            let id = Hashtbl.length tbl in
            Hashtbl.set tbl ~key:b ~data:id;
            id)
  in
  (* With [shape_candidates]: each disjunct's normal form printed with its
     variables replaced by numbered placeholders, as the string with the
     placeholders erased ([shape_ids], a number per distinct string) and the
     variables in the order they are printed ([occs]); [None] when the normal
     form has a variable the input's disjuncts do not (then the disjunct
     constrains no candidate). *)
  let shape_ids_occs =
    if not (shape_candidates || inclusion_candidates) then ([||], [||], [||])
    else
      let tbl = Hashtbl.Poly.create () in
      let re = Str.regexp "__cpv\\([0-9]+\\)__" in
      let res =
        Array.map canon_of ~f:(fun c ->
            let env = Set.to_list (Formula.term_sort_env_of c) in
            if List.exists env ~f:(fun (x, _) -> not (Map.Poly.mem index x)) then
              (-1, None, None)
            else
              let ren =
                Map.Poly.of_alist_exn
                @@ List.map env ~f:(fun (x, s) ->
                       ( x,
                         Term.mk_var
                           (Ident.Tvar (sprintf "__cpv%d__" (idx x)))
                           s ))
              in
              let str = Formula.str_of (Formula.subst ren c) in
              let occ = ref [] in
              let pos = ref 0 in
              (try
                 while true do
                   let p = Str.search_forward re str !pos in
                   occ := Int.of_string (Str.matched_group 1 str) :: !occ;
                   pos := p + 1
                 done
               with Stdlib.Not_found -> ());
              let shape = Str.global_replace re "_" str in
              let id =
                match Hashtbl.find tbl shape with
                | Some id -> id
                | None ->
                    let id = Hashtbl.length tbl in
                    Hashtbl.set tbl ~key:shape ~data:id;
                    id
              in
              (id, Some (Array.of_list (List.rev !occ)), Some str))
      in
      ( Array.map res ~f:(fun (id, _, _) -> id),
        Array.map res ~f:(fun (_, o, _) -> o),
        Array.map res ~f:(fun (_, _, str) -> str) )
  in
  let shape_ids, occs, shape_strs = shape_ids_occs in
  (* With [shape_commutative] (and [shape_candidates]): the role of each
     variable [k] in each disjunct, as a number: the disjunct's printed normal
     form with [k] printed as one placeholder and every other variable as
     another, cut into its [" + "]-separated pieces (a comparison operator
     being a piece of its own) and sorted.  The normal form orders the summands of a sum by variable name,
     so a renaming that carries a variable past another one of the same
     coefficient permutes them: the image has the same shape and the printed
     alignment pairs the variable with the wrong partner (a disjunct
     [9 - a - b + c >= 0] whose copy is [9 - b - a' + c >= 0] aligns [a]
     with [b]).  The role forgets the order of the pieces, so the variable a
     renamed one becomes has the role it had.  Only a candidate filter: a
     role is never asked to be exact, every renaming found is still checked
     by normalisation. *)
  let roles =
    if not ((shape_candidates && shape_commutative) || inclusion_candidates)
    then [||]
    else
      let tbl = Hashtbl.Poly.create () in
      let re = Str.regexp "__cpv\\([0-9]+\\)__" in
      let plus = Str.regexp_string " + " in
      (* a comparison is cut off its sides too, so that the summand printed
         last (next to [>= 0]) is a piece like any other *)
      let rel = Str.regexp " \\(>=\\|<=\\|!=\\|=\\|>\\|<\\) " in
      Array.mapi shape_strs ~f:(fun i -> function
        | None -> []
        | Some str ->
            let ks =
              match occs.(i) with
              | None -> []
              | Some oi -> List.dedup_and_sort ~compare:Int.compare (Array.to_list oi)
            in
            List.map ks ~f:(fun k ->
                let marked =
                  Str.global_substitute re
                    (fun m ->
                      if Int.of_string (Str.matched_group 1 m) = k then "U"
                      else "_")
                    str
                in
                let key =
                  Str.global_replace rel " + \\1 + " marked
                  |> Str.split plus
                  |> List.sort ~compare:String.compare
                in
                let id =
                  match Hashtbl.find tbl key with
                  | Some id -> id
                  | None ->
                      let id = Hashtbl.length tbl in
                      Hashtbl.set tbl ~key ~data:id;
                      id
                in
                (k, id)))
  in
  let alive = Array.create ~len:n true in
  (* the disjuncts each variable occurs in, latest first *)
  let occ = Array.create ~len:nv [] in
  Array.iteri lvars ~f:(fun i vs ->
      Set.iter vs ~f:(fun k -> occ.(k) <- i :: occ.(k)));
  let lits_of k = List.filter occ.(k) ~f:(fun i -> alive.(i)) in
  (* With [inclusion_candidates]: [incl.(u)] is the set of variables a
     private variable [u] may be bound to, or [None] for no restriction (no
     live disjunct holding [u] has a role for it).  It is the greatest
     relation [C] such that [y] in [C(u)] implies [y <> u], [y] has [u]'s
     sort, and every live disjunct [i] that gives [u] a role [r] (see
     [roles]) either holds [y] (a merge of [u] with a variable of [i]) or has
     a live partner [j] in which [y] has the role [r] and every other
     variable [w] with a role [r'] in [i] has a variable [w2 <> y] of role
     [r'] in [j] with [w2 = w] or, when [w] is private, [w2] in [C(w)].

     Why it is complete for what the search looks for.  Let [sigma] be a
     renaming of private variables that merges no two variables of a
     disjunct onto a third the disjunct does not mention, and under which
     every live disjunct holding a variable of its domain becomes a live
     disjunct.  Take [u] bound to [y] and a live disjunct [i] holding [u].
     If [sigma] merges [u] with a variable of [i], [y] is in [i].  Otherwise
     [sigma] maps the variables of [i] injectively, the image of [i]'s normal
     form is its normal form with the summands reordered, and it is a live
     disjunct [j] in which [y] plays [u]'s role and every other [w] has its
     image [sigma(w)] (itself when [w] is not bound) in the same role.  So
     the bindings of [sigma] satisfy the condition, and the greatest
     relation contains them.  The relation is computed by arc consistency:
     start from the variables that pass the condition with partners
     unconstrained and remove pairs until nothing changes.  It only filters
     candidates; every renaming found is still checked by normalisation, so
     the result stays exact.

     Why it is wanted.  A renamed copy and its original are not isomorphic
     (the original has more occurrences), so colours compared by equality
     separate exactly the pairs the search needs; compared by inclusion
     they keep them.  And the relation reads no names, unlike the printed
     alignment of [shape_candidates], which the normal form's ordering of
     summands by name makes depend on the order of the names.

     Computed over the live disjuncts at the start of each pass of
     [passes] (see there), not per search call: it does not depend on the
     search's bindings. *)
  let incl : Int.Set.t option array = Array.create ~len:nv None in
  let rec compute_incl () =
    let t0 = Common.Clock.now_s () in
    compute_incl_body ();
    condense_profile.incl_n.(!prof_phase) <- condense_profile.incl_n.(!prof_phase) + 1;
    condense_profile.incl_s.(!prof_phase) <-
      condense_profile.incl_s.(!prof_phase) +. (Common.Clock.now_s () -. t0)
  and compute_incl_body () =
    let role_of i k = List.Assoc.find roles.(i) k ~equal:Int.equal in
    (* the live disjuncts in which variable [w] has role [r] *)
    let by_rv = Hashtbl.Poly.create () in
    (* the variables that have role [r] in some live disjunct *)
    let by_r = Hashtbl.Poly.create () in
    Array.iteri roles ~f:(fun j rs ->
        if alive.(j) then
          List.iter rs ~f:(fun (w, r) ->
              Hashtbl.add_multi by_rv ~key:(r, w) ~data:j;
              Hashtbl.update by_r r ~f:(function
                | None -> Int.Set.singleton w
                | Some ws -> Set.add ws w)));
    let partners r y = Option.value ~default:[] (Hashtbl.find by_rv (r, y)) in
    (* the live disjuncts of [u] that give it a role, with that role *)
    let cons =
      Array.init nv ~f:(fun u ->
          if not is_priv.(u) then []
          else
            List.filter_map occ.(u) ~f:(fun i ->
                if alive.(i) then Option.map (role_of i u) ~f:(fun r -> (i, r))
                else None))
    in
    Array.iteri cons ~f:(fun u cs ->
        incl.(u) <-
          (match cs with
          | [] -> None
          | _ ->
              (* the condition with partners unconstrained, starting from the
                 smallest set one disjunct allows *)
              let allows (i, r) =
                Set.union lvars.(i)
                  (Option.value ~default:Int.Set.empty (Hashtbl.find by_r r))
              in
              let bound (i, r) =
                Set.length lvars.(i)
                + Option.value_map ~default:0 (Hashtbl.find by_r r) ~f:Set.length
              in
              let first =
                List.min_elt cs ~compare:(fun a b -> Int.compare (bound a) (bound b))
                |> Option.value_exn
              in
              Some
                (Set.filter (allows first) ~f:(fun y ->
                     y <> u
                     && sort_class.(y) = sort_class.(u)
                     && List.for_all cs ~f:(fun (i, r) ->
                            Set.mem lvars.(i) y
                            || not (List.is_empty (partners r y)))))));
    let img_mem w w2 =
      w2 = w
      || is_priv.(w)
         && match incl.(w) with None -> true | Some c -> Set.mem c w2
    in
    (* does [y] stay a candidate of [u] given the current relation *)
    let supported u y =
      List.for_all cons.(u) ~f:(fun (i, r) ->
          Set.mem lvars.(i) y
          || List.exists (partners r y) ~f:(fun j ->
                 List.for_all roles.(i) ~f:(fun (w, rw) ->
                     w = u
                     || List.exists roles.(j) ~f:(fun (w2, rw2) ->
                            w2 <> y && rw2 = rw && img_mem w w2))))
    in
    let changed = ref true in
    while !changed do
      changed := false;
      for u = 0 to nv - 1 do
        match incl.(u) with
        | None -> ()
        | Some c ->
            let c' = Set.filter c ~f:(supported u) in
            if Set.length c' < Set.length c then (
              incl.(u) <- Some c';
              changed := true)
      done
    done
  in
  let incl_stale = ref true in
  (* With [memo_failures], every read of a variable's state in the search is
     logged with how much of the state it looked at: level 1 whether the
     variable is decided, level 2 whether it is bound, fixed or neither, level
     3 what it is bound to.  A failed call then knows which variables its
     whole execution depended on, and how (see [search]).  [read_log] holds
     [level * nv + k]; the reads of the innermost open call are the entries
     from [frame_start], and [read_stamp.(l - 1).(k)] is the last position
     [k] was logged at with level [l], so a read is logged once per call and
     level. *)
  let read_log = ref (Array.create ~len:(max 16 (4 * nv)) 0) in
  let read_len = ref 0 in
  let read_stamp = Array.init 3 ~f:(fun _ -> Array.create ~len:nv (-1)) in
  let frame_start = ref 0 in
  let read_level = Array.create ~len:nv 0 in
  let rd_at l k =
    if memo_failures && read_stamp.(l - 1).(k) < !frame_start then (
      if !read_len >= Array.length !read_log then (
        let a = Array.create ~len:(2 * Array.length !read_log) 0 in
        Array.blit ~src:!read_log ~src_pos:0 ~dst:a ~dst_pos:0 ~len:!read_len;
        read_log := a);
      !read_log.(!read_len) <- (l * nv) + k;
      read_stamp.(l - 1).(k) <- !read_len;
      incr read_len)
  in
  let rd = rd_at 3 in
  let decided sigma fixed k =
    rd_at 1 k;
    Map.mem sigma k || Set.mem fixed k || not is_priv.(k)
  in
  let in_dom sigma k =
    rd_at 2 k;
    Map.mem sigma k
  in
  let image sigma i =
    Formula.subst
      (Map.fold sigma ~init:Map.Poly.empty ~f:(fun ~key ~data acc ->
           let y, s = vars.(data) in
           Map.Poly.set acc ~key:(fst vars.(key)) ~data:(Term.mk_var y s)))
      lits_a.(i)
  in
  (* the disjuncts with the normal form of disjunct [i]'s image, remembered
     per disjunct and per binding of its own variables in front of
     [matches_of], which still sees every image formula asked for the first
     time, so what it counts against the budgets is unchanged *)
  let image_matches = Hashtbl.Poly.create () in
  let image_match sigma i =
    Set.iter lvars.(i) ~f:rd;
    let key =
      ( i,
        Set.fold lvars.(i) ~init:[] ~f:(fun acc k ->
            match Map.find sigma k with Some y -> (k, y) :: acc | None -> acc)
      )
    in
    match Hashtbl.find image_matches key with
    | Some is -> is
    | None ->
        let is = matches_of (image sigma i) in
        Hashtbl.set image_matches ~key ~data:is;
        is
  in
  (* is some disjunct with these normal forms live and free of the domain
     of [sigma] *)
  let kept_sigma sigma is =
    List.exists is ~f:(fun j ->
        j < 0 || (alive.(j) && not (Set.exists lvars.(j) ~f:(in_dom sigma))))
  in
  (* a touched disjunct whose variables are all decided must become a live
     disjunct; whether that one mentions the final domain is checked at the
     end *)
  let ok sigma fixed i =
    if not (Set.for_all lvars.(i) ~f:(decided sigma fixed)) then true
    else List.exists (image_match sigma i) ~f:(fun j -> j < 0 || alive.(j))
  in
  (* [shape_cands sigma fixed u] (with [shape_candidates]): the variables [u]
     may still be bound to, or [None] for no restriction.  Each live
     disjunct [i] holding [u] in its normal form allows: for each live
     disjunct [j] whose normal form has the same shape, the variable the
     printed occurrences of [u] in [i] line up with in [j], provided the
     occurrences line up as a function that agrees with the decided
     variables' images (what makes [i]'s image [j] when the renaming keeps
     the printed order); every variable of a live disjunct of the same
     symbols ([bag_ids]) but another shape (the renaming reordered the
     normal form); and, for a merge, the image of every other decided
     variable of [i] and every other undecided one.  A candidate outside
     all of these can still succeed only by merging [u] with a variable of
     [i] bound later to the same third variable, or by an image whose normal
     form changes shape under a renaming that merges nothing; those
     condensations are not searched for.  The filter only removes
     candidates, and a found substitution is still checked by
     normalisation, so the result stays exact. *)
  let shape_cands sigma fixed u =
    let img v =
      rd v;
      match Map.find sigma v with Some w -> w | None -> v
    in
    List.fold (List.filter occ.(u) ~f:(fun i -> alive.(i))) ~init:None
      ~f:(fun acc i ->
        match occs.(i) with
        | None -> acc
        | Some oi when not (Array.mem oi u ~equal:Int.equal) -> acc
        | Some oi ->
            let c = ref Int.Set.empty in
            Set.iter lvars.(i) ~f:(fun v ->
                if v <> u then
                  c := Set.add !c (if decided sigma fixed v then img v else v));
            let shape_i = shape_ids.(i) in
            for j = 0 to n - 1 do
              if alive.(j) then
                if shape_ids.(j) = shape_i then (
                  match occs.(j) with
                  | Some oj when Array.length oj = Array.length oi -> (
                      let m = Hashtbl.Poly.create () in
                      let consistent =
                        Array.for_alli oi ~f:(fun p a ->
                            let b = oj.(p) in
                            (not (decided sigma fixed a) || img a = b)
                            &&
                            match Hashtbl.find m a with
                            | Some b' -> b' = b
                            | None ->
                                Hashtbl.set m ~key:a ~data:b;
                                true)
                      in
                      (if consistent then
                         match Hashtbl.find m u with
                         | Some b -> c := Set.add !c b
                         | None -> ());
                      if shape_commutative then
                        match List.Assoc.find roles.(i) u ~equal:Int.equal with
                        | Some r ->
                            List.iter roles.(j) ~f:(fun (w, r') ->
                                if r' = r then c := Set.add !c w)
                        | None -> ())
                  | _ -> ())
                else if bag_ids.(j) = bag_ids.(i) then
                  c := Set.union !c lvars.(j)
            done;
            Some
              (match acc with None -> !c | Some a -> Set.inter a !c))
  in
  let seed_limit = ref 0 in
  let nodes = ref 0 in
  let out_of_nodes () =
    match max_search_nodes with Some m -> !nodes > m | None -> false
  in
  (* With [memo_failures]: the calls of [search] that failed with no budget
     cut below them, keyed by their touched disjuncts and the variable they
     chose, each with the state at entry of every variable its execution
     read.  [search] is a function of [touched], the live disjuncts and the
     states of the variables it reads (bindings, decisions, the remembered
     normal forms being a function of the image), so a call entered with the
     same touched disjuncts and agreeing on all those variables executes the
     same way and fails too: it is answered from here without being searched.
     Cleared when a condensation changes which disjuncts are live. *)
  let failures = Hashtbl.Poly.create () in
  let cuts = ref 0 in
  (* what a read at level [l] saw of [k]'s state *)
  let state_at sigma fixed l k =
    match l with
    | 1 -> if Map.mem sigma k || Set.mem fixed k || not is_priv.(k) then 1 else 0
    | 2 -> if Map.mem sigma k then 2 else if Set.mem fixed k then 1 else 0
    | _ -> (
        match Map.find sigma k with
        | Some w -> w
        | None -> if Set.mem fixed k then -2 else -1)
  in
  let rec search sigma fixed touched =
    incr nodes;
    condense_profile.search_n.(!prof_phase) <- condense_profile.search_n.(!prof_phase) + 1;
    if
      !checks >= max_checks || !checks >= !seed_limit
      || out_of_nodes ()
    then (
      incr cuts;
      None)
    else if not memo_failures then search_body sigma fixed touched
    else
      let saved_start = !frame_start in
      let start = !read_len in
      frame_start := start;
      let cuts0 = !cuts and nodes0 = !nodes in
      let key = ref None in
      let result = search_body ~key sigma fixed touched in
      (* the variables read below with the most each read looked at, kept
         as this call's reads in its caller's segment of the log *)
      let reads =
        let acc = ref [] in
        for p = !read_len - 1 downto start do
          let e = !read_log.(p) in
          let k = e mod nv and l = e / nv in
          if read_level.(k) = 0 then acc := k :: !acc;
          if l > read_level.(k) then read_level.(k) <- l
        done;
        List.map !acc ~f:(fun k ->
            let l = read_level.(k) in
            read_level.(k) <- 0;
            (k, l))
      in
      (match (result, !key) with
      | None, Some key when !cuts = cuts0 && !nodes - nodes0 >= 1 ->
          let ks = Array.of_list (List.map reads ~f:fst)
          and ls = Array.of_list (List.map reads ~f:snd) in
          let vs = Array.mapi ks ~f:(fun p k -> state_at sigma fixed ls.(p) k) in
          let groups =
            match Hashtbl.find failures key with
            | Some g -> g
            | None ->
                let g = ref [] in
                Hashtbl.set failures ~key ~data:g;
                g
          in
          (match
             List.find !groups ~f:(fun (ks', ls', _) ->
                 Stdlib.(ks' = ks) && Stdlib.(ls' = ls))
           with
          | Some (_, _, tbl) -> Hash_set.add tbl vs
          | None ->
              let tbl = Hash_set.Poly.create () in
              Hash_set.add tbl vs;
              groups := (ks, ls, tbl) :: !groups)
      | _ -> ());
      read_len := start;
      frame_start := saved_start;
      List.iter reads ~f:(fun (k, l) ->
          for l' = 1 to 3 do
            read_stamp.(l' - 1).(k) <- -1
          done;
          rd_at l k);
      result
  and search_body ?key sigma fixed touched =
      match
        Set.find_map touched ~f:(fun i ->
            Array.find lvars_order.(i) ~f:(Fn.non (decided sigma fixed)))
      with
      | None ->
          if Set.for_all touched ~f:(fun i -> kept_sigma sigma (image_match sigma i))
          then Some (Int.Set.of_list (Map.keys sigma))
          else None
      | Some u -> (
          let hit =
            match key with
            | None -> false
            | Some r ->
                let k = (Set.to_list touched, u) in
                r := Some k;
                match Hashtbl.find failures k with
                | None -> false
                | Some groups ->
                    List.exists !groups ~f:(fun (ks, ls, tbl) ->
                        Hash_set.mem tbl
                          (Array.mapi ks ~f:(fun p x -> state_at sigma fixed ls.(p) x))
                        && (Array.iteri ks ~f:(fun p x -> rd_at ls.(p) x);
                            true))
          in
          if hit then None
          else
          let lits_u = Set.Poly.of_list (lits_of u) in
          let touched' = Set.union touched lits_u in
          (* Every disjunct of [touched] passed [ok] when this call was
             entered, and binding or fixing [u] (and fixing its image [w])
             changes [ok] only for a disjunct mentioning one of them: any
             other keeps its decidedness and its image, and its normal form
             is already remembered, so it passes again without a new image.
             So only those are asked, in the order of the whole set, which
             asks for the same new images in the same order. *)
          let try_bind w sigma fixed =
            if
              Set.for_all touched' ~f:(fun i ->
                  (not (Set.mem lvars.(i) u || Set.mem lvars.(i) w))
                  || ok sigma fixed i)
            then
              search sigma fixed touched'
            else None
          in
          let allowed =
            if inclusion_candidates then incl.(u)
            else if shape_candidates then shape_cands sigma fixed u
            else None
          in
          let try_cand w =
            if
              w <> u
              && (not (in_dom sigma w))
              && sort_class.(w) = sort_class.(u)
              && (match allowed with None -> true | Some c -> Set.mem c w)
            then try_bind w (Map.set sigma ~key:u ~data:w) (Set.add fixed w)
            else None
          in
          let rec cands w =
            if w >= nv then None
            else
              match try_cand w with
              | Some _ as r -> r
              | None -> cands (w + 1)
          in
          (* with the inclusion relation the candidates are visited in the
             same increasing order, without scanning every variable *)
          let first_cand =
            match (inclusion_candidates, allowed) with
            | true, Some c -> Set.find_map c ~f:try_cand
            | _ -> cands 0
          in
          match first_cand with
          | Some _ as r -> r
          | None ->
              let fixed = Set.add fixed u in
              if
                Set.for_all touched ~f:(fun i ->
                    (not (Set.mem lvars.(i) u)) || ok sigma fixed i)
              then search sigma fixed touched
              else None)
  in
  (* the live disjuncts per shape, kept until a condensation changes which
     disjuncts are live *)
  let ys_cache = Hashtbl.Poly.create () in
  let sizes = Array.map lits_a ~f:(fun l -> lazy (Formula.ast_size l)) in
  let try_seed x =
    match lits_of x with
    | [] -> None
    | i0 :: _ as xl ->
        let b0 = bag_ids.(i0) in
        (* the images of [x]: the variables of the live disjuncts shaped like
           one of [x]'s, a large one only if it does not mention [x] (see the
           head comment) *)
        let js =
          match Hashtbl.find ys_cache b0 with
          | Some js -> js
          | None ->
              let js =
                List.filter (List.init n ~f:Fn.id) ~f:(fun j ->
                    alive.(j) && bag_ids.(j) = b0)
              in
              Hashtbl.set ys_cache ~key:b0 ~data:js;
              js
        in
        let ys =
          List.fold js ~init:Set.Poly.empty ~f:(fun acc j ->
              if Set.mem lvars.(j) x && Lazy.force sizes.(j) > merge_seed_nodes
              then acc
              else Set.union acc lvars_t.(j))
        in
        let touched = Set.Poly.of_list xl in
        let allowed =
          if inclusion_candidates then incl.(x)
          else if shape_candidates then
            shape_cands Int.Map.empty Int.Set.empty x
          else None
        in
        Set.find_map ys ~f:(fun y ->
            let y = idx y in
            if
              y = x
              || sort_class.(y) <> sort_class.(x)
              || match allowed with None -> false | Some c -> not (Set.mem c y)
            then None
            else (
              seed_limit := !checks + seed_checks;
              let sigma = Int.Map.singleton x y in
              let fixed = Int.Set.singleton y in
              if Set.for_all touched ~f:(ok sigma fixed) then
                search sigma fixed touched
              else None))
  in
  (* passes over the variables until one finds nothing: dropping disjuncts
     can enable a seed an earlier one failed *)
  let rec passes () =
    let found = ref false in
    if inclusion_candidates && !incl_stale then (
      compute_incl ();
      incl_stale := false);
    for x = 0 to nv - 1 do
      if is_priv.(x) && !checks < max_checks && not (out_of_nodes ()) then
        match try_seed x with
        | None -> ()
        | Some dom ->
            found := true;
            Hashtbl.clear ys_cache;
            Hashtbl.clear failures;
            incl_stale := true;
            Array.iteri lvars ~f:(fun i vs ->
                if not (Set.are_disjoint vs dom) then alive.(i) <- false)
    done;
    if !found && !checks < max_checks && not (out_of_nodes ()) then passes ()
  in
  (* [joint]: drop a set of atoms together with the disjuncts that mention
     their variables, under one substitution (see the head comment).  A seed
     from [joint_atom_seeds] fixes the substitution on the atoms' variables;
     the search extends it over the variables of the touched disjuncts no
     kept atom reads, as for a seed of [passes]. *)
  (* [doomed (sigma, fixed)] for a partial closure of [joint_atom_seeds]: a
     live disjunct holding a variable of the closure's domain, whose
     variables are all bound or fixed, and whose image under the bindings is
     no live disjunct (nor [false]).  Bindings and fixed variables only grow
     along a closure, so in every complete closure that disjunct is touched,
     decided and imageless, and the hand-over refuses it at [ok] (or earlier);
     its subtree is not enumerated.  So no closure the hand-over would accept
     is lost to the prune itself; but the steps it saves under the per-pair
     closure bound let the enumeration reach closures it did not reach
     before, and the test may ask images the hand-over would not have asked,
     so the condensation found and the normalisation count can differ (each
     result is exact either way).  On one Rust-derived resolvent every one of 43,131 refused closures
     failed at [ok], and their enumeration was 143 of the call's 176 s. *)
  let doomed =
    if not joint_prune_doomed then fun _ -> false
    else fun (bs, fx) ->
      let sigma =
        Map.Poly.fold bs ~init:(Some Int.Map.empty) ~f:(fun ~key ~data acc ->
            match acc with
            | None -> None
            | Some m -> (
                match (Map.Poly.find index key, Map.Poly.find index data) with
                | Some kx, Some ky -> Some (Map.set m ~key:kx ~data:ky)
                | None, _ -> Some m
                | Some _, None -> None))
      in
      match sigma with
      | None -> false
      | Some sigma ->
          let fixed =
            Set.fold fx ~init:Int.Set.empty ~f:(fun acc x ->
                match Map.Poly.find index x with
                | Some k -> Set.add acc k
                | None -> acc)
          in
          (not (Map.is_empty sigma))
          && Map.existsi sigma ~f:(fun ~key ~data:_ ->
                 List.exists occ.(key) ~f:(fun i ->
                     alive.(i)
                     && Set.for_all lvars.(i) ~f:(fun k ->
                         Map.mem sigma k || Set.mem fixed k)
                     && not
                          (List.exists (image_match sigma i) ~f:(fun j ->
                               j < 0 || alive.(j)))))
  in
  let n_joint = ref 0 in
  let rec joint_loop () =
    if !checks < max_checks && not (out_of_nodes ()) then
      let found =
        joint_atom_seeds ~unknowns ~max_seeds:joint_max_seeds ~doomed
          ~pure:
            (List.filter_mapi (Array.to_list lvars_t) ~f:(fun i vs ->
                 if alive.(i) then Some vs else None))
          !kept_ps !kept_ns
          ~f:(fun (dps, dns, binds, fixd) ->
            condense_profile.seeds <- condense_profile.seeds + 1;
            let tf0 = Common.Clock.now_s () in
            (fun g ->
              Exn.protect ~f:g ~finally:(fun () ->
                  condense_profile.seed_f_s <-
                    condense_profile.seed_f_s +. (Common.Clock.now_s () -. tf0)))
            @@ fun () ->
            if !checks >= max_checks || out_of_nodes () then (
              condense_profile.refused_budget <- condense_profile.refused_budget + 1;
              None)
            else
              let kps = Set.diff !kept_ps dps and kns = Set.diff !kept_ns dns in
              (* the variables private once the seed's atoms are dropped *)
              let priv' = priv_of kps kns in
              let ok_binds =
                List.for_all binds ~f:(fun (x, y) ->
                    match (Map.Poly.find index x, Map.Poly.find index y) with
                    | None, _ -> true
                    | Some _, None -> false
                    | Some kx, Some ky ->
                        priv'.(kx) && sort_class.(kx) = sort_class.(ky))
              in
              if not ok_binds then (
                condense_profile.refused_binds <- condense_profile.refused_binds + 1;
                joint_trace (fun () ->
                    sprintf "seed refused: %s"
                      (String.concat ~sep:" "
                         (List.filter_map binds ~f:(fun (x, y) ->
                              match (Map.Poly.find index x, Map.Poly.find index y) with
                              | Some _, None ->
                                  Some (sprintf "%s->%s(image not in phi)"
                                          (Ident.name_of_tvar x) (Ident.name_of_tvar y))
                              | Some kx, Some ky
                                when not (priv'.(kx) && sort_class.(kx) = sort_class.(ky)) ->
                                  Some (sprintf "%s->%s(not private or sort)"
                                          (Ident.name_of_tvar x) (Ident.name_of_tvar y))
                              | _ -> None))));
                None)
              else
                let sigma =
                  List.fold binds ~init:Int.Map.empty ~f:(fun acc (x, y) ->
                      match Map.Poly.find index x with
                      | Some kx -> Map.set acc ~key:kx ~data:(idx y)
                      | None -> acc)
                in
                let fixed =
                  List.fold fixd ~init:Int.Set.empty ~f:(fun acc x ->
                      match Map.Poly.find index x with
                      | Some k -> Set.add acc k
                      | None -> acc)
                in
                let saved = Array.copy is_priv in
                Array.blit ~src:priv' ~src_pos:0 ~dst:is_priv ~dst_pos:0 ~len:nv;
                Hashtbl.clear failures;
                Hashtbl.clear ys_cache;
                (* the candidate filter of [inclusion_candidates] for the
                   variables private once the seed's atoms are dropped.  Only
                   [search] reads it ([ok] does not), so it is computed only
                   for a seed that reaches the search: of 43,195 seeds of one
                   resolvent 64 did, and computing it for every seed cost 83
                   of the call's 231 s.  [joint_incl_before_refusal] restores
                   the earlier order, for the test that the results agree. *)
                if inclusion_candidates && joint_incl_before_refusal then
                  compute_incl ();
                incl_stale := true;
                let touched =
                  Map.fold sigma ~init:Set.Poly.empty ~f:(fun ~key ~data:_ acc ->
                      Set.union acc (Set.Poly.of_list (lits_of key)))
                in
                seed_limit := !checks + joint_seed_checks;
                let res =
                  if Map.is_empty sigma then Some Int.Set.empty
                  else
                    match Set.find touched ~f:(fun i -> not (ok sigma fixed i)) with
                    | None ->
                        let c0 = !checks in
                        condense_profile.seeds_searched <-
                          condense_profile.seeds_searched + 1;
                        if inclusion_candidates && not joint_incl_before_refusal
                        then compute_incl ();
                        let r = search sigma fixed touched in
                        if Option.is_none r then
                          joint_trace (fun () ->
                              sprintf "search failed: %d bound, %d touched, %d checks"
                                (Map.length sigma) (Set.length touched) (!checks - c0));
                        r
                    | Some i ->
                        condense_profile.refused_ok <- condense_profile.refused_ok + 1;
                        (* would a shape test have refused it: no live disjunct
                           other than [i] has [i]'s bag of symbols *)
                        if
                          not
                            (Array.existsi bag_ids ~f:(fun j b ->
                                 j <> i && alive.(j) && b = bag_ids.(i)))
                        then
                          condense_profile.refused_ok_shape <-
                            condense_profile.refused_ok_shape + 1;
                        joint_trace (fun () ->
                            let s = Formula.str_of (image sigma i) in
                            sprintf "touched disjunct without image: %s"
                              (String.prefix s 400));
                        None
                in
                match res with
                | Some dom ->
                    Array.iteri lvars ~f:(fun i vs ->
                        if not (Set.are_disjoint vs dom) then alive.(i) <- false);
                    kept_ps := kps;
                    kept_ns := kns;
                    Hashtbl.clear failures;
                    Hashtbl.clear ys_cache;
                    incl_stale := true;
                    n_joint := !n_joint + Set.length dps + Set.length dns;
                    Some ()
                | None ->
                    Array.blit ~src:saved ~src_pos:0 ~dst:is_priv ~dst_pos:0
                      ~len:nv;
                    Hashtbl.clear failures;
                    None)
      in
      match found with Some () -> joint_loop () | None -> ()
  in
  let lap k t0 =
    condense_profile.phase_s.(k) <-
      condense_profile.phase_s.(k) +. (Common.Clock.now_s () -. t0)
  in
  lap 0 prof_t0;
  prof_phase := 1;
  let t1 = Common.Clock.now_s () in
  if joint then joint_loop ();
  lap 1 t1;
  prof_phase := 2;
  let t2 = Common.Clock.now_s () in
  passes ();
  lap 2 t2;
  Option.iter joint_dropped ~f:(fun r -> r := !n_joint);
  Option.iter checks_used ~f:(fun r -> r := !checks);
  Option.iter nodes_used ~f:(fun r -> r := !nodes);
  if Array.for_all alive ~f:Fn.id && !n_joint = 0 then (ps, ns, phi)
  else
    ( !kept_ps,
      !kept_ns,
      Formula.or_of
        (List.filteri (Array.to_list lits_a) ~f:(fun i _ -> alive.(i))) )
