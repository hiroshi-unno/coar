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
   theory fixes ([interpretation_dependent] says which are not, by symbol and
   two syntactic guards).
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
   the safe direction and it is not free -- see below.  Two exceptions.  A
   selector read guarded by its own constructor's tester in the formula
   itself ([is_C t /\ .. s t ..] or [~is_C t \/ .. s t ..]) is not counted
   ([settle_guarded_selector_reads]): the formula is then equivalent to one
   with a bound variable in place of the read.  And when
   [seq_read_range_guard] is on, a formula whose only open symbol is a
   sequence read and each of whose reads the formula itself puts in range
   ([settle_in_range_seq_reads]) is not reported.  Anything the syntactic tests
   cannot show stays reported.

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

(* Each result is distinct from every input spelling and earlier result of
   this generator. Classification placeholders must preserve independence even
   though the transformed formula is never submitted to a solver. *)
let fresh_read_placeholders ~prefix phi =
  let occupied = Formula.names_spelled_in phi in
  let n = ref 0 in
  let rec fresh sort =
    incr n;
    let name = Ident.Tvar (sprintf "%s%d" prefix !n) in
    if Set.mem occupied name then fresh sort else Term.mk_var name sort
  in
  fresh

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
   original, and stays too. An in-range outer read must also retain any
   unsettled read in its arguments: its element may itself depend on an
   out-of-range read. Both refusals lose only in the safe direction. *)
let settle_in_range_seq_reads phi =
  let fresh = fresh_read_placeholders ~prefix:"#seq_read_in_range" phi in
  let guards =
    List.filter_map (Formula.disjuncts_list_of phi) ~f:nonneg_form_of
  in
  let implied target = List.exists guards ~f:(lin_implies target) in
  let has_unsettled_read t =
    Set.exists (Term.funsyms_of t) ~f:(function
      | T_seq.SqNth _ -> true
      | _ -> false)
  in
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
        if in_range && not (has_unsettled_read s || has_unsettled_read j) then
          fresh se
        else t
    | t -> t)

(* Does the theory leave the value of an application of this symbol open, so
   that it may differ between models?  By symbol, and so conservative: a
   division is open only at divisor zero, but every division is reported. *)
let theory_open_symbol = function
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

(* [phi] with every tester-guarded selector read replaced by a placeholder
   variable of its own, and each guard by the constructor equation over the
   placeholders: at a conjunction, a conjunct [is_C t] and the reads of [C]'s
   fields on [t] in the other conjuncts; at a disjunction, a disjunct
   [~is_C t] and the reads in the other disjuncts ([Evaluator]'s lemma, for a
   datatype with at least two constructors).  Every connective and quantifier
   is entered, since the lemma is an equivalence of subformulas.

   What it is for: the result, read with each placeholder bound where its
   guard stood ([exists] at a conjunction, [forall] at a disjunction), is
   equivalent to [phi] in every model whatever a selector off its constructor
   denotes, and it has no such selector read.  So if the result mentions no
   open symbol, the truth value of [phi] is fixed by the theory once its free
   variables are; a read the traversal does not reach (under a [let], in an
   array lambda or an embedded formula, or under a binder of a variable of
   the guarded term) keeps its selector and is still reported.  Placeholders
   are distinct per guard and field, so a guard on one read is never taken
   for a guard on another; the result is a test object and is not meant to be
   solved. *)
let settle_guarded_selector_reads phi =
  let fresh = fresh_read_placeholders ~prefix:"#guarded_read" phi in
  let fresh_fields sorts = List.map sorts ~f:fresh in
  let rec settle ~holds ds =
    match Evaluator.settle_one_tester_guard ~holds ~fresh_fields ds with
    | Some ds -> settle ~holds ds
    | None -> ds
  in
  let rec go = function
    | Formula.BinaryOp (Formula.Or, _, _, _) as phi ->
        Formula.or_of
          (List.map ~f:go
          @@ settle ~holds:false (Evaluator.or_operands phi))
    | Formula.BinaryOp (Formula.And, _, _, _) as phi ->
        Formula.and_of
          (List.map ~f:go
          @@ settle ~holds:true (Evaluator.and_operands phi))
    | Formula.UnaryOp (op, phi, info) -> Formula.mk_unop ~info op (go phi)
    | Formula.BinaryOp (op, phi1, phi2, info) ->
        Formula.mk_binop ~info op (go phi1) (go phi2)
    | Formula.Bind (b, params, body, info) -> Formula.mk_bind ~info b params (go body)
    | phi -> phi
  in
  go phi

let is_open_selector = function
  | T_dt.DTSel _ as sym -> theory_open_symbol sym
  | _ -> false

(* Does [t] contain a subterm whose value the theory leaves open (a division
   whose divisor is not a non-zero literal, a selector of a datatype with
   several constructors, a sequence read, an exponentiation), not counting
   applications of function variables, which the caller accounts for itself?
   Every subterm is visited, including the bodies of array lambdas and of
   embedded formulas (those by symbol, after their tester-guarded selector
   reads are taken out), so a [false] answer means the term's value is fixed
   by the theory once its variables and function variables are.  A read
   guarded only by an [ite] on its tester is still reported. *)
let nonzero_literal = function
  | Term.FunApp (T_int.Int n, [], _) -> not (Z.equal n Z.zero)
  | Term.FunApp (T_real.Real q, [], _) -> not (Q.equal q Q.zero)
  | _ -> false

let rec has_theory_open_term t =
  match t with
  | Term.Var _ -> false
  | Term.FunApp (T_bool.Formula phi, args, _) ->
      Set.exists
        (Formula.funsyms_of @@ settle_guarded_selector_reads phi)
        ~f:(function FVar _ -> false | sym -> theory_open_symbol sym)
      || List.exists args ~f:has_theory_open_term
  | Term.FunApp ((T_int.Div _ | T_int.Rem _ | T_real.RDiv), [ a; b ], _) ->
      (not (nonzero_literal b)) || has_theory_open_term a || has_theory_open_term b
  | Term.FunApp (FVar _, args, _) -> List.exists args ~f:has_theory_open_term
  | Term.FunApp (sym, args, _) ->
      theory_open_symbol sym || List.exists args ~f:has_theory_open_term
  | Term.LetTerm (_, _, def, body, _) ->
      has_theory_open_term def || has_theory_open_term body

(* Is the value of [t] left open by the theory at its root, as opposed to in
   a subterm?  The root-level counterpart of [has_theory_open_term] over the
   symbols of the SMT-LIB theories only: a division or remainder whose divisor
   is not a non-zero literal, a selector of a datatype with several
   constructors, a sequence read.  Exponentiation is left out although
   [theory_open_symbol] reports it: it is in no SMT-LIB theory and z3 and
   cvc5 disagree about [0 ^ 0], so a constraint fixing its value describes no
   agreed structure.  Applications of function variables are not background
   values and are never reported. *)
let theory_open_at_root = function
  | Term.FunApp ((T_int.Div _ | T_int.Rem _ | T_real.RDiv), [ _; b ], _) ->
      not (nonzero_literal b)
  | Term.FunApp ((FVar _ | T_int.Power | T_real.RPower), _, _) -> false
  | Term.FunApp (sym, _, _) -> theory_open_symbol sym
  | _ -> false

let interpretation_dependent phi =
  let is_seq_read = function T_seq.SqNth _ -> true | _ -> false in
  let open_symbol = theory_open_symbol in
  let fsyms = Formula.funsyms_of phi in
  (* a selector read guarded by its own tester has the value the theory
     fixes ([settle_guarded_selector_reads]); the test goes on with the
     guarded reads out of the formula *)
  let phi, fsyms =
    if Set.exists fsyms ~f:is_open_selector then
      let phi = settle_guarded_selector_reads phi in
      (phi, Formula.funsyms_of phi)
    else (phi, fsyms)
  in
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

(** The one validity question [simplify unknowns check_valid cl] asks of
    [cl], and what [simplify] does without asking: [`Dropped] when it returns
    [None] whatever the answers, [`Kept] when it returns [Some _] without
    calling [check_valid], and [`Ask phi1] when it calls [check_valid phi1]
    once (and drops the clause exactly when that answer is [`Valid]).  It
    follows [simplify]'s steps up to that call, so the question is the one
    [simplify] asks.  What it is for: a caller that has established that
    [phi1] is not valid (a countermodel) knows that [simplify] keeps the
    clause, since a sound validity check never answers [`Valid] for it, and
    that the kept clause has [cl]'s environment and atoms, which [simplify]
    never changes. *)
let validity_question unknowns (_senv, pos, neg, phi) =
  let phi = Evaluator.simplify phi in
  let phis =
    Set.Poly.map (Formula.disjuncts_of phi) ~f:(fun phi ->
        (Formula.fvs_of phi, phi))
  in
  if Set.are_disjoint pos neg then
    let fvs_phi = Set.concat_map ~f:fst phis in
    if Set.are_disjoint fvs_phi unknowns then
      let fvs_pos_neg = Set.concat_map (Set.union pos neg) ~f:Atom.fvs_of in
      let phis1, _ = separate fvs_pos_neg phis in
      `Ask (Formula.or_of @@ Set.to_list (Set.Poly.map ~f:snd phis1))
    else `Kept
  else `Dropped

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
  let linear_equal a b =
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
  (* with the switch off and the act census on, a pair equal up to its linear
     normal form is reported and still treated as different *)
  let equal_int a b =
    if !condense_up_to_linear then linear_equal a b
    else (
      if Common.ActCensus.on () && linear_equal a b then
        Common.ActCensus.note "condensation.up_to_linear";
      false)
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

(* [match_private_formula priv sub pat phi] extends [sub] to a substitution
   for the variables in [priv] under which [pat] is syntactically [phi]: the
   formula analogue of [match_private], with atoms compared argument by
   argument (predicate symbols and predicate variables, with their sorts,
   exactly) and connectives structurally.  A subformula that mentions no
   variable of [priv] is matched only by syntactic equality, and a binder or a
   [let] that mentions one is not matched at all, so [Some] only when [pat]
   really becomes [phi] -- or, with [equal], when it becomes a formula that
   differs from [phi] only at term positions where [equal] holds of the two
   terms. *)
let match_private_formula ?(equal = fun _ _ -> false) priv sub pat phi =
  let same a b = try Stdlib.(a = b) with Invalid_argument _ -> false in
  let sort_of t =
    try Some (Term.sort_of t)
    with e when not (Common.Timer.is_async e) -> None
  in
  let rec term sub pat t =
    if Set.are_disjoint (Term.tvs_of pat) priv then
      if same pat t || equal pat t then Some sub else None
    else
      match (pat, t) with
      | Term.Var (x, s, _), _ when Set.mem priv x -> (
          match Map.Poly.find sub x with
          | Some t' -> if same t' t || equal t' t then Some sub else None
          | None -> (
              match sort_of t with
              | Some s' when same s s' -> Some (Map.Poly.set sub ~key:x ~data:t)
              | _ -> None))
      | ( Term.FunApp (T_bool.Formula p1, [], _),
          Term.FunApp (T_bool.Formula p2, [], _) ) ->
          go sub p1 p2
      | Term.FunApp (f1, a1, _), Term.FunApp (f2, a2, _) -> (
          match f1 with
          | T_bool.Formula _ | T_array.ALambda _ -> None
          | _ ->
              if List.length a1 = List.length a2 && same f1 f2 then
                List.fold2_exn a1 a2 ~init:(Some sub) ~f:(fun acc p u ->
                    Option.bind acc ~f:(fun sub -> term sub p u))
              else None)
      | _ -> None
  and atom sub a1 a2 =
    match (a1, a2) with
    | Atom.App (p1, ts1, _), Atom.App (p2, ts2, _)
      when List.length ts1 = List.length ts2 && same p1 p2 ->
        List.fold2_exn ts1 ts2 ~init:(Some sub) ~f:(fun acc p u ->
            Option.bind acc ~f:(fun sub -> term sub p u))
    | _ -> if same a1 a2 then Some sub else None
  and go sub pat phi =
    if Set.are_disjoint (Formula.tvs_of pat) priv then
      if same pat phi then Some sub else None
    else
      match (pat, phi) with
      | Formula.Atom (a1, _), Formula.Atom (a2, _) -> atom sub a1 a2
      | Formula.UnaryOp (o1, p1, _), Formula.UnaryOp (o2, p2, _) ->
          if same o1 o2 then go sub p1 p2 else None
      | Formula.BinaryOp (o1, l1, r1, _), Formula.BinaryOp (o2, l2, r2, _) ->
          if same o1 o2 then Option.bind (go sub l1 l2) ~f:(fun sub -> go sub r1 r2)
          else None
      | Formula.Bind (b1, env1, p1, _), Formula.Bind (b2, env2, p2, _) ->
          (* the same binder over the same names and sorts: the bound names
             are read as constants of both sides, so a caller that wants
             alpha-variants matched renames the bound variables of both
             canonically first; a bound name must not be in [priv] *)
          if
            same b1 b2 && same env1 env2
            && not (List.exists env1 ~f:(fun (x, _) -> Set.mem priv x))
          then go sub p1 p2
          else None
      | _ -> None
  in
  go sub pat phi

(* The number of match attempts [drop_derived_premises] has made in this
   process, and how many premises it has dropped (read by the tests). *)
let derived_premise_attempts = Atomic.make 0
let derived_premises_dropped = Atomic.make 0

(* [drop_derived_premises ~unknowns ?budget clauses] removes from a clause [C]
   a premise [p(t)] for which the set holds a definite clause [D] (one head
   atom [p(t')] over an unknown, premises [N_D], pure part [Phi_D]) and a
   substitution [sigma] for [D]'s own variables with [p(t') sigma = p(t)],
   every premise of [N_D sigma] a premise of [C] other than [p(t)], and every
   disjunct of [Phi_D sigma] a disjunct of [C]'s pure part.  It is repeated
   clause by clause and premise by premise, each test against the set as
   rewritten so far.

   Why this is exact.  Write [C] as [H \/ not p(t) \/ not N \/ Phi] and take
   any interpretation of the unknowns satisfying [D], in any model.  Fix the
   values of [C]'s variables.  If one of [H], [not N], [Phi] holds, both [C]
   and [C] without [not p(t)] hold.  Otherwise every premise of [N] holds and
   every disjunct of [Phi] is false; so do the premises of [N_D sigma] and the
   disjuncts of [Phi_D sigma], which are among them, and the instance of [D]
   under [sigma] (an instance of a universally quantified clause) forces
   [p(t)], so both clauses are false.  Hence, given [D], the clause and the
   clause without the premise are equivalent, and the clause set keeps exactly
   its solutions -- for every interpretation, so predicate kinds and the
   recovery of eliminated predicates' definitions are unaffected.  [D] is never
   [C] itself and never uses [p(t)] as one of [C]'s premises, which the case
   analysis needs.

   What it is for.  A callee's precondition derived at a call site and
   carried by its postcondition to the return site lands in the return site's
   clause as a premise, beside the very context the call site derived it
   from; when the precondition is later resolved away, each return site gets
   a copy of every call site's context, which the condensations then have to
   remove one by one, if they can.  Dropping the premise first leaves the
   precondition with no premise occurrence at all.

   [budget] bounds the match attempts per pair of a premise and a definite
   clause; running out only means that the premise stays.

   [droppable] (default: every predicate) names the predicates whose premises
   may be dropped.  The equivalence above holds for the set that still
   contains [D]; a caller that afterwards removes or replaces the clauses
   defining a predicate breaks it for that predicate.  The strategy
   refinement of a game solver does exactly that: it hands in a counter-play
   whose strategy predicates are placeholders, protected from elimination,
   each defined by a fact [FN(x)] that it discards after preprocessing to
   synthesise the predicate anew.  Dropping [FN(t)] from the clauses that read
   it, licensed by that fact, left them with no occurrence of the predicate,
   so nothing was left to synthesise and the refinement could only fail.  So
   the predicate eliminator passes the predicates it may eliminate itself
   (ordinary-kind unknowns not protected by its caller): their defining
   clauses are rewritten only by the eliminator, which keeps the set's
   solutions. *)
(* [COAR_DERIVED_TRACE] (instrument only): for each failed pair of a premise
   and a definite clause, one stderr line with how many of the definite
   clause's literals were matched and the instance of the one the search
   stopped at; with [COAR_DERIVED_DUMP=<predicate>] also both clauses'
   literals for that predicate.  Evaluated now: a [lazy] forced by two
   domains at once raises *)
let derived_trace =
  Lazy.from_val (Option.is_some (Stdlib.Sys.getenv_opt "COAR_DERIVED_TRACE"))

(* the normalised disjuncts [drop_derived_premises] made of a pure part, by
   the pure part's physical identity: an elimination step leaves most clauses
   as the same values, and normalising their disjuncts again in every step
   was most of the pass's cost.  A miss only recomputes; emptied when it
   grows past its bound; one table per domain, since eliminations can run
   in parallel domains *)
let derived_disjunct_cache : Formula.t list PhysFormula.t Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> PhysFormula.create 256)

let drop_derived_premises ~unknowns ?(budget = 1_000) ?(is_old = fun _ -> false)
    ?(droppable = fun (_ : string) -> true) (clauses : t Set.Poly.t) =
  let arr = Array.of_list (Set.to_list clauses) in
  (* [old.(k)]: clause [k] took part in an earlier call that tested every pair
     it is in, and is unchanged since, so a pair of two old clauses fails
     again: the test reads nothing but the two clauses and the budget *)
  let old = Array.map arr ~f:is_old in
  let pvar_of = function
    | Atom.App (Predicate.Var (p, _), _, _) -> Some (Ident.name_of_pvar p)
    | _ -> None
  in
  (* the definite clauses, by the name of their head's predicate *)
  let defs = Hashtbl.Poly.create () in
  Array.iteri arr ~f:(fun i (_, ps, _, _) ->
      match Set.to_list ps with
      | [ h ] -> (
          match pvar_of h with
          | Some p -> Hashtbl.add_multi defs ~key:p ~data:i
          | None -> ())
      | _ -> ());
  let key = function
    | Formula.Atom (Atom.App (Predicate.Var (p, _), ts, _), _) ->
        Hashtbl.hash (0, Ident.name_of_pvar p, List.length ts)
    | Formula.Atom (Atom.App (Predicate.Psym s, ts, _), _) ->
        Hashtbl.hash (1, s, List.length ts)
    | Formula.UnaryOp (_, Formula.Atom (Atom.App (Predicate.Psym s, ts, _), _), _)
      ->
        Hashtbl.hash (2, s, List.length ts)
    | _ -> 3
  in
  let changed = ref false in
  let dumped = Hash_set.Poly.create () in
  (* each clause's pure disjuncts with their bound variables renamed
     canonically, made once per clause: a step only ever removes premises, so
     the pure part a clause has at the start is the one it keeps *)
  let canon_disj = Array.map arr ~f:(fun _ -> None) in
  let canon d =
    let k = ref 0 in
    Formula.aconv_tvar_norm
      (fun () ->
        incr k;
        Ident.Tvar (sprintf "#dp%d" !k))
      d
  in
  let norm_disjunct d =
    canon
      (try Normalizer.normalize (Evaluator.simplify (canon d))
       with e when not (Common.Timer.is_async e) -> d)
  in
  let canon_disjuncts k =
    match canon_disj.(k) with
    | Some ds -> ds
    | None ->
        let _, _, _, phi = arr.(k) in
        let cache = Stdlib.Domain.DLS.get derived_disjunct_cache in
        match PhysFormula.find_opt cache phi with
        | Some ds -> canon_disj.(k) <- Some ds; ds
        | None ->
        (* each disjunct simplified and normalised on its own, so that a
           premise the input wrote one way and a resolvent's normalisation
           wrote another (nested binders merged into one block, conjuncts
           reordered) are compared in one form; equivalent disjuncts, so the
           decomposition still denotes the pure part.  The bound names are
           made canonical before the normalisation too, since the order in
           which it writes conjuncts follows the names. *)
        let stamp = Ident.fresh_stamp () in
        let ds =
          List.concat_map (Formula.disjuncts_list_of phi) ~f:(fun d ->
              Formula.disjuncts_list_of (norm_disjunct d))
          |> List.filter ~f:(Fn.non Formula.is_false)
          |> List.map ~f:canon
        in
        canon_disj.(k) <- Some ds;
        (* kept only when the computation drew no fresh name (the simplifier
           draws one for some shapes): the cache is keyed by address, so
           whether a later lookup hits depends on whether the collector moved
           [phi] meanwhile, and a hit that skipped draws would make every
           later fresh name, and through the names the order of later sets,
           depend on the collector's timing *)
        if Ident.fresh_stamp () = stamp then (
          if PhysFormula.length cache > 4096 then PhysFormula.reset cache;
          PhysFormula.replace cache phi ds);
        ds
  in
  let try_drop i a =
    let _, _, ns_c, _ = arr.(i) in
    match pvar_of a with
    | Some p when droppable p -> (
        (* the definite clauses whose premises' predicates, counted, are among
           [C]'s other premises' -- a necessary condition, read before any
           pure part is looked at *)
        let rest_counts = Hashtbl.create (module String) in
        Set.iter ns_c ~f:(fun b ->
            if not (phys_equal b a) then
              Option.iter (pvar_of b) ~f:(fun q -> Hashtbl.incr rest_counts q));
        let fits j =
          let _, ps_d, ns_d, _ = arr.(j) in
          Set.length ps_d = 1
          &&
          let need = Hashtbl.create (module String) in
          Set.iter ns_d ~f:(fun b ->
              match pvar_of b with
              | Some q -> Hashtbl.incr need q
              | None -> Hashtbl.incr need "#other");
          Hashtbl.for_alli need ~f:(fun ~key ~data ->
              data <= Option.value ~default:0 (Hashtbl.find rest_counts key))
        in
        let js =
          List.filter (Hashtbl.find_multi defs p) ~f:(fun j ->
              j <> i && (not (old.(i) && old.(j))) && fits j)
        in
        (not (List.is_empty js))
        &&
        let targets =
          List.map (Set.to_list (Set.remove ns_c a)) ~f:Formula.mk_atom
          @ canon_disjuncts i
        in
        let groups = Hashtbl.create (module Int) in
        List.iter targets ~f:(fun t -> Hashtbl.add_multi groups ~key:(key t) ~data:t);
        (* the equations [C]'s pure part holds when all its disjuncts are
           false: a disjunct [t1 != t2].  Two terms so equated may stand for
           each other in the match, since the case the argument reads is the
           one in which every disjunct is false *)
        let eqs = Common.Ext.Hashtbl.PolyDeep.create () in
        let add t1 t2 =
          Hashtbl.set eqs ~key:(t1, t2) ~data:();
          Hashtbl.set eqs ~key:(t2, t1) ~data:()
        in
        List.iter targets ~f:(function
          | Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _), _) -> (
              add t1 t2;
              (* an integer equation the normal form writes [c1 t1 + c2 t2 != 0]
                 with [c1 = -c2 = +-1] *)
              try
                if Term.is_int_sort (Term.sort_of t1) then
                  let monos =
                    Normalizer.linear_int_monomials_of (Value.Int Z.one)
                      (T_int.mk_sub t1 t2)
                    |> Map.Poly.filter ~f:(function
                         | Value.Int c -> not (Z.equal c Z.zero)
                         | _ -> true)
                  in
                  match Map.Poly.to_alist monos with
                  | [ (Some a, Value.Int c1); (Some b, Value.Int c2) ]
                    when Z.equal (Z.add c1 c2) Z.zero && Z.equal (Z.abs c1) Z.one ->
                      add a b
                  | _ -> ()
              with e when not (Common.Timer.is_async e) -> ())
          | _ -> ());
        let equal t1 t2 = Hashtbl.mem eqs (t1, t2) in
        (* the clause's literals up to the names of their bound variables:
           a closed pattern (one mentioning no variable of the definite
           clause) needs no substitution and holds as a literal of [C]
           exactly when an alpha-variant of it is one -- the same premise
           inserted into two clauses with binders of its own *)
        let canon_targets =
          lazy
            (let tbl = Common.Ext.Hashtbl.PolyDeep.create () in
             List.iter targets ~f:(fun t -> Hashtbl.set tbl ~key:t ~data:());
             tbl)
        in
        List.exists js ~f:(fun j ->
            let senv_d, ps_d, ns_d, phi_d = arr.(j) in
            let priv =
              Set.diff (Map.key_set senv_d) unknowns
            in
            (* Private Boolean aliases are scalar dependencies too. The
               structural matcher does not instantiate predicate heads, so
               refuse this defining clause instead of reading an alias as a
               closed literal after its scalar value was instantiated. *)
            let predicate_names =
              Set.Poly.map ~f:Ident.pvar_to_tvar
                (Set.union (Formula.pvs_of phi_d)
                   (Set.Poly.union_list
                      (List.map (Set.to_list (Set.union ps_d ns_d)) ~f:Atom.pvs_of)))
            in
            if not (Set.are_disjoint priv predicate_names) then false
            else
            match Set.to_list ps_d with
            | [ h ] -> (
                match match_private_formula ~equal priv Map.Poly.empty
                        (Formula.mk_atom h) (Formula.mk_atom a) with
                | None -> false
                | Some sub ->
                    let pats =
                      List.map (Set.to_list ns_d) ~f:Formula.mk_atom
                      @ canon_disjuncts j
                    in
                    let pats =
                      List.map pats ~f:(fun d ->
                          (d, Set.inter (Formula.fvs_of d) priv))
                    in
                    let closed, pats =
                      List.partition_tf pats ~f:(fun (_, vs) -> Set.is_empty vs)
                    in
                    List.for_all closed ~f:(fun (d, _) ->
                        Hashtbl.mem (Lazy.force canon_targets) d)
                    &&
                    let left = ref budget in
                    let total = List.length pats in
                    let deepest = ref (-1, "", 0) in
                    let unbound sub vs =
                      Set.count vs ~f:(fun x -> not (Map.Poly.mem sub x))
                    in
                    let rec search sub pats =
                      match pats with
                      | [] -> true
                      | _ ->
                          (* the premises of [D] first, which bind most
                             variables against few candidates, then the
                             pattern with fewest unbound variables: a bound
                             one is a membership test *)
                          let is_pvar = function
                            | Formula.Atom (Atom.App (Predicate.Var _, _, _), _) -> true
                            | _ -> false
                          in
                          let best, _ =
                            List.fold pats ~init:(None, Int.max_value)
                              ~f:(fun (b, n) ((d, vs) as pd) ->
                                let k =
                                  (if is_pvar d then 0 else 1_000_000)
                                  + unbound sub vs
                                in
                                if k < n then (Some pd, k) else (b, n))
                          in
                          let ((d, _) as pd) = Option.value_exn best in
                          let rest =
                            List.filter pats ~f:(fun q -> not (phys_equal q pd))
                          in
                          let cands = Hashtbl.find_multi groups (key d) in
                          let actual_sub =
                            Map.Poly.of_alist_reduce (Map.Poly.to_alist sub)
                              ~f:(fun a _ -> a)
                          in
                          let safe = Evaluator.scalar_substitution_is_safe actual_sub d in
                          let ok =
                            (* a pattern with every variable bound: its
                               instance normalised as [C]'s disjuncts were,
                               since the normal form of a comparison follows
                               the names of its variables *)
                            (unbound sub (snd pd) = 0
                            && (not (is_pvar d))
                            && safe
                            && (fun f -> Formula.is_false f || Hashtbl.mem (Lazy.force canon_targets) f)
                                 (norm_disjunct
                                    (Formula.subst actual_sub d))
                            && search sub rest)
                            || List.exists cands
                            ~f:(fun t ->
                              !left > 0
                              &&
                              (decr left;
                               Atomic.incr derived_premise_attempts;
                               match match_private_formula ~equal priv sub d t with
                               | Some sub' -> search sub' rest
                               | None -> false))
                          in
                          (if (not ok) && Lazy.force derived_trace then
                             let depth = total - List.length pats in
                             let dd, _, _ = !deepest in
                             if depth > dd then
                               deepest :=
                                 ( depth,
                                   Formula.str_of
                                     (if safe then Formula.subst actual_sub d else d),
                                   List.length cands ));
                          ok
                    in
                    let r = search sub pats in
                    (if (not r) && Lazy.force derived_trace then
                       let dd, str, nc = !deepest in
                       Stdlib.Printf.eprintf
                         "[derived-trace] %s in clause %d by clause %d: %d/%d matched, \
                          stuck at (%d candidates) %s\n%!"
                         p i j dd total nc str);
                    (if (not r) && Lazy.force derived_trace
                        && Stdlib.(Stdlib.Sys.getenv_opt "COAR_DERIVED_DUMP" = Some p)
                        && not (Hash_set.mem dumped (i, j)) then (
                       Hash_set.add dumped (i, j);
                       Stdlib.Printf.eprintf "[derived-dump] D=%d C=%d\n" j i;
                       List.iter pats ~f:(fun (d, _) ->
                           Stdlib.Printf.eprintf "[derived-dump] D: %s\n" (Formula.str_of d));
                       List.iter targets ~f:(fun t ->
                           Stdlib.Printf.eprintf "[derived-dump] C: %s\n" (Formula.str_of t));
                       Stdlib.Printf.eprintf "[derived-dump] head sub: %s\n%!"
                         (String.concat ~sep:", "
                            (List.map (Map.Poly.to_alist sub) ~f:(fun (x, t) ->
                                 Ident.name_of_tvar x ^ ":=" ^ Term.str_of t)))));
                    r)
            | _ -> false))
    | _ -> false
  in
  Array.iteri arr ~f:(fun i _ ->
      let rec loop () =
        let _, _, ns_c, _ = arr.(i) in
        match Set.find ns_c ~f:(try_drop i) with
        | Some a ->
            let senv_c, ps_c, ns_c, phi_c = arr.(i) in
            arr.(i) <- (senv_c, ps_c, Set.remove ns_c a, phi_c);
            old.(i) <- false;
            Atomic.incr derived_premises_dropped;
            changed := true;
            loop ()
        | None -> ()
      in
      loop ());
  if !changed then Set.Poly.of_array arr else clauses

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
   Preserves: [phi] and every literal not removed.

   A literal with no private variable.  Then [sigma] is the identity, and the
   step is the special case [L1 = L2]: with [condense_up_to_linear] set,
   [match_private_atom] with no private variable accepts [L2] against [L1]
   exactly when the two have the same predicate and sorts and each pair of
   arguments is syntactically equal, or (for integer subterms, also inside a
   constructor application) has a difference whose linear normal form is the
   constant [0].  Such a difference is [0] in every model and under every
   interpretation of the unknowns (a function-variable application, an
   integer division or remainder, each kept with its rounding mode, and
   every other non-linear subterm are opaque monomials of the normal form, so
   two of them cancel only when they are the same term), so [L2] and [L1]
   denote the same atom and [L1 \/ L2] is [L1] (idempotence of disjunction,
   of premises and of heads alike).  Why it is needed: resolution writes one
   integer argument as several unnormalised linear terms -- [x], [-(y - x - z
   - y + z)] -- so a clause can carry dozens of copies of one premise that
   share every variable with the rest of the clause; none is
   instance-generalised by another, and each copy multiplies the pure part
   of every later resolvent.  With the switch off nothing is compared here:
   two distinct members of the set are never syntactically equal.
   [condense_linear_duplicates_dropped] counts these drops in the process. *)
let condense_linear_duplicates_dropped = Atomic.make 0

let condense ~unknowns (ps, ns, phi) =
  let condense_side side other =
    let rec loop side =
      (* the first droppable literal, and whether it had no private
         variable (dropped as a duplicate up to the linear normal form) *)
      let found =
        Set.find_map side ~f:(fun n ->
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
            let no_priv = Set.is_empty priv in
            if
              ((not no_priv) || !condense_up_to_linear)
              && Set.exists rest ~f:(fun m ->
                  Option.is_some (match_private_atom priv n m))
            then Some (n, no_priv)
            else None)
      in
      match found with
      | Some (n, no_priv) ->
          if no_priv then (
            Atomic.incr condense_linear_duplicates_dropped;
            Common.PhaseTime.event_here "condense-linear-duplicate");
          loop (Set.remove side n)
      | None -> side
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
let scalar_clause_substitution_is_safe sub (ps, ns, phi) =
  Evaluator.scalar_substitution_is_safe sub phi
  && Set.for_all (Set.union ps ns) ~f:(fun atom ->
         Evaluator.scalar_substitution_is_safe sub (Formula.mk_atom atom))

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
    let admit pair =
      Option.filter pair ~f:(fun (x, y) ->
          scalar_clause_substitution_is_safe
            (Map.Poly.singleton y (Term.mk_var x T_int.SInt)) (ps, ns, phi))
    in
    match
      List.find_mapi ds ~f:(fun k d ->
          match d with
          | Formula.Atom (atm, _) ->
              Option.map (admit (var_pair atm)) ~f:(fun p -> (k, p))
          | Formula.UnaryOp
              ( Formula.Not,
                Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, ts, _), _),
                _ ) ->
              Option.map
                (admit
                   (match ts with
                   | [ t1; t2 ] -> var_pair (T_bool.mk_neq t1 t2)
                   | _ -> None))
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

(* [merge_var_equations ~unknowns (ps, ns, phi)] is
   [merge_int_var_equations] followed by the same renaming for two distinct
   variables of any one sort: a disjunct [x != y] (or [not (x = y)]) whose
   two sides are variables of the same sort, neither an unknown, is removed
   and [y] is replaced by [x] everywhere in the clause, until no such
   disjunct is left.

   Exact for the universal closure in every model, whatever the sort:
   [forall x y. (x != y \/ C(x, y))] is [forall x. C(x, x)].  A variable
   is replaced only by a variable, never by a compound term, and the
   substitution is capture-avoiding.  What it is for: a sequence equation
   between two copies of one witness, [p ++ x = p ++ y], becomes [x = y]
   once its common prefix is cancelled, and only once [y] is renamed into
   [x] does the copy that [y] belongs to become a renaming of the kept one
   that condensation can drop. *)
let merge_var_equations ~unknowns (ps, ns, phi) =
  let ps, ns, phi = merge_int_var_equations ~unknowns (ps, ns, phi) in
  let var_pair t1 t2 =
    match (t1, t2) with
    | Term.Var (x, s1, _), Term.Var (y, s2, _)
      when (not (Ident.tvar_equal x y))
           && (not (Set.mem unknowns x))
           && (not (Set.mem unknowns y))
           && (try Stdlib.(s1 = s2) with Invalid_argument _ -> false) ->
        Some (x, y, s1)
    | _ -> None
  in
  let rec loop (ps, ns, phi) =
    let ds = Formula.disjuncts_list_of phi in
    let admit pair =
      Option.filter pair ~f:(fun (x, y, sort) ->
          scalar_clause_substitution_is_safe
            (Map.Poly.singleton y (Term.mk_var x sort)) (ps, ns, phi))
    in
    match
      List.find_mapi ds ~f:(fun k d ->
          match d with
          | Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _), _)
          | Formula.UnaryOp
              ( Formula.Not,
                Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _),
                _ ) ->
              Option.map (admit (var_pair t1 t2)) ~f:(fun p -> (k, p))
          | _ -> None)
    with
    | None -> (ps, ns, phi)
    | Some (k, (x, y, s)) ->
        let sub = Map.Poly.singleton y (Term.mk_var x s) in
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

(* A match of one atom onto another by [joint_match_atom], compiled: the
   parts of the match that do not read the substitution -- the predicates,
   the function symbols, the sorts of the variables and the subterms matched
   only syntactically -- are compared once, and what is left is a list of
   steps on the substitution, in the order [joint_match_atom] takes them:
   [JVar (x, Some (y, sorts_equal))] for a pattern variable [x] (not an
   unknown) against a variable [y], [JVar (x, None)] against anything else,
   [JFix vs] for a subterm equal to its counterpart, whose variables are
   fixed, and [JFail] where the match fails whatever the substitution.
   [joint_run_plan] on a plan gives what [joint_match_atom] gives on the two
   atoms, from every state: each step does what [joint_match_atom]'s case
   for that position does, the comparisons it skips being the ones whose
   outcome the plan holds.  Why: the enumeration of [joint_atom_seeds]
   matches the same pairs of atoms tens of thousands of times, and the
   sorts it compared each time carry whole datatype definitions. *)
type joint_step =
  | JVar of Ident.tvar * (Ident.tvar * bool) option
  | JFix of Ident.tvar Set.Poly.t
  | JFail

let joint_plan ~unknowns pat t =
  let same a b = try Stdlib.(a = b) with Invalid_argument _ -> false in
  let rec go acc pat t =
    match (pat, t) with
    | Term.Var (x, s, _), _ when not (Set.mem unknowns x) -> (
        match t with
        | Term.Var (y, s', _) -> JVar (x, Some (y, same s s')) :: acc
        | _ -> JVar (x, None) :: acc)
    | Term.FunApp (f1, a1, _), Term.FunApp (f2, a2, _) -> (
        match f1 with
        | T_bool.Formula _ | T_array.ALambda _ ->
            if same pat t then JFix (Term.tvs_of pat) :: acc else JFail :: acc
        | _ ->
            if same f1 f2 && List.length a1 = List.length a2 then
              List.fold2_exn a1 a2 ~init:acc ~f:go
            else JFail :: acc)
    | _ -> if same pat t then JFix (Term.tvs_of pat) :: acc else JFail :: acc
  in
  match (pat, t) with
  | ( Atom.App (Predicate.Var (p1, s1), a1, _),
      Atom.App (Predicate.Var (p2, s2), a2, _) )
    when Ident.pvar_equal p1 p2 && same s1 s2
         && List.length a1 = List.length a2 ->
      List.rev (List.fold2_exn a1 a2 ~init:[] ~f:go)
  | _ -> [ JFail ]

let joint_run_plan plan (sigma, fixed) =
  let fix_all st vs =
    Set.fold vs ~init:(Some st) ~f:(fun acc x ->
        Option.bind acc ~f:(fun (sigma, fixed) ->
            if Map.Poly.mem sigma x then None
            else Some (sigma, Set.add fixed x)))
  in
  List.fold plan ~init:(Some (sigma, fixed)) ~f:(fun acc step ->
      Option.bind acc ~f:(fun ((sigma, fixed) as st) ->
          match step with
          | JFail -> None
          | JFix vs -> fix_all st vs
          | JVar (x, ty) -> (
              match Map.Poly.find sigma x with
              | Some y -> (
                  match ty with
                  | Some (y', _) when Ident.tvar_equal y y' -> Some st
                  | _ -> None)
              | None -> (
                  match ty with
                  | Some (y, true) ->
                      if Ident.tvar_equal x y then Some (sigma, Set.add fixed x)
                      else if Set.mem fixed x || Map.Poly.mem sigma y then None
                      else Some (Map.Poly.set sigma ~key:x ~data:y, Set.add fixed y)
                  | _ -> None))))

(* [joint_atom_seeds ~unknowns ~max_seeds ~f ps ns] calls [f] on candidate
   seeds of a joint condensation, in order, and returns the first [Some] it
   answers ([None] when none does).  A seed ([joint_seed]) is a set of head
   atoms [dps] of [ps] and premises [dns] of [ns] to drop, and a substitution
   of variables to variables ([binds]; [fixed] the variables it maps to
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

   [doomed (sigma, fixed)], when given, is asked of every partial closure
   before it is extended; when it answers [true] the closures extending it are not
   enumerated.  It must answer [true] only when [f] would answer [None] for
   every complete closure extending the partial one (bindings and fixed
   variables only grow along a closure). *)
(* [COAR_JOINT_TRACE] (instrument only): at most [COAR_JOINT_TRACE] lines
   (default 200) on stderr saying why each joint seed failed *)
(* evaluated now: a [lazy] forced by two domains at once raises [Lazy.Undefined] *)
let joint_trace_left =
  Lazy.from_val
    (ref
       (match Stdlib.Sys.getenv_opt "COAR_JOINT_TRACE" with
       | None -> 0
       | Some n -> Option.value ~default:200 (int_of_string_opt n)))

let joint_trace msg =
  let left = Lazy.force joint_trace_left in
  if !left > 0 then (
    decr left;
    eprintf "[joint] %s\n%!" (msg ()))

(* A complete closure [joint_atom_seeds] hands to its [f].  The variables
   are numbered by [joint_atom_seeds] ([js_var] gives a number's variable,
   a bijection on the call's variables); [js_dropped] holds the dropped
   atoms as positions in the atom order [Set.to_list ps @ Set.to_list ns],
   [js_binds] the bindings and [js_fixed] the fixed variables, each listed
   once in no particular order, and [js_atoms] the dropped head atoms and
   premises as sets, computed only when forced. *)
type joint_seed = {
  js_dropped : Int.Set.t;
  js_binds : (int * int) list;
  js_fixed : int list;
  js_var : int -> Ident.tvar;
  js_atoms : (Atom.t Set.Poly.t * Atom.t Set.Poly.t) Lazy.t;
}

(* [joint_plan] over variable numbers: [IVar (x, Some (y, sorts_equal))],
   [IVar (x, None)], [IFix vs] and [IFail] are [JVar], [JFix] and [JFail]
   with each variable replaced by its number *)
type joint_istep = IVar of int * (int * bool) option | IFix of int list | IFail

(* the key of a remembered atom image: the atom's position and, per
   variable of the atom in name order, the number of its image or [-1] *)
module JointImageKey = struct
  type t = int * int list

  let compare (i, l) (j, m) =
    match Int.compare i j with 0 -> List.compare Int.compare l m | r -> r

  let hash (i, l) = List.fold l ~init:i ~f:(fun h x -> (h * 31) + x + 1) land Int.max_value
  let sexp_of_t _ = Sexp.Atom "joint-image"
end

let joint_atom_seeds ~unknowns ~max_seeds ?(closure_steps = 2_000) ?(pure = [])
    ?doomed ~f ps ns =
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
  let same_key i j =
    match (keys.(i), keys.(j)) with
    | Some k1, Some k2 -> Stdlib.(k1 = k2)
    | _ -> false
  in
  (* The variables are numbered, in the order first met, and the closures
     are kept over the numbers: a binding is an [Int.Map], the fixed
     variables an [Int.Set].  A variable is its name ([Ident.tvar] is a
     name), so the numbering is a bijection and every question below has the
     answer it has over names; which closure is visited when, and how the
     per-pair bound [closure_steps] counts, are as over names.  Why: the
     enumeration visits tens of thousands of closures per call on resolvents
     of 13-16 atoms (a hundred thousand on some), nearly all refused by [f],
     and over names every one of its steps compared variable names through
     polymorphic maps and sets, and each closure handed on built the set of
     its dropped atoms, whose comparison walks whole datatype definitions in
     the predicates' sorts. *)
  let ids = Hashtbl.create (module String) in
  let names = ref (Array.create ~len:64 (Ident.Tvar "")) in
  let nvars = ref 0 in
  let id_of x =
    let s = Ident.name_of_tvar x in
    match Hashtbl.find ids s with
    | Some k -> k
    | None ->
        let k = !nvars in
        if k >= Array.length !names then (
          let a = Array.create ~len:(2 * k) (Ident.Tvar "") in
          Array.blit ~src:!names ~src_pos:0 ~dst:a ~dst_pos:0 ~len:k;
          names := a);
        !names.(k) <- x;
        incr nvars;
        Hashtbl.set ids ~key:s ~data:k;
        k
  in
  let var_of k = !names.(k) in
  let tvs =
    Array.map lits ~f:(fun (_, a) -> Array.of_list (List.map (Set.to_list (Atom.tvs_of a)) ~f:id_of))
  in
  (* whether a numbered variable is an unknown, and the disjuncts of [pure]
     holding it, both computed when first asked *)
  let unknown_tbl = Hashtbl.create (module Int) in
  let is_unknown k =
    Hashtbl.find_or_add unknown_tbl k ~default:(fun () -> Set.mem unknowns (var_of k))
  in
  (* [verify] asks, of every complete closure, whether each dropped atom's
     image under the closure's bindings is a kept atom of its polarity.  The
     image depends only on the atom and the bindings of its own variables, and
     which atoms it equals does not depend on which are kept, so both are
     remembered per atom and per binding of its variables ([images_of]): the
     closures of one seed share most of their atoms and bindings, and
     substituting an atom and comparing it structurally with every other atom
     (its sorts carry whole datatype definitions) was most of the time of a
     joint condensation, 21 of 29 s on one resolvent of 13 atoms handing
     11,256 closures to [f].  The answer is the one recomputing gives:
     [same] is a function of its arguments and the remembered list holds
     every atom of the polarity the image equals, of which [verify] asks
     whether one is kept. *)
  let env_ids =
    Array.map lits ~f:(fun (_, a) ->
        List.map ~f:id_of
          (List.dedup_and_sort ~compare:Ident.tvar_compare
             (List.map (Set.to_list (Atom.term_sort_env_of a)) ~f:fst)))
  in
  let images_tbl = Hashtbl.create (module JointImageKey) in
  let images_of sigma k =
    let key =
      ( k,
        List.map env_ids.(k) ~f:(fun x ->
            match Map.find sigma x with Some y -> y | None -> -1) )
    in
    match Hashtbl.find images_tbl key with
    | Some js -> js
    | None ->
        let pos, a = lits.(k) in
        let m =
          Set.fold (Atom.term_sort_env_of a) ~init:Map.Poly.empty
            ~f:(fun acc (x, s) ->
              match Map.find sigma (id_of x) with
              | Some y -> Map.Poly.set acc ~key:x ~data:(Term.mk_var (var_of y) s)
              | None -> acc)
        in
        let a' = Atom.subst m a in
        let js =
          List.filter (List.init nl ~f:Fn.id) ~f:(fun j ->
              let pos', b = lits.(j) in
              Bool.(pos = pos') && same a' b)
        in
        Hashtbl.set images_tbl ~key ~data:js;
        js
  in
  let verify (dropped, (sigma, fixed)) =
    (not (Map.is_empty sigma))
    && (not
          (Map.existsi sigma ~f:(fun ~key ~data:_ ->
               Set.mem fixed key || is_unknown key)))
    && (let rec kept_free k =
          k >= nl
          || (Set.mem dropped k
             || not (Array.exists tvs.(k) ~f:(Map.mem sigma)))
             && kept_free (k + 1)
        in
        kept_free 0)
    && Set.for_all dropped ~f:(fun k ->
           List.exists (images_of sigma k) ~f:(fun j -> not (Set.mem dropped j)))
  in
  let to_seed (dropped, (sigma, fixed)) =
    {
      js_dropped = dropped;
      js_binds = Map.to_alist sigma;
      js_fixed = Set.to_list fixed;
      js_var = var_of;
      js_atoms =
        lazy
          (let pick pos =
             Set.Poly.of_list
               (List.filter_map (Set.to_list dropped) ~f:(fun k ->
                    if Bool.(fst lits.(k) = pos) then Some (snd lits.(k)) else None))
           in
           (pick true, pick false));
    }
  in
  (* [linked k sigma fixed]: atom [k] has a variable that is neither bound
     nor fixed and shares a disjunct of the pure part with a bound variable.
     Such an atom is not forced into the closure, but if it stays, that
     variable stays read by an atom and the disjunct's image keeps it: a copy
     of a callee precondition applied at a copied argument that a linking
     equation ties to the bound variables is only dropped together with the
     rest of its copy. *)
  (* The pure part's disjuncts are read through an index from each variable
     to the disjuncts holding it: [near sigma] is the set of disjuncts that
     hold a bound variable, and an atom is linked when one of its free
     variables is in one of them -- the same condition as asking every
     disjunct whether it holds both a bound and a free variable, without
     walking the whole pure part for every open atom at every step of every
     closure (on resolvents of 13-16 atoms and 160-230 disjuncts that walk
     was a tenth of a joint condensation's time). *)
  let disj_of = Hashtbl.Poly.create () in
  List.iteri pure ~f:(fun i vs -> Set.iter vs ~f:(fun x -> Hashtbl.add_multi disj_of ~key:x ~data:i));
  let disjs_tbl = Hashtbl.create (module Int) in
  let disjs k =
    Hashtbl.find_or_add disjs_tbl k ~default:(fun () ->
        Option.value ~default:[] (Hashtbl.find disj_of (var_of k)))
  in
  (* [near sigma] marks the disjuncts holding a bound variable with a
     fresh stamp and returns it, rather than collecting them into a new
     table at every closure step: a mark is read only while the closure step
     that made it scans its open atoms, before it extends the closure *)
  let near_mark = Array.create ~len:(List.length pure) (-1) in
  let near_gen = ref 0 in
  let near sigma =
    incr near_gen;
    let g = !near_gen in
    Map.iter_keys sigma ~f:(fun x -> List.iter (disjs x) ~f:(fun d -> near_mark.(d) <- g));
    g
  in
  let linked k (sigma, fixed) near =
    Array.exists tvs.(k) ~f:(fun x ->
        (not (Map.mem sigma x))
        && (not (Set.mem fixed x))
        &&
        let g = Lazy.force near in
        List.exists (disjs x) ~f:(fun d -> near_mark.(d) = g))
  in
  let doomed =
    Option.map doomed ~f:(fun d (sigma, fixed) ->
        d
          ( Map.fold sigma ~init:Map.Poly.empty ~f:(fun ~key ~data acc ->
                Map.Poly.set acc ~key:(var_of key) ~data:(var_of data)),
            Set.fold fixed ~init:Set.Poly.empty ~f:(fun acc k -> Set.add acc (var_of k)) ))
  in
  let iplan p =
    Array.of_list
      (List.map p ~f:(function
        | JFail -> IFail
        | JFix vs -> IFix (List.map (Set.to_list vs) ~f:id_of)
        | JVar (x, ty) ->
            IVar (id_of x, Option.map ty ~f:(fun (y, b) -> (id_of y, b)))))
  in
  (* [joint_run_plan] over numbers *)
  let run_plan plan (sigma, fixed) =
    let rec go p sigma fixed =
      if p >= Array.length plan then Some (sigma, fixed)
      else
        match plan.(p) with
        | IFail -> None
        | IFix vs ->
            if List.exists vs ~f:(Map.mem sigma) then None
            else go (p + 1) sigma (List.fold vs ~init:fixed ~f:Set.add)
        | IVar (x, ty) -> (
            match Map.find sigma x with
            | Some y -> (
                match ty with
                | Some (y', _) when y = y' -> go (p + 1) sigma fixed
                | _ -> None)
            | None -> (
                match ty with
                | Some (y, true) ->
                    if x = y then go (p + 1) sigma (Set.add fixed x)
                    else if Set.mem fixed x || Map.mem sigma y then None
                    else go (p + 1) (Map.set sigma ~key:x ~data:y) (Set.add fixed y)
                | _ -> None))
    in
    go 0 sigma fixed
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
  let plans = Array.init nl ~f:(fun _ -> Array.create ~len:nl None) in
  let plan c d =
    match plans.(c).(d) with
    | Some p -> p
    | None ->
        let p = iplan (joint_plan ~unknowns (snd lits.(c)) (snd lits.(d))) in
        plans.(c).(d) <- Some p;
        p
  in
  let close i j =
    match run_plan (plan i j) (Int.Map.empty, Int.Set.empty) with
    | None -> None
    | Some st ->
        steps := 0;
        let images c dropped st k =
          let rec from d =
            if d >= nl then None
            else if
              d = c || Set.mem dropped d || (not (same_key c d))
              || !steps >= closure_steps
            then from (d + 1)
            else (
              incr steps;
              match run_plan (plan c d) st with
              | None -> from (d + 1)
              | Some st' -> (
                  match k st' with Some _ as r -> r | None -> from (d + 1)))
          in
          from 0
        in
        let rec first k ~f = if k >= nl then None else if f k then Some k else first (k + 1) ~f in
        let rec loop dropped keep ((sigma, _) as st) =
          if match doomed with Some d -> d st | None -> false then None else
          let dom_hit k = Array.exists tvs.(k) ~f:(Map.mem sigma) in
          let open_ k = (not (Set.mem dropped k)) && not (Set.mem keep k) in
          match first 0 ~f:(fun k -> (not (Set.mem dropped k)) && dom_hit k) with
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
              let near_st = lazy (near sigma) in
              match first 0 ~f:(fun k -> open_ k && linked k st near_st) with
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
  mutable refused_merge_only : int;
  mutable pattern_nf : int;
  mutable pattern_any : int;
  mutable pruned : int;
  mutable pattern_s : float;
  mutable pattern_bag_s : float;
  mutable named_s : float;
  mutable doomed_s : float;
  mutable doomed_n : int;
  mutable possible_hit : int;
  mutable occ_skipped : int;
  mutable key_s : float;
  mutable find_s : float;
  mutable miss_n : int;
  mutable miss_s : float;
  mutable bag_n : int;
  mutable pattern_hit : int;
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
    refused_merge_only = 0;
    pattern_nf = 0;
    pattern_any = 0;
    pruned = 0;
    pattern_s = 0.;
    pattern_bag_s = 0.;
    named_s = 0.;
    doomed_s = 0.;
    doomed_n = 0;
    possible_hit = 0;
    occ_skipped = 0;
    key_s = 0.;
    find_s = 0.;
    miss_n = 0;
    miss_s = 0.;
    bag_n = 0;
    pattern_hit = 0;
  }

(* [COAR_CONDENSE_DIAG] (instrument only): one stderr line per seed variable
   of [condense_pure]'s passes that spent more than 50 normalisations or found
   a condensation, and for a call that reached its normalisation budget its
   private variables and every disjunct's normal form.  The result is the same
   either way. *)
(* evaluated now: a [lazy] forced by two domains at once raises [Lazy.Undefined] *)
let condense_diag =
  Lazy.from_val (Option.is_some (Stdlib.Sys.getenv_opt "COAR_CONDENSE_DIAG"))
let condense_diag_on () = Lazy.force condense_diag

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
  p.refused_ok_shape <- 0;
  p.refused_merge_only <- 0;
  p.pattern_nf <- 0;
  p.pattern_any <- 0;
  p.pruned <- 0;
  p.pattern_s <- 0.;
  p.pattern_bag_s <- 0.;
  p.named_s <- 0.;
  p.doomed_s <- 0.;
  p.doomed_n <- 0;
  p.possible_hit <- 0;
  p.occ_skipped <- 0;
  p.key_s <- 0.;
  p.find_s <- 0.;
  p.miss_n <- 0;
  p.miss_s <- 0.;
  p.bag_n <- 0;
  p.pattern_hit <- 0

let condense_profile_str () =
  let p = condense_profile in
  let ph k name =
    sprintf "%s: %.2fs nf=%d/%.2fs incl=%d/%.2fs search=%d" name p.phase_s.(k)
      p.nf_n.(k) p.nf_s.(k) p.incl_n.(k) p.incl_s.(k) p.search_n.(k)
  in
  sprintf
    "%s | %s seeds=%d searched=%d in-f=%.2fs refused: budget=%d binds=%d ok=%d \
     (no same-shaped live disjunct=%d) merge-only=%d | %s | merge-patterns: nf=%d (remembered=%d) any=%d pruned=%d \
     doomed=%d/%.2fs patterns=%.2fs bags=%.2fs named=%.2fs possible-hits=%d occ-skipped=%d \
     cbag: n=%d key=%.2fs find=%.2fs miss=%d/%.2fs"
    (ph 0 "setup") (ph 1 "joint") p.seeds p.seeds_searched p.seed_f_s
    p.refused_budget p.refused_binds p.refused_ok p.refused_ok_shape
    p.refused_merge_only (ph 2 "passes")
    p.pattern_nf p.pattern_hit p.pattern_any p.pruned p.doomed_n p.doomed_s p.pattern_s
    p.pattern_bag_s p.named_s p.possible_hit p.occ_skipped p.bag_n p.key_s p.find_s p.miss_n p.miss_s

(* Hash table keys of [condense_pure]'s search, over integers only, compared
   and hashed by functions of their own.  The polymorphic hash reads at most
   ten meaningful values of a key, so the keys of failed search calls -- the
   list of touched disjuncts, tens long and growing by extension -- shared a
   few hash values, and every lookup compared them polymorphically along the
   bucket.  Equality is the same structural equality as before and the tables
   are only looked up and written, never iterated, so which keys collide shows
   in no result: the search asks the same images in the same order. *)
module CondenseKeys = struct
  let hash_ints init l =
    List.fold l ~init ~f:(fun h x -> (h * 31) + x) land Int.max_value

  (* a disjunct and the bindings of its bound variables *)
  module Image = struct
    type t = int * (int * int) list

    let compare (i, l) (j, m) =
      match Int.compare i j with
      | 0 ->
          List.compare
            (fun (a, b) (c, d) ->
              match Int.compare a c with 0 -> Int.compare b d | r -> r)
            l m
      | r -> r

    let hash (i, l) =
      List.fold l ~init:i ~f:(fun h (a, b) -> (((h * 31) + a) * 31) + b)
      land Int.max_value

    let sexp_of_t _ = Sexp.Atom "image"
  end

  (* touched disjuncts and the variable chosen *)
  module Call = struct
    type t = int list * int

    let compare (l, u) (m, v) =
      match List.compare Int.compare l m with 0 -> Int.compare u v | r -> r

    let hash (l, u) = hash_ints u l
    let sexp_of_t _ = Sexp.Atom "call"
  end

  module States = struct
    type t = int array

    let compare = Array.compare Int.compare
    let hash a = hash_ints 0 (Array.to_list a)
    let sexp_of_t _ = Sexp.Atom "states"
  end
end

(* [condense_dt_symbols phi]: the datatype constructors, selectors and
   testers [phi] mentions, by name ([c:k], [s:f], [t:k], a tester and its
   negation both [t:k]), embedded formulas included. *)
let condense_dt_symbols phi =
  let fs =
    Set.to_list (Formula.funsyms_of phi)
    |> List.filter_map ~f:(function
         | T_dt.DTCons (name, _, _) -> Some ("c:" ^ name)
         | T_dt.DTSel (name, _, _) -> Some ("s:" ^ name)
         | _ -> None)
  in
  let ps =
    Set.to_list (Formula.predsyms_of phi)
    |> List.filter_map ~f:(function
         | T_dt.IsCons (name, _) | T_dt.NotIsCons (name, _) -> Some ("t:" ^ name)
         | _ -> None)
  in
  String.Set.of_list (fs @ ps)

(* [condense_cbag phi]: the multiset (its sorted tokens joined by spaces:
   one string, which a hash table's hash reads whole, where a list's hash
   read only its first tokens, the same in most bags) of the printed
   tokens of [phi] with every free and every bound variable printed as [_]
   and the brackets taken off each token, together with the multiset of the
   numbers of times each free variable is printed.  An injective renaming of
   free variables changes none of it, nor does a reordering of the operands
   of a sum, a conjunction or a disjunction (the tokens are only permuted,
   and a bracket that a reordering moves from one operand to another is not
   part of any token).  A renaming that merges two variables changes the
   occurrence counts, which is what tells a disjunct whose image repeats a
   variable from its same-shaped siblings.  It forgets more than the
   formula, which is what the merge-pattern prune of [condense_pure] needs:
   equal formulas up to such changes have equal bags.  The variables [keep]
   holds are printed by name instead, so the bag is kept by an injective
   renaming that fixes them. *)
let condense_cbag =
  let rels = String.Set.of_list [ "<"; ">"; "<="; ">="; "<>" ] in
  fun ?(keep = fun _ -> false) phi ->
    let names = Formula.names_spelled_in phi in
    let raw = Formula.str_of phi in
    let rec choose prefix =
      if Set.exists names ~f:(fun x ->
           String.is_prefix (Ident.name_of_tvar x) ~prefix)
         || String.is_substring raw ~substring:prefix
      then choose (prefix ^ "_") else prefix
    in
    let bound_prefix = choose "#cbv" and free_prefix = choose "#cbf" in
    let bound = Str.regexp (Str.quote bound_prefix ^ "[0-9]+") in
    let free = Str.regexp (Str.quote free_prefix ^ "[0-9]+") in
    let phi =
      if Set.is_empty (Formula.quantified_sort_env_of phi) then phi
      else
        let k = ref 0 in
        Formula.aconv_tvar_norm
          (fun () ->
            incr k;
            Ident.Tvar (sprintf "%s%d" bound_prefix !k))
          phi
    in
    let erase =
      Map.Poly.of_alist_exn
      @@ List.filter_mapi (Set.to_list (Formula.term_sort_env_of phi)) ~f:(fun k (x, s) ->
             if keep x then None
             else Some (x, Term.mk_var (Ident.Tvar (sprintf "%s%d" free_prefix k)) s))
    in
    let str = Formula.str_of (Formula.subst erase phi) in
    let counts = Hashtbl.Poly.create () in
    let pos = ref 0 in
    (try
       while true do
         let p = Str.search_forward free str !pos in
         Hashtbl.incr counts (Str.matched_string str);
         pos := p + 1
       done
     with Stdlib.Not_found -> ());
    let occ = List.map (Hashtbl.data counts) ~f:(sprintf "#occ:%d") in
    occ
    @ (Str.global_replace free "_" str
    |> Str.global_replace bound "_"
    |> String.split ~on:' '
    |> List.filter_map ~f:(fun tok ->
           let tok = String.filter tok ~f:(fun c -> not (Char.equal c '(' || Char.equal c ')')) in
           let tok =
             if Set.mem rels tok then tok
             else
               String.lstrip ~drop:(Char.equal '<') tok
               |> String.rstrip ~drop:(Char.equal '>')
           in
           if String.is_empty tok then None else Some tok))
    |> List.sort ~compare:String.compare
    |> String.concat ~sep:" "

(* [condense_cbag_key ~keep phi] records both a canonical formula and the
   names/sorts of the free variables the bag erases, in that formula. Free
   variables outside [keep] are renamed injectively to [<p><k>], in first
   occurrence order, with [p] absent from the input's names. The free-variable
   metadata distinguishes such a generated name from the same spelling kept
   literally in another formula: an erased [x] and a retained [#cbk0] must
   never share a key merely because both canonical formulas print [#cbk0].
   Equal keys preserve the canonical formula and which of its variables the
   bag erases; sorts and all retained symbols remain part of the key too.
   The rank order affects cache reuse only, not the validity of a shared key.
   No global fresh-variable counter is read or advanced. *)
let condense_cbag_key ~keep phi =
  let names = Formula.names_spelled_in phi in
  let rec choose prefix =
    if Set.exists names ~f:(fun x -> String.is_prefix (Ident.name_of_tvar x) ~prefix)
    then choose (prefix ^ "_")
    else prefix
  in
  let prefix = choose "#cbk" in
  let free =
    Set.fold (Formula.term_sort_env_of phi) ~init:Map.Poly.empty
      ~f:(fun acc (x, s) -> if keep x then acc else Map.Poly.set acc ~key:x ~data:s)
  in
  if Map.Poly.is_empty free then (phi, [])
  else
    let ren = ref Map.Poly.empty in
    let k = ref 0 in
    Formula.iter_term phi ~f:(function
      | Term.Var (x, _, _) when Map.Poly.mem free x && not (Map.Poly.mem !ren x) ->
          ren :=
            Map.Poly.set !ren ~key:x
              ~data:
                (Term.mk_var
                   (Ident.Tvar (sprintf "%s%d" prefix !k))
                   (Map.Poly.find_exn free x));
          incr k
      | _ -> ());
    (* Retain the erasure role even for a variable the traversal did not
       rename. This list is ordered by canonical names, not original names. *)
    let erased =
      List.map (Map.Poly.to_alist free) ~f:(fun (x, sort) ->
          match Map.Poly.find !ren x with
          | Some (Term.Var (y, _, _)) -> y, sort
          | _ -> x, sort)
      |> List.sort ~compare:Poly.compare
    in
    (Formula.subst !ren phi, erased)

(* [condense_cbag_memo] (on by default): [condense_pure] computes the bags of
   its pattern images and of its disjuncts through a table keyed by
   [condense_cbag_key], so an image that is an injective renaming of one
   already bagged (the images of renamed copies of a disjunct, which are what
   condensation removes) is not printed again.  Exact: the bag returned is
   the bag of the formula asked (the key's contract and the bag's invariance),
   and computing a bag draws no fresh name, so the condensation asks the same
   questions with the same names. *)
let condense_cbag_memo = Atomic.make true

(* [condense_cbag_memo_mutant] (for tests only): the key keeps the free
   variables' names out of it entirely, so formulas that differ by a merge of
   two variables share a key; not exact, and the property test must tell it
   apart *)
let condense_cbag_memo_mutant = ref false

(* the bag of [phi] through [tbl] ([condense_cbag_memo]); a key the table
   cannot hash or compare (a value the polymorphic hash rejects) is computed
   directly *)
let condense_cbag_through tbl ?(keep = fun _ -> false) phi =
  if not (Atomic.get condense_cbag_memo) then condense_cbag ~keep phi
  else
    let p = condense_profile in
    p.bag_n <- p.bag_n + 1;
    let tk = Common.Clock.now_s () in
    let key =
      if !condense_cbag_memo_mutant then
        condense_cbag_key ~keep:(fun _ -> false)
          (Formula.subst
             (Map.Poly.of_alist_exn
                (List.map (Set.to_list (Formula.term_sort_env_of phi)) ~f:(fun (x, s) ->
                     (x, Term.mk_var (Ident.Tvar "#cbm") s))))
             phi)
      else condense_cbag_key ~keep phi
    in
    let tf = Common.Clock.now_s () in
    p.key_s <- p.key_s +. (tf -. tk);
    let found = try `F (Hashtbl.find tbl key) with Invalid_argument _ -> `Bad in
    p.find_s <- p.find_s +. (Common.Clock.now_s () -. tf);
    match found with
    | `Bad -> condense_cbag ~keep phi
    | `F (Some b) -> b
    | `F None ->
        let tm = Common.Clock.now_s () in
        let b = condense_cbag ~keep phi in
        p.miss_n <- p.miss_n + 1;
        p.miss_s <- p.miss_s +. (Common.Clock.now_s () -. tm);
        (try Hashtbl.set tbl ~key ~data:b with Invalid_argument _ -> ());
        b

(* [condense_premise_ok ~fresh phi] checks, on one formula, the two facts
   about [Evaluator.simplify] followed by [Normalizer.normalize] (call it
   [nf]) that the merge-pattern prune of [condense_pure] rests on: (P1) the
   datatype constructors, selectors and testers of [nf phi] are among those
   of [phi]; (P2) for the renaming [rho] of every free variable of [phi] to a
   fresh variable of its sort ([fresh] gives the name for the [k]-th), the
   bags [condense_cbag (nf (phi rho))] and [condense_cbag (nf phi)] are
   equal.  Returns the two outcomes and whether, beyond (P2),
   [nf (phi rho)] is syntactically [(nf phi) rho]. *)
let condense_premise_ok ~fresh phi =
  let nf l = Normalizer.normalize @@ Evaluator.simplify l in
  let c = nf phi in
  let p1 = Set.is_subset (condense_dt_symbols c) ~of_:(condense_dt_symbols phi) in
  let env = Set.to_list (Formula.term_sort_env_of phi) in
  let ren =
    Map.Poly.of_alist_exn
    @@ List.mapi env ~f:(fun k (x, s) -> (x, Term.mk_var (fresh k) s))
  in
  let c' = nf (Formula.subst ren phi) in
  let p2 = Stdlib.(condense_cbag c' = condense_cbag c) in
  let syn =
    try Stdlib.(Formula.str_of c' = Formula.str_of (Formula.subst ren c))
    with Invalid_argument _ -> false
  in
  (p1, p2, syn)

(* [COAR_CONDENSE_PREMISE] (instrument only): [condense_premise_ok] asked of
   every disjunct [condense_pure] condenses and of every merge-pattern image
   it normalises, with a tally on stderr every 2,000 formulas and at exit
   (formulas checked, (P1)
   failures, (P2) failures, syntactic agreements); a failure prints the
   formula.  The result is the same either way. *)
let condense_premise_counts = Array.create ~len:4 0

(* evaluated now: a [lazy] forced by two domains at once raises [Lazy.Undefined] *)
let condense_premise_on =
  Lazy.from_val
    (Option.is_some (Stdlib.Sys.getenv_opt "COAR_CONDENSE_PREMISE")
    && (Stdlib.at_exit (fun () ->
            let c = condense_premise_counts in
            eprintf "[condense-premise] checked=%d p1-fail=%d p2-fail=%d syntactic=%d\n%!"
              c.(0) c.(1) c.(2) c.(3));
        true))

let condense_premise_probe phi =
  if Lazy.force condense_premise_on then (
    let p1, p2, syn =
      condense_premise_ok ~fresh:(fun k -> Ident.Tvar (sprintf "#cpr%d" k)) phi
    in
    let c = condense_premise_counts in
    c.(0) <- c.(0) + 1;
    if not p1 then (
      c.(1) <- c.(1) + 1;
      eprintf "[condense-premise] P1 fails on %s\n%!" (Formula.str_of phi));
    if not p2 then (
      c.(2) <- c.(2) + 1;
      eprintf "[condense-premise] P2 fails on %s\n%!" (Formula.str_of phi));
    if syn then c.(3) <- c.(3) + 1;
    if c.(0) mod 2000 = 0 then
      eprintf "[condense-premise] checked=%d p1-fail=%d p2-fail=%d syntactic=%d\n%!" c.(0)
        c.(1) c.(2) c.(3))

(* [clear_nonempty t] empties [t].  Base's [Hashtbl.clear] walks the whole
   bucket array, which keeps the size the table once grew to, so clearing an
   empty table that a search had filled earlier costs its capacity; an empty
   table needs nothing done.  The joint condensation clears two tables for
   every closure it is handed, most of them refused before either is
   written. *)
let clear_nonempty t = if Hashtbl.length t > 0 then Hashtbl.clear t

(* [condense_joint_merge_only] (off by default): when on, the joint
   hand-over of [condense_pure] does not search a seed that touches a large
   disjunct whose image could be accepted only through a merge of its
   variables (see [condense_pure]).  Off because the refusal is not exact:
   it can miss a condensation, and it stays off until a census shows it
   changes none on the corpora the default is judged by.  The
   [COAR_CONDENSE_AB_MERGE_ONLY] instrument of the predicate eliminator runs
   each condensation both ways. *)
let condense_joint_merge_only = Atomic.make false

(* [condense_occ_filter] (on by default): the merge-pattern prune of
   [condense_pure] skips the bag of a pattern image whose free-variable
   occurrence profile ([condense_occ_profile]) is no input disjunct's, since
   such an image has no input disjunct's bag.  Exact: the profile is a function
   of the bag where both are defined (see [condense_occ_profile]); an image
   whose bag would be found is never skipped, so the prune's every answer is
   the same, and bagging draws no fresh name.  [COAR_CONDENSE_OCC_FILTER_OFF]
   (instrument only) starts it off, to time a run without it. *)
let condense_occ_filter =
  Atomic.make (Option.is_none (Stdlib.Sys.getenv_opt "COAR_CONDENSE_OCC_FILTER_OFF"))

(* [condense_occ_profile phi]: the occurrence counts of the free term
   variables of [phi], sorted, as one string, or [None] outside the fragment
   where it is shown to be read off [condense_cbag phi].  In the fragment --
   atoms of a predicate symbol or variable over terms built from variables,
   formulas embedded as Boolean terms (read in the same scope) and function
   symbols other than an uninterpreted function head or an array lambda
   (which carry a name or a binder of their own),
   under negation, binary connectives and universal and existential
   quantifiers; no [let] -- a free variable is printed exactly at its free occurrences, once
   each, and the bag reads one occurrence token per free variable, the number
   of times its placeholder is printed (the facts the bag memo's renaming
   invariance rests on).  So the bag's [#occ:] tokens are the profile's
   counts, provided the print itself has no token beginning with [#occ:]:
   the caller asks that of the clause it condenses (no such text and no
   string literal in its print), and normalising introduces no such symbol.
   Hence equal bags have equal profiles.

   An application of a function variable [\f t1 .. tn] is in the fragment
   too, under three conditions that make its head behave like a term
   variable in the bag: the head is not bound by a quantifier of [phi], it
   has one function sort wherever it is applied, and no free term variable
   has its name.  Then the bag treats the head as it treats a free variable
   unless the head is a defined function ([defined_fvars]):
   [Formula.term_sort_env_of] collects it (with its function sort), so the
   bag's erasing substitution renames it to a placeholder, and the printer
   prints the head as a backslash followed by that placeholder at each
   application and nowhere else; the head is counted once per application.
   A defined function is not collected, so it is printed by its name, which
   is no placeholder, and it is not counted.  Without the conditions the
   function returns [None]: a bound head may be renamed by the bag's
   binder normalisation, and a name with two sorts makes the bag's erasing
   map raise, which skipping the bag would hide. *)
(* instrument only: why the last call's filter was not used *)
let condense_occ_why = ref ""

let condense_occ_profile phi =
  let exception Outside in
  let outside what = condense_occ_why := what; raise Outside in
  let counts = Hashtbl.Poly.create () in
  (* the free term variables' names, and the function sort of each head of an
     application of a function variable, to tell at the end whether one name
     stands for two things *)
  let var_names = Hash_set.Poly.create () in
  let heads = Hashtbl.Poly.create () in
  let rec term bvs = function
    | Term.Var (x, _, _) ->
        if not (Set.mem bvs x) then (
          Hashtbl.incr counts x;
          Hash_set.add var_names x)
    | Term.FunApp (FVar (x, sargs, sret), args, _) ->
        if Set.mem bvs x then outside "fvar-bound";
        let s = Sort.mk_fun (sargs @ [ sret ]) in
        (match Hashtbl.find heads x with
        | None -> Hashtbl.set heads ~key:x ~data:s
        | Some s' ->
            if not (try Stdlib.(s = s') with Invalid_argument _ -> false) then
              outside "fvar-sorts");
        if not (Hash_set.mem defined_fvars x) then Hashtbl.incr counts x;
        List.iter args ~f:(term bvs)
    | Term.FunApp (T_bool.Formula phi, args, _) ->
        formula bvs phi;
        List.iter args ~f:(term bvs)
    | Term.FunApp (T_array.ALambda _, _, _) -> outside "alambda"
    | Term.FunApp (_, args, _) -> List.iter args ~f:(term bvs)
    | Term.LetTerm _ -> outside "let-term"
  and formula bvs = function
    | Formula.Atom (Atom.App ((Predicate.Psym _ | Predicate.Var _), args, _), _) ->
        List.iter args ~f:(term bvs)
    | Formula.Atom (Atom.App (Predicate.Fixpoint _, _, _), _) -> outside "fixpoint"
    | Formula.Atom ((Atom.True _ | Atom.False _), _) -> ()
    | Formula.UnaryOp (_, phi, _) -> formula bvs phi
    | Formula.BinaryOp (_, l, r, _) ->
        formula bvs l;
        formula bvs r
    | Formula.Bind ((Formula.Forall | Formula.Exists), ps, phi, _) ->
        formula (Set.union bvs (Set.Poly.of_list (List.map ps ~f:fst))) phi
    | Formula.Bind (Formula.Random _, _, _, _) -> outside "random"
    | Formula.LetFormula _ | Formula.LetRec _ -> outside "let"
  in
  match formula Set.Poly.empty phi with
  | exception Outside -> None
  | () when Hashtbl.existsi heads ~f:(fun ~key ~data:_ -> Hash_set.mem var_names key) ->
      condense_occ_why := "fvar-var";
      None
  | () ->
      Some
        (Hashtbl.data counts |> List.sort ~compare:Int.compare
        |> List.map ~f:Int.to_string |> String.concat ~sep:",")

(* [condense_roles_reference shape_strs occs]: the roles of [condense_pure]
   (see there), computed as first written: for each disjunct and each of its
   variables [k], the whole printed normal form is rewritten with [k] marked,
   then cut and sorted.  A disjunct of [L] characters and [V] variables costs
   [V] regular-expression passes over [L] characters, and the keys, lists of
   strings that share long sorted prefixes, are hashed by the polymorphic
   hash, which reads only their first few elements.  Kept as the reference
   [condense_roles_by_pieces_of] is checked against
   ([COAR_CONDENSE_ROLES_CHECK]) and for [condense_roles_by_pieces] off. *)
let condense_roles_reference shape_strs occs =
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


(* [condense_roles_by_pieces_of shape_strs occs]: the same roles as
   [condense_roles_reference], with the same numbers, at a cost per variable
   that depends on the pieces holding it rather than on the whole print.

   Why the pieces suffice.  The pieces are cut at [" + "] and at a
   comparison operator with a space on each side; a placeholder [__cpvN__]
   holds none of those characters, and neither does the ["U"] or ["_"] it is
   printed as.  So marking the placeholders commutes with cutting: the pieces
   of the marked print are the marked pieces of the unmarked one, in the same
   order, and a piece without [k] prints as its base (every placeholder
   ["_"]) whatever [k] is.  Number every piece string met in the call (a
   bijection between strings and numbers).  The reference's key for [k] in
   disjunct [i] is then the multiset [M = B - R + A] of numbers, where [B] is
   the bases of [i]'s pieces, [R] the bases of the pieces holding [k] and [A]
   those pieces marked for [k], and two variables share a role exactly when
   their multisets are equal.

   How equality is decided without building [M].  Each disjunct's [B] is
   numbered as a multiset.  A key is looked up by a sum of its numbers'
   hashes, [hash B - hash R + hash A], and compared exactly with each key of
   the same sum: when both come from the same [B], [B - R + A = B - R' + A']
   iff [R' + A = R + A'], a comparison of the few pieces holding the two
   variables ([R] is contained in [B]); otherwise both multisets are built
   and compared.  The second case is rare: replacing every ["U"] by ["_"]
   maps a marked piece to its base, so two equal keys have bases equal up to
   literal ["U"] characters in the print, and without such a character equal
   keys have the same [B].

   Roles are numbered in the order their key is first met, which visits the
   disjuncts and their variables in the reference's order, so the numbers
   agree.  Cost: one cut and one placeholder scan per disjunct and a sort of
   its piece numbers; per variable, the pieces holding it are printed and
   sorted.  The reference rewrote, cut and sorted the whole print once per
   variable and hashed lists of strings sharing long prefixes by their first
   few elements: on a print of 10,000 characters, 811 pieces and 56
   variables that is 56 passes over all of it. *)
let condense_roles_by_pieces_of shape_strs occs =
  let re = Str.regexp "__cpv\\([0-9]+\\)__" in
  let plus = Str.regexp_string " + " in
  let rel = Str.regexp " \\(>=\\|<=\\|!=\\|=\\|>\\|<\\) " in
  let piece_ids = Hashtbl.create (module String) in
  let piece_id s =
    match Hashtbl.find piece_ids s with
    | Some id -> id
    | None ->
        let id = Hashtbl.length piece_ids in
        Hashtbl.set piece_ids ~key:s ~data:id;
        id
  in
  let base_ids = Hashtbl.create (module String) in
  let mix (x : int) = Hashtbl.hash x in
  let sum = List.fold ~init:0 ~f:(fun acc x -> acc + mix x) in
  let sorted l = List.sort l ~compare:Int.compare in
  (* the keys met so far, by their sum: base multiset number, [R], [A], the
     multiset itself when asked for, and the role number *)
  let keys = Hashtbl.create (module Int) in
  let n_roles = ref 0 in
  Array.mapi shape_strs ~f:(fun i -> function
    | None -> []
    | Some str -> (
        let ks =
          match occs.(i) with
          | None -> []
          | Some oi -> List.dedup_and_sort ~compare:Int.compare (Array.to_list oi)
        in
        match ks with
        | [] -> []
        | _ ->
            let pieces =
              Array.of_list (Str.split plus (Str.global_replace rel " + \\1 + " str))
            in
            (* each piece as the text between its placeholders and the
               placeholders' numbers, scanned as [Str.global_substitute]
               scans: each match from the end of the previous one *)
            let parsed =
              Array.map pieces ~f:(fun p ->
                  let segs = ref [] and vs = ref [] and pos = ref 0 in
                  (try
                     while true do
                       let b = Str.search_forward re p !pos in
                       let e = Str.match_end () in
                       let v = Int.of_string (Str.matched_group 1 p) in
                       segs := String.sub p ~pos:!pos ~len:(b - !pos) :: !segs;
                       vs := v :: !vs;
                       pos := e
                     done
                   with Stdlib.Not_found -> ());
                  segs := String.subo p ~pos:!pos :: !segs;
                  (Array.of_list (List.rev !segs), Array.of_list (List.rev !vs)))
            in
            let render k (segs, vs) =
              let b = Buffer.create 64 in
              Array.iteri vs ~f:(fun j v ->
                  Buffer.add_string b segs.(j);
                  Buffer.add_string b (if v = k then "U" else "_"));
              Buffer.add_string b segs.(Array.length vs);
              Buffer.contents b
            in
            (* placeholder numbers are variable indices, never negative *)
            let base = Array.map parsed ~f:(fun pv -> piece_id (render (-1) pv)) in
            let base_sorted = Array.sorted_copy base ~compare:Int.compare in
            let bid =
              let key =
                String.concat_array ~sep:"," (Array.map base_sorted ~f:Int.to_string)
              in
              match Hashtbl.find base_ids key with
              | Some id -> id
              | None ->
                  let id = Hashtbl.length base_ids in
                  Hashtbl.set base_ids ~key ~data:id;
                  id
            in
            let hb = Array.fold base ~init:0 ~f:(fun acc x -> acc + mix x) in
            (* the pieces holding each variable, each piece once *)
            let holders = Hashtbl.create (module Int) in
            Array.iteri parsed ~f:(fun j (_, vs) ->
                Array.iter vs ~f:(fun v ->
                    Hashtbl.update holders v ~f:(function
                      | Some (j' :: _ as js) when j' = j -> js
                      | Some js -> j :: js
                      | None -> [ j ])));
            List.map ks ~f:(fun k ->
                let js = Option.value ~default:[] (Hashtbl.find holders k) in
                let r = List.map js ~f:(fun j -> base.(j)) in
                let a = List.map js ~f:(fun j -> piece_id (render k parsed.(j))) in
                let h = hb - sum r + sum a in
                let ms =
                  lazy
                    (let m = Array.copy base in
                     List.iter2_exn js a ~f:(fun j x -> m.(j) <- x);
                     Array.sort m ~compare:Int.compare;
                     m)
                in
                let same (bid', r', a', ms', _) =
                  if bid = bid' then
                    List.equal Int.equal (sorted (r' @ a)) (sorted (r @ a'))
                  else Array.equal Int.equal (Lazy.force ms) (Lazy.force ms')
                in
                let entries = Option.value ~default:[] (Hashtbl.find keys h) in
                match List.find entries ~f:same with
                | Some (_, _, _, _, id) -> (k, id)
                | None ->
                    let id = !n_roles in
                    incr n_roles;
                    Hashtbl.set keys ~key:h ~data:((bid, r, a, ms, id) :: entries);
                    (k, id))))

(* [condense_roles_by_pieces] (on by default): [condense_pure] computes its
   roles by [condense_roles_by_pieces_of] rather than
   [condense_roles_reference]; the two return the same array (see the former).
   [COAR_CONDENSE_ROLES_REFERENCE] (instrument only) starts it off, to time a
   run with the reference; [COAR_CONDENSE_ROLES_CHECK] (instrument only)
   computes both on every call and stops the process with both printed where
   they differ. *)
let condense_roles_by_pieces =
  Atomic.make (Option.is_none (Stdlib.Sys.getenv_opt "COAR_CONDENSE_ROLES_REFERENCE"))

let condense_roles_by_pieces_of shape_strs occs =
  let r = condense_roles_by_pieces_of shape_strs occs in
  (if Option.is_some (Stdlib.Sys.getenv_opt "COAR_CONDENSE_ROLES_CHECK") then
     let r0 = condense_roles_reference shape_strs occs in
     if not (Array.equal (List.equal (Tuple2.equal ~eq1:Int.equal ~eq2:Int.equal)) r r0) then (
       Array.iteri shape_strs ~f:(fun i s ->
           eprintf "[condense-roles] D%d %s\n  new: %s\n  ref: %s\n" i
             (Option.value ~default:"-" s)
             (String.concat ~sep:" " (List.map r.(i) ~f:(fun (k, id) -> sprintf "%d:%d" k id)))
             (String.concat ~sep:" " (List.map r0.(i) ~f:(fun (k, id) -> sprintf "%d:%d" k id))));
       failwith "condense_roles_by_pieces_of differs from the reference"));
  r

(* [condense_formula_hash phi]: a hash of a formula for the tables of
   [condense_pure] whose keys are formulas and whose equality is polymorphic
   comparison ([condense_formula_tbl]).  Why not the generic deep hash: it
   reads the first 100 meaningful nodes breadth first, and on a quantified
   formula whose variables carry datatype sorts those are spent inside the
   sort trees, which renamed near-copies share; so the images of one
   disjunct under different renamings fell into a few buckets and every
   lookup compared formulas in a bucket.  This hash walks the formula in
   pre-order and reads its connectives, binders' variable names, predicate
   and function symbols and variable names, never a variable's or binder's
   sort and never an [info] field, and stops after [condense_formula_hash_budget]
   nodes.
   Contract (consistency with the table's equality): if [Stdlib.compare a b
   = 0] then [condense_formula_hash a = condense_formula_hash b].  Proof: the
   result is computed by structural recursion and reads, of its argument,
   only constructor tags, the fields it descends into, and [Hashtbl.hash] of
   names, operators, binders and symbols; the budget is a count of nodes
   visited in a fixed order, so it too is a function of the structure.  Two
   values that compare equal have the same constructors and equal fields
   everywhere, hence the same reads (for [Hashtbl.hash] on a field: it is
   consistent with structural equality, normalising floats and calling a
   custom block's own hash, as the generic deep hash already assumed of these
   keys).  So equal keys get equal hashes; unequal keys may collide, which
   costs a comparison, never an answer.  The result is non-negative. *)
let condense_formula_hash_budget = 256

let condense_formula_hash (phi : Formula.t) : int =
  let h = ref 17 and n = ref 0 in
  let mix x = h := ((!h * 65599) + x) land Int.max_value in
  let visit () =
    incr n;
    !n <= condense_formula_hash_budget
  in
  let rec term t =
    if visit () then
      match t with
      | Term.Var (Ident.Tvar x, _, _) ->
          mix 1;
          mix (String.hash x)
      | Term.FunApp (T_bool.Formula phi, args, _) ->
          mix 2;
          formula phi;
          List.iter args ~f:term
      | Term.FunApp (FVar (Ident.Tvar x, _, _), args, _) ->
          mix 3;
          mix (String.hash x);
          List.iter args ~f:term
      | Term.FunApp (sym, args, _) ->
          mix 4;
          mix (Stdlib.Hashtbl.hash sym);
          List.iter args ~f:term
      | Term.LetTerm (Ident.Tvar x, _, def, body, _) ->
          mix 5;
          mix (String.hash x);
          term def;
          term body
  and atom = function
    | Atom.True _ -> mix 6
    | Atom.False _ -> mix 7
    | Atom.App (pred, args, _) ->
        (match pred with
        | Predicate.Var (Ident.Pvar p, _) ->
            mix 8;
            mix (String.hash p)
        | Predicate.Psym sym ->
            mix 9;
            mix (Stdlib.Hashtbl.hash sym)
        | Predicate.Fixpoint _ -> mix 10);
        List.iter args ~f:term
  and formula phi =
    if visit () then
      match phi with
      | Formula.Atom (a, _) -> atom a
      | Formula.UnaryOp (op, phi1, _) ->
          mix 11;
          mix (Stdlib.Hashtbl.hash op);
          formula phi1
      | Formula.BinaryOp (op, phi1, phi2, _) ->
          mix 12;
          mix (Stdlib.Hashtbl.hash op);
          formula phi1;
          formula phi2
      | Formula.Bind (binder, senv, phi1, _) ->
          mix 13;
          (match binder with
          | Formula.Forall -> mix 14
          | Formula.Exists -> mix 15
          | Formula.Random _ -> mix 16);
          List.iter senv ~f:(fun (Ident.Tvar x, _) -> mix (String.hash x));
          formula phi1
      | Formula.LetFormula (Ident.Tvar x, _, def, phi1, _) ->
          mix 17;
          mix (String.hash x);
          term def;
          formula phi1
      | Formula.LetRec (_, phi1, _) ->
          mix 18;
          formula phi1
  in
  formula phi;
  !h

(* A table keyed by formulas, compared polymorphically, hashed by
   [condense_formula_hash]; consistent by that function's contract. *)
let condense_formula_tbl () =
  Hashtbl.Using_hashable.create
    ~hashable:
      {
        Base.Hashable.hash = condense_formula_hash;
        compare = Stdlib.compare;
        sexp_of_t = (fun _ -> Sexp.Atom "<formula>");
      }
    ()

(* [condense_pattern_memo] (off by default; set from
   [condensation.pure.pattern_memo]): what the merge-pattern prune of
   [condense_pure] reads of a pattern image, remembered across its calls in
   this domain.  A pattern image is a disjunct [d] of the clause under a
   renaming [ren] of some of its variables to variables of their sorts; the
   prune reads of its normal form [c] (under the call's binder-renaming mode
   [alpha]) only whether [c] is [false], [condense_occ_profile c] and
   [condense_cbag c], and, when a live disjunct has the same bag, the bag of
   [c] with some variables kept by name.  The first three are remembered,
   keyed by [d] (compared structurally), [ren] (as a list of name pairs with
   the target's sort, sorted by source name) and [alpha]; the last is
   computed from [c] again when it is asked for.

   Contract of the remembered values: equal to what the call would compute.
   Remembered is only an entry whose image and normal form were computed
   without drawing a fresh name ([Ident.fresh_stamp] unchanged; a
   capture-avoiding substitution or the simplifier may draw), and only while
   the function and datatype environments are the values they were when it
   was stored (the tables are emptied when either is replaced).  The image is
   a function of [d] and [ren]; simplification and normalisation are
   functions of the formula, the two environments and switches fixed at
   start-up; the profile and the bag are functions of the normal form.  So a
   remembered entry is what a recomputation would give, and skipping that
   recomputation leaves every later fresh name as it was.  The caller still
   charges one normalisation per pattern, remembered or not, so the budgets
   cut the search where they did and the condensation is the same.

   Kept: two generations of [condense_pattern_memo_gen] entries per mode,
   the older dropped when the newer fills; the strings are interned per
   generation pair, since few distinct profiles and bags recur.

   Why: successive resolvents of one predicate share most of their pure
   parts, and the searches that spend each condensation's whole budget
   normalise the same pattern images again from call to call: on large
   resolvents of Rust-derived inputs about half of each call's pattern
   images had been normalised by an earlier call, and the pattern images
   were most of the condensation's time.

   Off by default, and off it costs nothing: [condense_pure] reads the switch
   once per call and, when it is off, allocates no table, no key, no entry
   and no hash array, and makes the calls it made before the memo existed.
   Why off: on Rust-derived inputs whose condensation is their open phase
   the memo cut the condensation's time by at most a quarter, within the
   run-to-run spread on most of them, answered no further input, and raised
   the peak resident size from about 0.5 GB to 0.9-1.6 GB (the larger
   generation sizes being the ones that saved the most time).  The cost
   exceeded the gain on every input measured. *)
let condense_pattern_memo = Atomic.make false

(* [condense_pattern_memo_mutant] (for tests only): the key leaves out the
   renaming, so all images of one disjunct share an entry; not exact, and
   the property test must tell it apart *)
let condense_pattern_memo_mutant = ref false

(* per generation and mode: on one 120 s run of a Rust-derived input, 20,000,
   60,000 and 200,000 entries remembered 49, 53 and 56 % of 2.5 million
   pattern images, at a peak resident size of 0.64, 0.88 and 1.44 GB
   against 0.47 GB without the memo *)
let condense_pattern_memo_gen = 50_000

type condense_pattern_entry = {
  pe_false : bool;
  mutable pe_occ : string option option;  (** [None]: not computed yet *)
  mutable pe_bag : string option;  (** [None]: not computed yet *)
}

module CondensePatternKey = struct
  type t = {
    d : Formula.t;
    dh : int;  (** [condense_formula_hash d] *)
    ren : (Ident.tvar * Ident.tvar * Sort.t) list;
  }

  let compare a b =
    match Int.compare a.dh b.dh with
    | 0 -> (
        match
          List.compare
            (fun (x, y, s) (x', y', s') ->
              match Ident.tvar_compare x x' with
              | 0 -> (
                  match Ident.tvar_compare y y' with
                  | 0 -> Stdlib.compare s s'
                  | r -> r)
              | r -> r)
            a.ren b.ren
        with
        | 0 -> Stdlib.compare a.d b.d
        | r -> r)
    | r -> r

  let hash k =
    List.fold k.ren ~init:k.dh ~f:(fun h (x, y, _) ->
        (((h * 31) + String.hash (Ident.name_of_tvar x)) * 31)
        + String.hash (Ident.name_of_tvar y))
    land Int.max_value

  let sexp_of_t _ = Sexp.Atom "pattern"
end

type condense_pattern_tables = {
  mutable p_envs : (DTEnv.t * FunEnv.t) option;
  mutable p_cur : (CondensePatternKey.t, condense_pattern_entry) Hashtbl.t array;
  mutable p_prev : (CondensePatternKey.t, condense_pattern_entry) Hashtbl.t array;
  mutable p_strings : (string, string) Hashtbl.t;
}

let condense_pattern_tbl () = Hashtbl.create (module CondensePatternKey)

let condense_pattern_key : condense_pattern_tables Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () ->
      {
        p_envs = None;
        p_cur = Array.init 2 ~f:(fun _ -> condense_pattern_tbl ());
        p_prev = Array.init 2 ~f:(fun _ -> condense_pattern_tbl ());
        p_strings = Hashtbl.create (module String);
      })

(* this domain's tables, emptied first if an environment was replaced *)
let condense_pattern_tables () =
  let t = Stdlib.Domain.DLS.get condense_pattern_key in
  let envs = (get_dtenv (), get_fenv ()) in
  (match t.p_envs with
  | Some (d, f) when phys_equal d (fst envs) && phys_equal f (snd envs) -> ()
  | _ ->
      t.p_envs <- Some envs;
      t.p_cur <- Array.init 2 ~f:(fun _ -> condense_pattern_tbl ());
      t.p_prev <- Array.init 2 ~f:(fun _ -> condense_pattern_tbl ());
      t.p_strings <- Hashtbl.create (module String));
  t

(* a key the polymorphic comparison rejects (a sort holding a value it
   cannot compare) is neither found nor stored *)
(* empties this domain's tables (tests: after a mutant key has filled them) *)
let condense_pattern_memo_reset () =
  (Stdlib.Domain.DLS.get condense_pattern_key).p_envs <- None

let condense_pattern_find t ~alpha k =
  let a = if alpha then 1 else 0 in
  try
    match Hashtbl.find t.p_cur.(a) k with
    | Some e -> Some e
    | None -> (
        match Hashtbl.find t.p_prev.(a) k with
        | Some e ->
            Hashtbl.set t.p_cur.(a) ~key:k ~data:e;
            Some e
        | None -> None)
  with Invalid_argument _ -> None

let condense_pattern_store t ~alpha k e =
  let a = if alpha then 1 else 0 in
  if Hashtbl.length t.p_cur.(a) >= condense_pattern_memo_gen then (
    t.p_prev.(a) <- t.p_cur.(a);
    t.p_cur.(a) <- condense_pattern_tbl ();
    if Hashtbl.length t.p_strings >= 4 * condense_pattern_memo_gen then
      t.p_strings <- Hashtbl.create (module String));
  try Hashtbl.set t.p_cur.(a) ~key:k ~data:e with Invalid_argument _ -> ()

let condense_pattern_intern t s =
  match Hashtbl.find t.p_strings s with
  | Some s' -> s'
  | None ->
      Hashtbl.set t.p_strings ~key:s ~data:s;
      s


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
   receives the number of atoms dropped.  A seed is not searched when a
   disjunct it touches has more than [joint_merge_only_nodes] nodes and no
   other live disjunct has its bag of symbols: a renaming that merges none
   of its variables keeps the bag of its normal form, so it can be accepted
   only through a merge of its own variables, which the passes do not seed
   on a disjunct of more than [merge_seed_nodes] nodes either.  The search
   for such a merge normalises one image of the whole disjunct per merge
   pattern: on an RCaml resolvent of 19 disjuncts, one of 3,253 nodes with
   eight private variables, a single seed ran for more than five minutes
   inside its 5,000-normalisation budget, each image costing tens of
   milliseconds.  The bound is above the passes' 16 nodes because the joint
   rounds do find such merges on mid-sized disjuncts: on three RCaml inputs
   refusing above 16 nodes changed 20 of about a thousand condensations,
   and refusing above 256 none.  The refusal can only miss a condensation,
   never make one inexact; it is applied only while
   [condense_joint_merge_only] is on (off by default).

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

   [merge_pattern_prune] fails a search call at once when some touched
   disjunct can have no acceptable image under any completion of the
   bindings.  It asks this of every touched disjunct where a seed's search
   starts, and afterwards, as [ok] does, of the disjuncts holding the
   variable just bound or fixed or its image (a disjunct whose own variables
   did not change can still lose its last candidate image to the grown
   domain; that is not looked for, which only prunes less).  For a touched
   disjunct [i] it substitutes the bindings made so
   far and enumerates the merge patterns of the variables still undecided
   (each sent to a variable of its sort the image already holds, to an
   earlier undecided one, or left alone; at most [merge_pattern_max]
   patterns, else [i] is not pruned on), normalises the image under each,
   and keeps the bags ([condense_cbag]) of the results, with the image's
   decided variables printed by name, and whether one is [false].  The call
   fails when no result is [false] (or [joint] is off) and no live disjunct
   free of the current domain has one of those bags (its own variables
   among the decided ones printed by name too).
   It rests on one assumption about [nf], the composition
   [Evaluator.simplify] then [Normalizer.normalize]: renaming the free
   variables of a formula injectively before [nf] gives the bag [nf] gives
   without the renaming (only the order of operands and the names change;
   [condense_premise_ok] checks it on a formula).  Under it the prune is
   exact: a completion restricted to [i]'s variables is one of the patterns
   followed by an injective renaming that fixes the decided variables (they
   are final), so the final image normalises to a formula with the bag of
   that pattern's; an acceptable image is [false] or
   a live disjunct with the same normal form, hence the same bag, free of
   the final domain, which contains the current one.  So a pruned call is
   one that would fail, every condensation found is one the search without
   the prune finds first, and where no budget cuts either search the two
   return the same clause.  Where the assumption fails the prune can only
   miss a condensation: what is dropped is still checked by normalisation,
   so the result is an equivalence of the clause either way.
   With [merge_pattern_gate] [g] the test is asked only once the call has
   charged [g] normalisations.  On three Rust-derived inputs the calls were
   bimodal: 3,697 of 3,908 ended under 2,000 normalisations (147 s in all)
   and the other 208 reached the 20,000 cap (594 s), none in between but 3;
   the test costs more than it saves on the first kind and is what ends the
   second.  A gate on the normalisations of the current seed instead did
   not separate them, since the seeds the prune ends are most of the seeds
   of a capped call and each paid the gate before being ended.  Which calls
   are pruned changes, not what a pruned call is, so the result is the same
   as without the gate wherever no budget cuts the search.
   [merge_pattern_identity_only] (for tests only, a mutant) takes the
   pattern without merges alone, which is not exact.  The pattern
   normalisations are charged to the budgets like any other, and the test
   is not asked once a budget is spent (the search call it guards then
   ends at its entry and fails, as a pruned one does).  They were once
   uncharged, and then the prune made the budgets void: a pruned call
   fails before any image of its touched disjuncts is normalised, so a
   seed whose every branch is pruned charges nothing and is never cut,
   and the search enumerates the bindings of the disjunct's undecided
   variables to the end, an exponential number of calls each paying up
   to [merge_pattern_max] pattern normalisations.  On a Rust-derived
   resolvent of 13 disjuncts (two renamed copies of a 458-node quantified
   disjunct with 14 variables, 8 candidates each) the call charged 2,000
   normalisations, opened the prune's gate, and then ran for more than
   five minutes on pattern normalisations alone with the seed 13
   normalisations short of its budget.  Charging them changes which
   condensation a budget-cut search finds, never whether a found one is
   exact, and it can find fewer: on a 106-disjunct resolvent of another
   Rust-derived input the uncharged prune ran 28,000 pattern
   normalisations past the call's cap of 20,000 and dropped 35 disjuncts,
   where the charged one stops at the cap having dropped 3.  Charging only
   the seed's budget leaves the call without a cap (a 20-disjunct
   resolvent then ran 35,796 pattern normalisations, where the capped
   call stops after 18,050).  Why the
   prune is wanted: a resolvent carrying a datatype decomposition tree
   copied from a program state has a root disjunct holding every child
   variable of its sort; a seed in a child family binds a child variable
   to a sibling, which merges two of the root's variables (or, one level
   down, two of a child's), so that disjunct's image is no live
   disjunct, but that was found only once all of its private variables
   were decided, after every combination of their candidates had been
   normalised until the seed's budget ran out (58 of 291 condensations
   of one input ended at the budget that way, finding nothing more).

   [checks_used], when given, receives the number of normalisations the
   call charged against its budget, and [nodes_used] the number of search
   calls it made.

   Contract.  Requires [unknowns] to hold every variable of the clause that
   stands for an unknown (a predicate or function to be solved for), so
   that none of them is renamed.  Returns [(ps', ns', phi')] with [ps']
   a subset of [ps], [ns'] of [ns], and the disjuncts of [phi'] a subset
   of [phi]'s (in their order), whose universal closure is equivalent to
   the input clause's in every model and for every interpretation of the
   unknowns; when it gives up (a budget spent) it returns the
   condensations found so far, the clause itself if none.  Every
   normalisation it runs is charged to [checks] except those answered
   from a cache, so it runs at most [max_checks] of them plus the
   overshoot of the step that crosses the bound (one prune test, at most
   [merge_pattern_max] pattern normalisations, and the images [ok] asks
   for in the frames that are still open).  Search calls all of whose
   images are cached charge nothing; [max_search_nodes] is what bounds
   those. *)
let condense_pure ~unknowns ?(max_checks = 20_000) ?(seed_checks = 500)
    ?(merge_seed_nodes = 16) ?(atom_free = true) ?(shape_candidates = false)
    ?(shape_commutative = false) ?(inclusion_candidates = false)
    ?max_search_nodes ?(memo_failures = false) ?checks_used ?nodes_used
    ?(joint = false) ?(joint_seed_checks = 5_000) ?(joint_max_seeds = 2_000)
    ?joint_dropped ?(joint_incl_before_refusal = false)
    ?(joint_prune_doomed = false) ?(merge_pattern_prune = false)
    ?(merge_pattern_max = 256) ?(merge_pattern_gate = 0)
    ?(merge_pattern_identity_only = false)
    ?(joint_merge_only_nodes = 256)
    (ps, ns, phi) =
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
  let nf_uncounted l =
    let c = Normalizer.normalize @@ Evaluator.simplify l in
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
  let canon_ids = condense_formula_tbl () in
  (* the normal form two disjuncts are compared in, remembered per formula
     (an image asked for again by a later seed is not normalised again, and
     is not counted against the budgets); what is kept is the disjuncts with
     that normal form, which is all the search reads of it *)
  let memo = condense_formula_tbl () in
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
    let first = condense_formula_tbl () in
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
  (* [merge_pattern_prune]: the live disjuncts by the bag of their normal
     form, and per disjunct, computed when first asked, what its image can
     be (see the head comment) *)
  let cbag_tbl = Hashtbl.Poly.create () in
  let by_cbag = Hashtbl.create (module Int) in
  (* the bags computed in this call, keyed up to an injective renaming of the
     free variables a bag erases ([condense_cbag_memo]) *)
  let cbag_memo = Common.Ext.Hashtbl.PolyDeep.create () in
  let condense_cbag ?keep c = condense_cbag_through cbag_memo ?keep c in
  (* [condense_occ_filter]: the input disjuncts' occurrence profiles, or
     [None] when the filter cannot be used in this call (switched off, the
     clause's print has [#occ] text or a string literal, or some disjunct is
     outside the profile's fragment) *)
  let occ_live =
    lazy
    (if not (Atomic.get condense_occ_filter) then None
     else
       let raw = Formula.str_of phi in
       if String.is_substring raw ~substring:"#occ" || String.contains raw '"' then (
         condense_occ_why := "text";
         None)
       else
         let tbl = Hash_set.create (module String) in
         if
           Array.for_all canon_of ~f:(fun c ->
               match condense_occ_profile c with
               | Some k ->
                   Hash_set.add tbl k;
                   true
               | None -> false)
         then Some tbl
         else None)
  in
  (* built when the prune is first asked, so that a call that ends before
     its gate opens pays nothing for it *)
  let bags_built =
    lazy
    (Array.iteri canon_of ~f:(fun j c ->
        condense_premise_probe lits_a.(j);
        let b = condense_cbag c in
        let id =
          match Hashtbl.find cbag_tbl b with
          | Some id -> id
          | None ->
              let id = Hashtbl.length cbag_tbl in
              Hashtbl.set cbag_tbl ~key:b ~data:id;
              id
        in
        Hashtbl.add_multi by_cbag ~key:id ~data:j))
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
    else if not (Atomic.get condense_roles_by_pieces) then
      condense_roles_reference shape_strs occs
    else condense_roles_by_pieces_of shape_strs occs
  in
  let alive = Array.create ~len:n true in
  (* the disjuncts each variable occurs in, latest first *)
  let occ = Array.create ~len:nv [] in
  Array.iteri lvars ~f:(fun i vs ->
      Set.iter vs ~f:(fun k -> occ.(k) <- i :: occ.(k)));
  let lits_of k = List.filter occ.(k) ~f:(fun i -> alive.(i)) in
  (* [Int.Set.of_list (lits_of k)], remembered until a condensation changes
     which disjuncts are live ([alive_gen] counts those changes); the set is
     the one [of_list] builds from the same list, tree shape included *)
  let alive_gen = ref 0 in
  let lits_sets = Array.create ~len:nv None in
  let lits_set_of k =
    match lits_sets.(k) with
    | Some (g, s) when g = !alive_gen -> s
    | _ ->
        let s = Int.Set.of_list (lits_of k) in
        lits_sets.(k) <- Some (!alive_gen, s);
        s
  in
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
  (* [merge_pattern_prune]: what the image of disjunct [i] can be under a
     completion of [sigma] and [fixed], remembered per disjunct and per
     state of its variables (bound to what, decided otherwise, undecided).
     The image so far substitutes the bound variables; each undecided
     variable may end up as one of the image's variables of its sort or as a
     variable it does not hold, and only the first changes the image beyond
     an injective renaming.  So each merge pattern -- each undecided variable
     sent to a decided image variable of its sort, to an earlier undecided
     one, or left alone -- is normalised once, and the result is the bags of
     those normal forms and whether one is [false]; [`Any] when there are
     more than [merge_pattern_max] patterns.  The states are read through
     [decided] and [rd], so a failure remembered by [memo_failures] knows it
     depends on them. *)
  let possible_tbl = Hashtbl.create (module CondenseKeys.Image) in
  (* [condense_pattern_memo], read once per call; with it off nothing of the
     memo is allocated or computed *)
  let pattern_memo_on = Atomic.get condense_pattern_memo in
  (* the disjuncts' hashes, for [condense_pattern_memo]'s keys *)
  let dhash =
    if pattern_memo_on then
      Array.map lits_a ~f:(fun l -> lazy (condense_formula_hash l))
    else [||]
  in
  (* the budgets of the search: the normalisations the current seed may
     still charge end at [seed_limit], those of the whole call at
     [max_checks], and the search calls at [max_search_nodes] *)
  let seed_limit = ref 0 in
  let nodes = ref 0 in
  let out_of_nodes () =
    match max_search_nodes with Some m -> !nodes > m | None -> false
  in
  let budget_spent () =
    !checks >= max_checks || !checks >= !seed_limit || out_of_nodes ()
  in

  let possible_at sigma fixed i =
    let st =
      Set.fold lvars.(i) ~init:[] ~f:(fun acc k ->
          if decided sigma fixed k then (
            rd k;
            match Map.find sigma k with Some y -> (k, y) :: acc | None -> (k, -2) :: acc)
          else (k, -1) :: acc)
    in
    let key = (i, st) in
    match Hashtbl.find possible_tbl key with
    | Some r ->
        condense_profile.possible_hit <- condense_profile.possible_hit + 1;
        r
    | None ->
        let tp0 = Common.Clock.now_s () in
        let bound = List.filter st ~f:(fun (_, y) -> y >= 0) in
        let image_vars =
          List.map st ~f:(fun (k, y) -> if y >= 0 then y else k)
          |> List.filter ~f:(fun k ->
                 not (List.exists st ~f:(fun (k', y) -> k' = k && y = -1)))
          |> List.dedup_and_sort ~compare:Int.compare
        in
        (* the image's decided variables are its final ones: a completion
           renames only what the undecided variables become *)
        let keep_ids = Int.Set.of_list image_vars in
        let keep = Set.Poly.of_list (List.map image_vars ~f:(fun k -> fst vars.(k))) in
        let undecided =
          List.filter_map st ~f:(fun (k, y) -> if y = -1 then Some k else None)
          |> List.sort ~compare:Int.compare
        in
        (* the patterns, each a list of (undecided variable, its target) *)
        let count = ref 0 in
        let exception Too_many in
        let rec patterns reps = function
          | [] ->
              incr count;
              if !count > merge_pattern_max then raise Too_many;
              [ [] ]
          | u :: rest ->
              let targets =
                if merge_pattern_identity_only then []
                else List.filter reps ~f:(fun w -> sort_class.(w) = sort_class.(u))
              in
              List.concat_map (u :: targets) ~f:(fun w ->
                  let reps' = if w = u then u :: reps else reps in
                  List.map (patterns reps' rest) ~f:(fun p ->
                      if w = u then p else (u, w) :: p))
        in
        let r =
          match patterns image_vars undecided with
          | exception Too_many ->
              condense_profile.pattern_any <- condense_profile.pattern_any + 1;
              `Any
          | pats ->
              let has_false = ref false in
              let ids =
                let mt =
                  if pattern_memo_on then Some (condense_pattern_tables ())
                  else None
                in
                List.filter_map pats ~f:(fun pat ->
                    let pairs = bound @ pat in
                    let image () =
                      let ren =
                        List.fold pairs ~init:Map.Poly.empty ~f:(fun acc (k, w) ->
                            let y, s = vars.(w) in
                            Map.Poly.set acc ~key:(fst vars.(k)) ~data:(Term.mk_var y s))
                      in
                      Formula.subst ren lits_a.(i)
                    in
                    condense_profile.pattern_nf <- condense_profile.pattern_nf + 1;
                    (* charged like every other normalisation, also when
                       what the prune reads of it is remembered
                       ([condense_pattern_memo]): see the head comment on
                       why an uncharged prune left the search without a
                       bound *)
                    incr checks;
                    let pkey =
                      Option.map mt ~f:(fun _ ->
                          {
                            CondensePatternKey.d = lits_a.(i);
                            dh = Lazy.force dhash.(i);
                            ren =
                              (if !condense_pattern_memo_mutant then []
                               else pairs)
                              |> List.map ~f:(fun (k, w) ->
                                  let y, s = vars.(w) in
                                  (fst vars.(k), y, s))
                              |> List.sort ~compare:(fun (x, _, _) (x', _, _) ->
                                     Ident.tvar_compare x x');
                          })
                    in
                    let remembered =
                      match (mt, pkey) with
                      | Some t, Some k -> condense_pattern_find t ~alpha:alpha_canon k
                      | _ -> None
                    in
                    match remembered with
                    | Some e ->
                        condense_profile.pattern_hit <- condense_profile.pattern_hit + 1;
                        let img = lazy (image ()) in
                        if Lazy.force condense_premise_on then
                          condense_premise_probe (Lazy.force img);
                        (* the normal form again, uncharged, for what the
                           entry does not hold: it is the one the call would
                           have computed (see [condense_pattern_memo]) *)
                        let c = lazy (nf_uncounted (Lazy.force img)) in
                        if joint && e.pe_false then (
                          has_false := true;
                          None)
                        else if
                          match Lazy.force occ_live with
                          | None -> false
                          | Some live -> (
                              let occ =
                                match e.pe_occ with
                                | Some o -> o
                                | None ->
                                    let o = condense_occ_profile (Lazy.force c) in
                                    e.pe_occ <- Some o;
                                    o
                              in
                              match occ with
                              | Some k -> not (Hash_set.mem live k)
                              | None -> false)
                        then (
                          condense_profile.occ_skipped <- condense_profile.occ_skipped + 1;
                          None)
                        else
                          let b =
                            match e.pe_bag with
                            | Some b -> b
                            | None ->
                                let b = condense_cbag (Lazy.force c) in
                                e.pe_bag <- Some b;
                                b
                          in
                          Option.map (Hashtbl.find cbag_tbl b) ~f:(fun id ->
                              (id, lazy (condense_cbag ~keep:(Set.mem keep) (Lazy.force c))))
                    | None ->
                    let s0 = Option.map mt ~f:(fun _ -> Ident.fresh_stamp ()) in
                    let img = image () in
                    condense_premise_probe img;
                    let c = nf img in
                    (* the entry to fill in, with the memo on only *)
                    let e =
                      match (mt, pkey, s0) with
                      | Some t, Some k, Some s0 ->
                          let e =
                            { pe_false = Formula.is_false c; pe_occ = None; pe_bag = None }
                          in
                          if Ident.fresh_stamp () = s0 then
                            condense_pattern_store t ~alpha:alpha_canon k e;
                          Some e
                      | _ -> None
                    in
                    if joint && Formula.is_false c then (
                      has_false := true;
                      None)
                    else if
                      match Lazy.force occ_live with
                      | None -> false
                      | Some live -> (
                          let o = condense_occ_profile c in
                          (match (mt, e) with
                           | Some t, Some e ->
                               e.pe_occ <- Some (Option.map o ~f:(condense_pattern_intern t))
                           | _ -> ());
                          match o with
                          | Some k -> not (Hash_set.mem live k)
                          | None -> false)
                    then (
                      condense_profile.occ_skipped <- condense_profile.occ_skipped + 1;
                      None)
                    else
                      let tb0 = Common.Clock.now_s () in
                      let b = condense_cbag c in
                      (match (mt, e) with
                       | Some t, Some e -> e.pe_bag <- Some (condense_pattern_intern t b)
                       | _ -> ());
                      condense_profile.pattern_bag_s <-
                        condense_profile.pattern_bag_s +. (Common.Clock.now_s () -. tb0);
                      Option.map (Hashtbl.find cbag_tbl b) ~f:(fun id ->
                          (id, lazy (condense_cbag ~keep:(Set.mem keep) c))))
              in
              `Bags (ids, !has_false, keep_ids)
        in
        Hashtbl.set possible_tbl ~key ~data:r;
        condense_profile.pattern_s <-
          condense_profile.pattern_s +. (Common.Clock.now_s () -. tp0);
        r
  in
  (* [merge_pattern_prune]: some touched disjunct has no acceptable image
     under any completion of [sigma] (see the head comment); the domain is
     read through [in_dom] as well *)
  let named_bags = Hashtbl.Poly.create () in
  let named_bag j keep_ids =
    let ks = Set.to_list (Set.inter lvars.(j) keep_ids) in
    match Hashtbl.find named_bags (j, ks) with
    | Some b -> b
    | None ->
        let tn0 = Common.Clock.now_s () in
        let keep = Set.Poly.of_list (List.map ks ~f:(fun k -> fst vars.(k))) in
        let b = condense_cbag ~keep:(Set.mem keep) canon_of.(j) in
        Hashtbl.set named_bags ~key:(j, ks) ~data:b;
        condense_profile.named_s <-
          condense_profile.named_s +. (Common.Clock.now_s () -. tn0);
        b
  in
  let rec doomed_one sigma fixed i =
    merge_pattern_prune
    && !checks >= merge_pattern_gate
    (* once a budget is spent the search call this test guards ends at its
       entry, failing as a pruned call does, so the test would only spend
       normalisations past the budget *)
    && (not (budget_spent ()))
    && (Lazy.force bags_built;
        true)
    && (condense_profile.doomed_n <- condense_profile.doomed_n + 1;
        let td0 = Common.Clock.now_s () in
        let r = doomed_body sigma fixed i in
        condense_profile.doomed_s <-
          condense_profile.doomed_s +. (Common.Clock.now_s () -. td0);
        r)
  and doomed_body sigma fixed i =
    (match possible_at sigma fixed i with
       | `Any | `Bags (_, true, _) -> false
       | `Bags (ids, false, keep_ids) ->
           not
             (List.exists ids ~f:(fun (id, named) ->
                  List.exists
                    (Option.value ~default:[] (Hashtbl.find by_cbag id))
                    ~f:(fun j ->
                      alive.(j)
                      && (not (Set.exists lvars.(j) ~f:(in_dom sigma)))
                      && String.equal (named_bag j keep_ids) (Lazy.force named)))))
    && (condense_profile.pruned <- condense_profile.pruned + 1;
        true)
  in
  let merge_doomed sigma fixed touched =
    merge_pattern_prune && Set.exists touched ~f:(doomed_one sigma fixed)
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
  let image_matches = Hashtbl.create (module CondenseKeys.Image) in
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
  (* With [memo_failures]: the calls of [search] that failed with no budget
     cut below them, keyed by their touched disjuncts and the variable they
     chose, each with the state at entry of every variable its execution
     read.  [search] is a function of [touched], the live disjuncts and the
     states of the variables it reads (bindings, decisions, the remembered
     normal forms being a function of the image), so a call entered with the
     same touched disjuncts and agreeing on all those variables executes the
     same way and fails too: it is answered from here without being searched.
     Cleared when a condensation changes which disjuncts are live. *)
  let failures = Hashtbl.create (module CondenseKeys.Call) in
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
    if budget_spent () then (
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
                 Array.equal Int.equal ks' ks && Array.equal Int.equal ls' ls)
           with
          | Some (_, _, tbl) -> Hash_set.add tbl vs
          | None ->
              let tbl = Hash_set.create (module CondenseKeys.States) in
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
          let lits_u = Int.Set.of_list (lits_of u) in
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
                  || (ok sigma fixed i && not (doomed_one sigma fixed i)))
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
                    (not (Set.mem lvars.(i) u))
                    || (ok sigma fixed i && not (doomed_one sigma fixed i)))
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
        (* sets of disjunct numbers are [Int.Set]s: the same tree a
           polymorphic set of the same numbers built by the same operations
           is, so every traversal visits them in the same order *)
        let touched = Int.Set.of_list xl in
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
              if
                Set.for_all touched ~f:(ok sigma fixed)
                && not (merge_doomed sigma fixed touched)
              then search sigma fixed touched
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
        let c0 = !checks and n0 = !nodes in
        let r = try_seed x in
        if condense_diag_on () && (!checks - c0 > 50 || Option.is_some r) then
          eprintf "[condense-diag] x=%s sort=%s incl=%s lits=%d sizes=%s checks=%d nodes=%d %s\n%!"
            (Ident.name_of_tvar (fst vars.(x)))
            (Term.str_of_sort (snd vars.(x)))
            (match incl.(x) with None -> "none" | Some c -> string_of_int (Set.length c))
            (List.length (lits_of x))
            (String.concat ~sep:","
               (List.map (lits_of x) ~f:(fun i -> string_of_int (Lazy.force sizes.(i)))))
            (!checks - c0) (!nodes - n0)
            (match r with Some d -> sprintf "found dom=%d" (Set.length d) | None -> "none");
        match r with
        | None -> ()
        | Some dom ->
            found := true;
            clear_nonempty ys_cache;
            clear_nonempty failures;
            incl_stale := true;
            Array.iteri lvars ~f:(fun i vs ->
                if not (Set.are_disjoint vs dom) then alive.(i) <- false);
            incr alive_gen
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
    if not joint_prune_doomed then None
    else Some (fun (bs, fx) ->
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
                               j < 0 || alive.(j))))))
  in
  let n_joint = ref 0 in
  (* [merge_only_large i]: disjunct [i] has more than [joint_merge_only_nodes]
     nodes and no other live disjunct has its bag of symbols ([bag_ids]).
     A renaming that merges none of its variables leaves the bag of its
     normal form unchanged, so once it is touched its image can be accepted
     only through a merge of its variables; the joint hand-over does not
     search for that on a large disjunct (see the head comment). *)
  let merge_only_large i =
    Atomic.get condense_joint_merge_only
    && Lazy.force sizes.(i) > joint_merge_only_nodes
    && not
         (Array.existsi bag_ids ~f:(fun j b ->
              j <> i && alive.(j) && b = bag_ids.(i)))
  in
  let touched_tbl = Hashtbl.create (module JointImageKey) in
  let touched_gen = ref 0 in
  (* [anchor_count.(k)]: the number of kept atoms (of either polarity, an
     atom kept in both counted twice) that read variable [k], so that the
     variables private once a seed's atoms are dropped -- [priv_of] of the
     kept atoms minus the dropped ones -- are those whose count the dropped
     atoms bring to zero and that are not unknowns: what [priv_of] gives,
     without collecting the variables of every kept atom for every seed (a
     fifth of a joint condensation's time on resolvents of 13-16 atoms whose
     enumeration hands over ten thousand closures).  Recounted at each round,
     the only point where the kept atoms change. *)
  let anchor_count = Array.create ~len:nv 0 in
  let is_unknown = Array.map vars ~f:(fun (x, _) -> Set.mem unknowns x) in
  let vars_of_atom a =
    List.filter_map (Set.to_list (Atom.tvs_of a)) ~f:(Map.Poly.find index)
  in
  (* the variables of the kept atoms by their position in the order
     [joint_atom_seeds] numbers them ([Set.to_list] of the kept head atoms,
     then of the kept premises), which is how a seed names its dropped atoms *)
  let kept_vars = ref [||] in
  let count_atom delta p =
    List.iter !kept_vars.(p) ~f:(fun k -> anchor_count.(k) <- anchor_count.(k) + delta)
  in
  let rec joint_loop () =
    Array.fill anchor_count ~pos:0 ~len:nv 0;
    kept_vars :=
      Array.of_list (List.map (Set.to_list !kept_ps @ Set.to_list !kept_ns) ~f:vars_of_atom);
    Array.iteri !kept_vars ~f:(fun p _ -> count_atom 1 p);
    (* the clause's number of each variable of [joint_atom_seeds]' numbering,
       or [None] for a variable the pure part does not hold *)
    let loc_tbl = Hashtbl.create (module Int) in
    let loc (seed : joint_seed) l =
      Hashtbl.find_or_add loc_tbl l ~default:(fun () ->
          Map.Poly.find index (seed.js_var l))
    in
    if !checks < max_checks && not (out_of_nodes ()) then
      let found =
        joint_atom_seeds ~unknowns ~max_seeds:joint_max_seeds ?doomed
          ~pure:
            (List.filter_mapi (Array.to_list lvars_t) ~f:(fun i vs ->
                 if alive.(i) then Some vs else None))
          !kept_ps !kept_ns
          ~f:(fun seed ->
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
              (* the kept atoms once the seed's are dropped, needed only
                 when the seed succeeds *)
              let kps = lazy (Set.diff !kept_ps (fst (Lazy.force seed.js_atoms)))
              and kns = lazy (Set.diff !kept_ns (snd (Lazy.force seed.js_atoms))) in
              (* The variables private once the seed's atoms are dropped:
                 [priv_of] of the kept atoms but the seed's.  A variable no
                 dropped atom reads keeps its count, so its privacy is the
                 current [is_priv]; one a dropped atom reads becomes private
                 when the dropped atoms read it every time a kept atom does.
                 Since dropping only lowers the counts, the new private
                 variables are the current ones and [changed], and [is_priv]
                 is set by writing [changed] (and restored by clearing it)
                 rather than by copying the whole array twice per seed. *)
              let changed =
                Set.iter seed.js_dropped ~f:(count_atom (-1));
                let acc = ref [] in
                let visit p =
                  List.iter !kept_vars.(p) ~f:(fun k ->
                      if anchor_count.(k) = 0 && (not is_unknown.(k))
                         && (not is_priv.(k)) && not (List.mem !acc k ~equal:Int.equal)
                      then acc := k :: !acc)
                in
                Set.iter seed.js_dropped ~f:visit;
                Set.iter seed.js_dropped ~f:(count_atom 1);
                !acc
              in
              let priv'_at k = is_priv.(k) || List.mem changed k ~equal:Int.equal in
              let ok_binds =
                List.for_all seed.js_binds ~f:(fun (x, y) ->
                    match (loc seed x, loc seed y) with
                    | None, _ -> true
                    | Some _, None -> false
                    | Some kx, Some ky ->
                        priv'_at kx && sort_class.(kx) = sort_class.(ky))
              in
              if not ok_binds then (
                condense_profile.refused_binds <- condense_profile.refused_binds + 1;
                joint_trace (fun () ->
                    sprintf "seed refused: %s"
                      (String.concat ~sep:" "
                         (List.filter_map seed.js_binds ~f:(fun (x, y) ->
                              let x = seed.js_var x and y = seed.js_var y in
                              match (Map.Poly.find index x, Map.Poly.find index y) with
                              | Some _, None ->
                                  Some (sprintf "%s->%s(image not in phi)"
                                          (Ident.name_of_tvar x) (Ident.name_of_tvar y))
                              | Some kx, Some ky
                                when not (priv'_at kx && sort_class.(kx) = sort_class.(ky)) ->
                                  Some (sprintf "%s->%s(not private or sort)"
                                          (Ident.name_of_tvar x) (Ident.name_of_tvar y))
                              | _ -> None))));
                None)
              else
                let sigma =
                  List.fold seed.js_binds ~init:Int.Map.empty ~f:(fun acc (x, y) ->
                      match loc seed x with
                      | Some kx -> Map.set acc ~key:kx ~data:(Option.value_exn (loc seed y))
                      | None -> acc)
                in
                let fixed =
                  List.fold seed.js_fixed ~init:Int.Set.empty ~f:(fun acc x ->
                      match loc seed x with
                      | Some k -> Set.add acc k
                      | None -> acc)
                in
                List.iter changed ~f:(fun k -> is_priv.(k) <- true);
                clear_nonempty failures;
                clear_nonempty ys_cache;
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
                (* a function of the domain of [sigma] and of the live
                   disjuncts: remembered per domain until a condensation
                   changes the live disjuncts, the same set (tree shape
                   included) the same unions build *)
                let touched =
                  if !touched_gen <> !alive_gen then (
                    clear_nonempty touched_tbl;
                    touched_gen := !alive_gen);
                  Hashtbl.find_or_add touched_tbl (Map.length sigma, Map.keys sigma)
                    ~default:(fun () ->
                      Map.fold sigma ~init:Int.Set.empty ~f:(fun ~key ~data:_ acc ->
                          Set.union acc (lits_set_of key)))
                in
                seed_limit := !checks + joint_seed_checks;
                let res =
                  if Map.is_empty sigma then Some Int.Set.empty
                  else
                    match Set.find touched ~f:(fun i -> not (ok sigma fixed i)) with
                    | None when merge_doomed sigma fixed touched -> None
                    | None when Set.exists touched ~f:merge_only_large ->
                        condense_profile.refused_merge_only <-
                          condense_profile.refused_merge_only + 1;
                        None
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
                    incr alive_gen;
                    kept_ps := Lazy.force kps;
                    kept_ns := Lazy.force kns;
                    clear_nonempty failures;
                    clear_nonempty ys_cache;
                    incl_stale := true;
                    n_joint := !n_joint + Set.length seed.js_dropped;
                    Some ()
                | None ->
                    List.iter changed ~f:(fun k -> is_priv.(k) <- false);
                    clear_nonempty failures;
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
  if condense_diag_on () && !checks >= max_checks then (
    eprintf "[condense-diag] capped call: %d disjuncts, private: %s\n" n
      (String.concat ~sep:" "
         (List.filter_mapi (Array.to_list vars) ~f:(fun k (x, s) ->
              if is_priv.(k) then
                Some (sprintf "%s:%s" (Ident.name_of_tvar x) (Term.str_of_sort s))
              else None)));
    Array.iteri canon_of ~f:(fun i c ->
        eprintf "[condense-diag] D%d%s %s\n" i (if alive.(i) then "" else "(dropped)")
          (Formula.str_of c));
    eprintf "%!");
  Option.iter joint_dropped ~f:(fun r -> r := !n_joint);
  Option.iter checks_used ~f:(fun r -> r := !checks);
  Option.iter nodes_used ~f:(fun r -> r := !nodes);
  if Array.for_all alive ~f:Fn.id && !n_joint = 0 then (ps, ns, phi)
  else
    ( !kept_ps,
      !kept_ns,
      Formula.or_of
        (List.filteri (Array.to_list lits_a) ~f:(fun i _ -> alive.(i))) )
