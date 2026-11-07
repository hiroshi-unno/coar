(* Model-based projection, per theory.

   This implements the projections of Nikolaj Bjorner and Mikolas Janota,
   "Playing with Quantified Satisfaction", EPiC Series in Computing vol. 35
   (LPAR-20, Short Presentations), 2015, pp. 15-27, doi 10.29007/vv21 -- which
   generalises the QBF expansion/CEGAR line to theories, and whose theory list
   is the module list below: linear integer and real arithmetic, algebraic data
   types and arrays, with Booleans, bit-vectors and finite domains beside them.

   The operation itself is older and is due to Anvesh Komuravelli, Arie
   Gurfinkel and Sagar Chaki, "SMT-Based Model Checking for Recursive Programs",
   CAV 2014: given a formula and one of its models, return a formula that the
   model satisfies and that implies the existential closure -- an
   under-approximate quantifier elimination.  That last property is the contract
   every module here owes and the one the projection test checks.

   A neighbouring file solves the same quantified problems by strategy
   improvement instead, and its per-theory step selects a TERM rather than
   returning a region; the two are different algorithms and neither is a
   refactoring of the other. *)
open Core
open Common.Ext
open Common.Combinator
open LogicOld

(* Under [model], [not (d | t)] means [t] leaves a nonzero remainder, and the one
   disjunct of [d | t + 1 \/ ... \/ d | t + (d - 1)] that holds is the one whose
   offset cancels it: [i = (-v) mod d] for [v] the model's value of [t].  It is
   computed in [Z], since [d] is a term's constant and can exceed a native int;
   the enumeration of [1, d-1] it replaces is kept for a [t] the evaluator
   cannot read, where it needs [d] to fit.  Divisibility by [d] is divisibility
   by [|d|] (the evaluator reads [d | t] as [t mod d = 0], Euclidean), so the
   offsets are taken modulo [|d|]; with [d] itself a negative divisor left the
   offset list empty and failed the final assertion.  Requires [not (d | t)] to
   hold in [model]; returns the atom [d | t + i], normalized. *)
let pdiv_of_not_pdiv model d t =
  let dv = Z.abs (T_int.let_int d) in
  let atom_at i =
    T_int.mk_pdiv d @@ Evaluator.simplify_term @@ T_int.mk_add t (T_int.mk_int i)
  in
  let holds atom = Evaluator.eval_atom @@ Atom.subst model atom in
  let value_of_t =
    match Evaluator.eval_term (Term.subst model t) with
    | Value.Int v -> Some v
    | _ -> None
    | exception exn_ when not (Common.Timer.is_async exn_) -> None
  in
  let res =
    match value_of_t with
    | Some _ when Z.(leq dv one) -> []
    | Some v ->
        let i = Z.erem (Z.neg v) dv in
        if Z.sign i = 0 then []
        else
          let atom = atom_at i in
          if holds atom then [ Normalizer.normalize_atom atom ] else []
    | None ->
        if not (Z.fits_int dv) then []
        else
          List.filter_map
            (List.range ~stop:`inclusive 1 (Z.to_int dv - 1))
            ~f:(fun i ->
              let atom = atom_at (Z.of_int i) in
              if holds atom then Option.return @@ Normalizer.normalize_atom atom
              else None)
  in
  match res with [ atom ] -> atom | _ -> assert false

let sign ~print model atom =
  let res =
    if Evaluator.eval @@ Evaluator.simplify_atom @@ Atom.subst model atom then (
      print @@ lazy (sprintf "[sign] pos: %s" (Atom.str_of atom));
      Formula.mk_atom @@ Normalizer.normalize_atom atom)
    else (
      print @@ lazy (sprintf "[sign] neg: %s" (Atom.str_of atom));
      match Atom.negate atom with
      | None ->
          if true then Formula.negate @@ Formula.mk_atom atom
          else failwith @@ sprintf "[sign] %s" (Atom.str_of atom)
      | Some neg_atom -> Formula.mk_atom @@ Normalizer.normalize_atom neg_atom)
  in
  match res with
  | Formula.Atom (Atom.App (Predicate.Psym T_int.NotPDiv, [ t1; t2 ], _), _)
    -> (
      assert (T_int.is_int t1);
      Formula.mk_atom @@ pdiv_of_not_pdiv model t1 t2)
  | fml -> fml

exception NotNormalized

(* [consulted], when given, is set when the result was read off [model] (a disjunction,
   of which only the sides [model] satisfies are kept); otherwise the result is a
   function of the formula alone *)
let rec atoms_of ?consulted model = function
  | Formula.Atom (atm, _) -> Set.Poly.singleton atm
  | Formula.UnaryOp (Not, Atom (phi, _), _) -> (
      match Atom.negate phi with
      (* The result is read as a *conjunction*, so returning the empty set here would assert
         nothing and quietly drop this literal -- which weakens the projection, the direction
         that breaks "the result implies the existential".  [Atom.negate] answers [None] only
         for an application of an uninterpreted predicate, which a theory projection should
         never be handed. *)
      | None ->
          failwith
          @@ sprintf
               "[mbp] cannot negate %s: model-based projection expects theory \
                atoms, not an application of an uninterpreted predicate"
               (Atom.str_of phi)
      | Some neg_atom -> Set.Poly.singleton neg_atom)
  | Formula.UnaryOp (Not, UnaryOp (Not, phi', _), _) ->
      atoms_of ?consulted model phi'
  | Formula.BinaryOp (And, phi1, phi2, _) ->
      Set.union (atoms_of ?consulted model phi1) (atoms_of ?consulted model phi2)
  | Formula.BinaryOp (Or, phi1, phi2, _) ->
      Option.iter consulted ~f:(fun r -> r := true);
      let s1 =
        if Evaluator.eval @@ Evaluator.simplify @@ Formula.subst model phi1 then
          atoms_of ?consulted model phi1
        else Set.Poly.empty
      in
      let s2 =
        if Evaluator.eval @@ Evaluator.simplify @@ Formula.subst model phi2 then
          atoms_of ?consulted model phi2
        else Set.Poly.empty
      in
      (* Same reasoning as above: two empty halves would union to the empty set, i.e. to
         [true], dropping the whole disjunction.  It can only happen when the model does not
         satisfy the input, which is the caller's precondition, so say so instead. *)
      if Set.is_empty s1 && Set.is_empty s2 then
        failwith
        @@ sprintf
             "[mbp] the model satisfies neither side of %s; model-based \
              projection requires a model of its input"
             (Formula.str_of (Formula.mk_or phi1 phi2))
      else Set.union s1 s2
  | _ ->
      (*failwith (Formula.str_of phi ^ " is not atomic formula")*)
      raise NotNormalized

let normalize_mbp_reading ?consulted model =
  let ph name f x = Common.PhaseTime.with_phase name (fun () -> f x) in
  ph "nm-simplify" Evaluator.simplify_atom
  >> ph "nm-split" (atoms_of ?consulted model)
  >> ph "nm-normalize" (Set.Poly.map ~f:Normalizer.normalize_atom)
  >> Set.concat_map
       ~f:
         (ph "nm-simplify" Evaluator.simplify_atom
         >> ph "nm-split" (atoms_of ?consulted model)
         >> ph "nm-normalize" (Set.Poly.map ~f:Normalizer.normalize_atom))

let normalize_mbp model = normalize_mbp_reading model

(* [normalize_mbp]'s results by the atom (structurally), kept only for an atom whose
   normalization did not read the model, so that a hit returns what recomputing under
   any model returns: simplification and normalization of an atom read the atom alone
   (no fresh name is drawn, no solver is asked).  Successive projections of one solve
   hand over largely the same atoms -- on a 2025 HWMCC bit-vector miter, three of four
   atoms normalized before the bit-vector rules had been normalized in an earlier call,
   at about 10 ms an atom.  A miss only recomputes; emptied when it grows past its
   bound; one table per domain, since projections can run in parallel domains.  Used
   by the bit-vector projection only, whose atoms carry no sort that polymorphic
   comparison cannot compare. *)
let normalize_mbp_cache :
    (Atom.t, Atom.t Set.Poly.t) Hashtbl.t Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> Common.Ext.Hashtbl.PolyDeep.create ())

let normalize_mbp_cache_bound = 4096

let normalize_mbp_memo model atom =
  let tbl = Stdlib.Domain.DLS.get normalize_mbp_cache in
  match Hashtbl.find tbl atom with
  | Some atoms -> atoms
  | None ->
      let consulted = ref false in
      let atoms = normalize_mbp_reading ~consulted model atom in
      if not !consulted then (
        if Hashtbl.length tbl >= normalize_mbp_cache_bound then Hashtbl.clear tbl;
        Hashtbl.set tbl ~key:atom ~data:atoms);
      atoms

(* How large [Formula.elim_ite] would make [phi], saturated at [k].  The estimate follows
   that rewriting: a conditional concatenates its branches and prefixes each with its
   condition, a binary application takes the cartesian product of its arguments, and a
   formula embedded in a term is rewritten in place, so sizes multiply along the nesting.
   Counting branches instead of size is not enough -- a bit-vector circuit of 559 nodes
   with only 32 branches expands to 1.4 million, because the multiplication happens at
   every level below an embedded formula. *)
let ite_blowup_upto k phi =
  let sat n = if n >= k || n < 0 then k else n in
  let rec of_term = function
    (* (branches, size) *)
    | Term.Var _ -> (1, 1)
    | Term.FunApp (T_bool.IfThenElse, [ c; a; b ], _) ->
        let sc = of_formula @@ Formula.of_bool_term c in
        let pa, sa = of_term a and pb, sb = of_term b in
        (sat (pa + pb), sat (sa + (pa * sc) + sb + (pb * sc)))
    | Term.FunApp (T_bool.Formula phi, [], _) -> (1, sat (1 + of_formula phi))
    | Term.FunApp (_, [ t ], _) ->
        let p, s = of_term t in
        (p, sat (s + p))
    | Term.FunApp (_, ts, _) ->
        List.fold ts ~init:(1, 1) ~f:(fun (p, s) t ->
            let p', s' = of_term t in
            (sat (p * p'), sat ((s * p') + (s' * p))))
    | Term.LetTerm (_, _, def, body, _) ->
        (1, sat (1 + snd (of_term def) + snd (of_term body)))
  and of_atom = function
    | Atom.App (_, ts, _) ->
        let p, s =
          List.fold ts ~init:(1, 1) ~f:(fun (p, s) t ->
              let p', s' = of_term t in
              (sat (p * p'), sat ((s * p') + (s' * p))))
        in
        sat (s + p)
    | _ -> 1
  and of_formula = function
    | Formula.Atom (atm, _) -> of_atom atm
    | Formula.UnaryOp (_, phi, _) -> sat (1 + of_formula phi)
    | Formula.BinaryOp (_, phi1, phi2, _) ->
        sat (1 + of_formula phi1 + of_formula phi2)
    | Formula.Bind (_, _, phi, _) -> sat (1 + of_formula phi)
    | Formula.LetFormula (_, _, def, body, _) ->
        sat (1 + snd (of_term def) + of_formula body)
    | Formula.LetRec (_, phi, _) -> of_formula phi
  in
  of_formula phi

(* whether a conditional occurs anywhere in a term, an atom or a formula.  The formula
   embedded in a Bool-sorted term is searched too, since a conditional inside it is one
   the projection has to account for just the same. *)
let rec has_ite = function
  | Term.Var _ -> false
  | Term.FunApp (T_bool.IfThenElse, _, _) -> true
  | Term.FunApp (T_bool.Formula phi, [], _) -> has_ite_in_formula phi
  | Term.FunApp (_, ts, _) -> List.exists ts ~f:has_ite
  | Term.LetTerm (_, _, def, body, _) -> has_ite def || has_ite body

and has_ite_in_formula phi =
  Set.exists (Formula.terms_of phi) ~f:has_ite
  ||
  match phi with
  | Formula.Atom (Atom.App (_, ts, _), _) -> List.exists ts ~f:has_ite
  | _ -> false

let has_ite_in_atom = function
  | Atom.App (_, ts, _) -> List.exists ts ~f:has_ite
  | _ -> false

(* Cut the guards a conditional-resolving pass produced down to a set that still
   implies them all.

   A word-level circuit decodes one control value in many places, so resolving its
   conditionals against a model emits the same condition over and over -- and, around a
   decoder, the whole fan of a variable's other values as separate disequalities:
   i21 <> 14, i21 <> 9, ..., i21 = 5.  The last of those implies every one of the others,
   so all that has to be said is i21 = 5.

   This matters beyond the size of the output.  Resolving a conditional commits the
   projection to the model's branch, and the models that take the other branch are left
   to later calls; each guard that survives is therefore a condition the caller may have
   to come back for.  Cutting the redundant ones costs nothing and leaves fewer to come
   back for.

   Soundness needs only that the kept set still implies the dropped ones and that the
   model satisfies it, which both steps here keep: duplicates say the same thing, and an
   equality to one value implies a disequality to any other. *)
let minimize_guards guards =
  let lits =
    List.dedup_and_sort ~compare:Stdlib.compare
    @@ List.concat_map guards ~f:Formula.conjuncts_list_of
  in
  (* the values a term is equated to by a positive literal, when the value is ground *)
  let fixed =
    List.fold lits ~init:Map.Poly.empty ~f:(fun acc -> function
      | Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _) -> (
          match
            if Set.is_empty (Term.fvs_of t2) then
              Some (t1, t2)
            else if Set.is_empty (Term.fvs_of t1) then Some (t2, t1)
            else None
          with
          | Some (t, v) -> Map.Poly.set acc ~key:t ~data:v
          | None -> acc)
      | _ -> acc)
  in
  if Map.Poly.is_empty fixed then lits
  else
    List.filter lits ~f:(function
      | Formula.UnaryOp
          ( Formula.Not,
            Formula.Atom (Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _), _),
            _ )
      | Formula.Atom (Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _), _) -> (
          let other t v =
            match Map.Poly.find fixed t with
            | Some v' -> Set.is_empty (Term.fvs_of v) && not (Stdlib.(v = v'))
            | None -> false
          in
          not (other t1 t2 || other t2 t1))
      | _ -> true)

(* the model leaves a condition open; the caller falls back on the exhaustive rewriting *)
exception IteModelUndetermined

(* Linear alternative to [Formula.elim_ite], which is exponential in the conditionals of
   an atom: replace a conditional by the branch the model takes, and conjoin its condition
   as a guard.  Under that guard the two are the same term -- sign(M, c) /\ A[ite (c,t,e)]
   and sign(M, c) /\ A[t] have the same models when M satisfies c -- so this substitutes a
   subterm for one of its own subterms and never copies the term around it.  The result is
   therefore no larger than the input, which is what the projection's size requirement
   asks for, and it needs no bound to stay that way.  The guards go outside any negation,
   because the result under-approximates the input: hence the polarity, and hence the else
   branch guards with the projection of the negated condition rather than the negation of
   the projected one.

   [keep] is asked about the whole conditional, and leaves it alone when it answers true.
   The caller uses it for the conditionals that mention no variable being eliminated: for
   those, what the conditional denotes is irrelevant to the elimination, so it is carried
   through as one opaque term and neither branch nor condition is looked at.  Nothing is
   asserted about it either -- emitting its condition as a guard would constrain the other
   variables for no gain, and the result would cover fewer models than it has to.
   A conditional that mentions one of them is resolved, which does weaken the projection:
   the models that take the other branch are left to other calls, up to twice as many of
   them per conditional.  That is the same bargain the projection's other rules make.

   On a word-level circuit the opaque kind is most of them -- 96 of 184 conditionals of
   one input, against 24 variables to remove -- which is also what lets the conditionals
   that do matter be resolved before the let-bound definitions are inlined, where a
   conditional left in place is copied once per use of its definition.

   [lenient] leaves a conditional the model cannot decide in place as well, rather than
   raising: a caller that has nothing exponential to fall back on wants the term back.

   A variable bound inside [phi] (a quantifier, an array lambda, a let) is not the
   model's variable of the same name, so below its binder the model is consulted without
   it -- a condition over it is then one the model cannot decide.  Reading the outer value
   instead picks a branch at a point the binder does not range over only: under
   [forall z.] with the model's [z = -1], [ite (z >= 0, z + 1, 1 - z) >= 1] became
   [forall z. 1 - z >= 1 /\ z < 0], false in a model of the true input; and a guard read
   off the outer value inside a lambda's body escaped the lambda and was captured by the
   free variable, so the result no longer implied the input.  One exception keeps the
   model path through an existential prefix: when the model's values of the bound
   variables make the body true, they are a witness, and the result keeps that witness.

   Pre: the model maps variables to ground terms.  Post, for a [phi] the model satisfies:
   the model satisfies the result, the result implies [phi], and every guard mentions
   only variables free where it is conjoined. *)
let elim_ite_with_model ?(keep = fun _ -> false) ?(lenient = false) model phi =
  let holds model cond =
    let cond = Formula.subst model cond in
    if not @@ Formula.is_ground cond then
      if lenient then None else raise IteModelUndetermined
    else
      try Some (Evaluator.eval @@ Evaluator.simplify cond)
      with exn_ when not (Common.Timer.is_async exn_) ->
        if lenient then None else raise IteModelUndetermined
  in
  (* whether the model's own values make [phi] true: a ground, evaluable yes, never a
     guess *)
  let true_at model phi =
    let phi = Formula.subst model phi in
    Formula.is_ground phi
    &&
    try Evaluator.eval @@ Evaluator.simplify phi
    with exn_ when not (Common.Timer.is_async exn_) -> false
  in
  let without model vars =
    Map.Poly.filter_keys model ~f:(fun v -> not (List.mem vars v ~equal:Ident.tvar_equal))
  in
  (* guards are returned innermost last and conjoined at the enclosing atom, so none of
     them escapes a formula binder; a term binder's guards do leave it, which is sound
     because its body is rewritten under a model without the bound variable, so a guard
     from it cannot mention that variable *)
  let rec of_term model guards = function
    | Term.Var _ as t -> (guards, t)
    | Term.FunApp ((T_array.ALambda ((x, _), _) as fsym), [ body ], info) ->
        let guards, body = of_term (without model [ x ]) guards body in
        (guards, Term.mk_fsym_app ~info fsym [ body ])
    | Term.FunApp (T_bool.IfThenElse, [ c; th; el ], info) as t -> (
        if keep t then (guards, t)
        else
          let cond = Formula.of_bool_term c in
          match holds model cond with
          | Some true -> of_term model (of_formula model true cond :: guards) th
          | Some false -> of_term model (of_formula model false cond :: guards) el
          | None ->
              (* the model cannot decide the condition, so leave the conditional where it
                 is.  Its subterms are still rewritten, and a guard that comes back from a
                 branch is conjoined outside this conditional: sound, because a guard
                 states what the model makes true and, under it, the branch that replaced
                 a conditional below denotes the same term on both sides of [c]. *)
              let guards, c' = of_term model guards c in
              let guards, th' = of_term model guards th in
              let guards, el' = of_term model guards el in
              ( guards,
                if phys_equal c c' && phys_equal th th' && phys_equal el el' then t
                else Term.mk_fsym_app ~info T_bool.IfThenElse [ c'; th'; el' ] ))
    | Term.FunApp (T_bool.Formula phi, [], info) ->
        (guards, Term.mk_fsym_app ~info (T_bool.Formula (of_formula model true phi)) [])
    | Term.FunApp (fsym, ts, info) ->
        let guards, ts = List.fold_map ts ~init:guards ~f:(of_term model) in
        (guards, Term.mk_fsym_app ~info fsym ts)
    | Term.LetTerm (var, sort, def, body, info) ->
        (* only the definition: a guard from [body] can mention [var] *)
        let guards, def = of_term model guards def in
        (guards, Term.mk_let_term ~info var sort def body)
  and of_atom model = function
    | Atom.App (pred, ts, info) ->
        let guards, ts = List.fold_map ts ~init:[] ~f:(of_term model) in
        (guards, Atom.mk_app ~info pred ts)
    | atm -> ([], atm)
  and of_formula model pos phi =
    match phi with
    | Formula.Atom (atm, info) ->
        let guards, atm = of_atom model atm in
        let base =
          if pos then Formula.mk_atom ~info atm
          else Formula.mk_neg @@ Formula.mk_atom ~info atm
        in
        Formula.and_of (base :: minimize_guards guards)
    | Formula.UnaryOp (Not, phi, _) -> of_formula model (not pos) phi
    | Formula.BinaryOp (And, phi1, phi2, _) ->
        let phi1 = of_formula model pos phi1 and phi2 = of_formula model pos phi2 in
        if pos then Formula.mk_and phi1 phi2 else Formula.mk_or phi1 phi2
    | Formula.BinaryOp (Or, phi1, phi2, _) ->
        let phi1 = of_formula model pos phi1 and phi2 = of_formula model pos phi2 in
        if pos then Formula.mk_or phi1 phi2 else Formula.mk_and phi1 phi2
    | Formula.BinaryOp (Imply, phi1, phi2, _) ->
        let phi1 = of_formula model (not pos) phi1
        and phi2 = of_formula model pos phi2 in
        if pos then Formula.mk_or phi1 phi2 else Formula.mk_and phi1 phi2
    | Formula.BinaryOp ((Iff | Xor), phi1, phi2, _) ->
        (* both polarities are needed at once, which one branch cannot supply *)
        if
          (not lenient)
          && (has_ite_in_formula phi1 || has_ite_in_formula phi2)
        then raise IteModelUndetermined
        else if pos then phi
        else Formula.mk_neg phi
    | Formula.Bind (binder, senv, body, info) ->
        let existential =
          match binder with
          | Formula.Exists -> pos
          | Formula.Forall -> not pos
          | Formula.Random _ -> false
        in
        let model =
          if
            existential
            && true_at model (if pos then body else Formula.mk_neg body)
          then model
          else without model (List.map senv ~f:fst)
        in
        let phi = of_formula model pos body in
        if pos then Formula.mk_bind ~info binder senv phi
        else
          Formula.mk_bind ~info
            (match binder with
            | Formula.Forall -> Formula.Exists
            | Formula.Exists -> Formula.Forall
            (* a random binder has no dual to push the negation through, and
               leaving it as it stands would change what the formula says *)
            | Formula.Random _ -> raise IteModelUndetermined)
            senv phi
    | Formula.LetFormula (var, sort, def, body, info) ->
        let guards, def = of_term model [] def in
        (* the body's conditions can test [var], so put its value in the model.  Folded,
           not merely substituted: unfolded definitions copy into each other *)
        let model =
          let value = Evaluator.simplify_term @@ Term.subst model def in
          if Set.is_empty @@ Term.fvs_of value then
            Map.Poly.set model ~key:var ~data:value
          else Map.Poly.remove model var
        in
        Formula.and_of
          (Formula.mk_let_formula ~info var sort def (of_formula model pos body)
          :: minimize_guards guards)
    | Formula.LetRec (_, _, _) ->
        if lenient then if pos then phi else Formula.mk_neg phi
        else raise IteModelUndetermined
  in
  of_formula model true phi

(* The literals a conditional-bearing atom reduces to, once the conditions the
   preprocessing left in place are settled by the model.

   The preprocessing removes every conditional whose condition does not mention a
   variable being eliminated, which costs nothing.  What reaches here is the rest: a
   condition that does mention one, where committing to the model's branch does constrain
   that variable.  It is still the choice the projection's other rules make -- the
   datatype rule picks the constructor test the model satisfies, the real rule picks which
   side of a disequality to strengthen, the integer rule fixes the case split at the
   model's residue -- and the condition itself rejoins the conjunction as a literal about
   that variable, which the theory rules then read like any other.

   Nothing is enumerated and nothing is copied, so this needs no bound. *)
let resolve_ite_in_atom model atm =
  if not @@ has_ite_in_atom atm then Set.Poly.singleton atm
  else
    let phi = elim_ite_with_model ~lenient:true model @@ Formula.mk_atom atm in
    let pos, neg = Formula.atoms_of ~nrec:true phi in
    Set.union pos neg
    |> Set.Poly.map ~f:(fun a ->
        if Evaluator.eval @@ Evaluator.simplify_atom @@ Atom.subst model a then a
        else
          match Atom.negate a with
          | Some neg -> neg
          | None ->
              failwith
              @@ sprintf
                   "[mbp] cannot negate %s: model-based projection expects theory \
                    atoms, not an application of an uninterpreted predicate"
                   (Atom.str_of a))
    |> Set.filter ~f:(Atom.is_true >> not)

(* The definitional form: projecting over a circuit without inlining its definitions.

   The preprocessing this replaces inlines every let-bound definition into each of its
   uses, which is exponential in the sharing -- 1,837 nodes of one input became
   17,917,748 -- and it has to run, because what follows selects the atoms that mention
   the variable being removed, and an atom sitting under a binding does not stand on its
   own.

   The alternative is the definitional encoding of G. S. Tsejtin, "On the complexity of
   derivation in propositional calculus", Studies in Constructive Mathematics and
   Mathematical Logic, Part II, 1968, pp. 115-125 -- taken at the level of terms rather
   than of propositions, which is the same move an SMT preprocessor calls flattening and
   which Z3 and cvc5 both apply to a conditional inside a term.  Name every compound
   subterm by a fresh variable and state the naming as an equation,

     A[t]   is   exists v. v = t /\ A[v]        (v fresh)

   which is an equivalence rather than merely equisatisfiability, and which is linear in
   the shared form.  The fresh variables are existential, so the projection's own rule
   for several variables covers them,

     Mbp(M, xs, phi)  =  Mbp(M', xs ++ vs, phi_flat)

   with M' extending M by evaluating each definition bottom-up -- no solver call -- and
   the result implies exists xs. phi exactly as before.  Nothing beyond the published
   rules is needed: the naming is a preprocessing step that brings a conditional inside a
   term, for which the published syntax has no case at all, into a position the rules do
   cover.

   Every definition is one operator applied to names, variables and constants.  That
   depth is what keeps removing a name cheap: the equality rule substitutes a name's
   definition for the name, and a definition one node deep costs one node per occurrence
   instead of a whole subtree.

   Three steps follow the naming, and the third decides whether this pays.  A definition
   v = ite (c, t, e) is settled against the model into a guard and one branch -- once per
   conditional, rather than once per use of it as the inlining would.  That drops the
   reference the other branch held, so a definition nothing refers to any more can be
   dropped, and with it everything only it referred to.  On a circuit that is the cone of
   influence of the model's own control path, and it is the only thing that keeps the set
   of names still to be removed small.  A name whose definition mentions, directly or
   through other names, none of the variables being removed is then left alone entirely,
   and substituted back once at the end -- the result has to be a plain term, the solver
   interface this feeds having no let.

   What this does not promise: the size requirement holds on the definitional form, where
   the output has at most one equation per definition of the input, and not on the term
   the final substitution rebuilds, whose size is that of the surviving names expanded as
   a tree.  Only the names the result still mentions are expanded, and the projection has
   by then removed most of them. *)
module Flat = struct
  type t = {
    prefix : sort_env_list;
        (** the existential prefix peeled off the input, so that the body can be named at
            all: a term under a binder cannot be given a name outside it *)
    defs : (Ident.tvar * Sort.t * Term.t) list;
        (** dependency order: a definition's arguments are defined before it *)
    body : Formula.t;
    guards : Formula.t list;
        (** the conditions settling the conditionals committed to *)
    facts : Formula.t list;
        (** what the branch the model did not take still says: for a settled
            [v = ite (c, t, e)], the signed comparison of the two branches, which is the
            literal the published rule produces for the atom [v = e] and which settling
            alone would drop *)
    model : term_subst_map;  (** the input's model, extended to the names *)
  }

  (* The prefix is also peeled through a conjunction, by [A /\ exists x. B = exists x.
     (A /\ B)] when x is not free in A.  [Formula.rm_div_mod] returns exactly that shape:
     its top-level restriction -- [true] when every division sits under the prefix --
     conjoined in front of the prefix, with the quotient and remainder variables bound one
     level further in.  Stopping at the conjunction leaves the whole input under a binder:
     nothing in it can be named, and the quotient and remainder variables are neither
     removed nor valued by the model, so every projection of an input with [div] or [mod]
     fails and its caller falls back to the model's point.  A variable that would be
     captured stops the peeling there; the formula is then returned unchanged below that
     point, which is the old behaviour. *)
  let peel_exists phi =
    let rec go acc = function
      | Formula.Bind (Formula.Exists, senv, phi, _) -> go (acc @ senv) phi
      | Formula.BinaryOp (Formula.And, phi1, phi2, info) as phi -> (
          let senv1, phi1' = go [] phi1 in
          let senv2, phi2' = go [] phi2 in
          let bvs senv = Set.Poly.of_list @@ List.map senv ~f:fst in
          let bvs1 = bvs senv1 and bvs2 = bvs senv2 in
          match (senv1, senv2) with
          | [], [] -> (acc, phi)
          | _ ->
              if
                Set.is_empty (Set.inter bvs1 bvs2)
                && Set.is_empty (Set.inter bvs1 (Formula.fvs_of phi2))
                && Set.is_empty (Set.inter bvs2 (Formula.fvs_of phi1))
              then (acc @ senv1 @ senv2, Formula.mk_and ~info phi1' phi2')
              else (acc, phi))
      | phi -> (acc, phi)
    in
    go [] phi

  (* Decide the ground arithmetic atoms and fold the constants through the connectives.
     The other path of the projection runs [Evaluator.simplify], which does this among
     much else; this path cannot, because that also inlines let-bindings.  What it has to
     remove is what [Formula.rm_div_mod] leaves behind: [1 != 0 => ...] for a constant
     divisor and the vacuous [x = y /\ -1 = 0 => ...] relating two divisions by different
     constants.  Left in, the projection signs every atom of them against the model, and
     the antecedent of a vacuous implication then contributes literals about the
     variables that are true of this model only.  Only atoms over integers and reals are
     decided: they are closed arithmetic on numerals once [rm_div_mod] has run, whereas a
     ground term of another sort may have a value only in some interpretation. *)
  let rec fold_ground phi =
    match phi with
    | Formula.Atom (Atom.App (_, ts, _), _)
      when (not @@ List.is_empty ts)
           && List.for_all ts ~f:T_irb.is_sint_sreal
           && Set.is_empty (Formula.fvs_of phi) -> (
        match
          try Some (Evaluator.eval phi)
          with exn when not (Common.Timer.is_async exn) -> None
        with
        | Some true -> Formula.mk_true ()
        | Some false -> Formula.mk_false ()
        | None -> phi)
    | Formula.Atom _ -> phi
    | Formula.UnaryOp (Formula.Not, phi1, info) ->
        let phi1 = fold_ground phi1 in
        if Formula.is_true phi1 then Formula.mk_false ()
        else if Formula.is_false phi1 then Formula.mk_true ()
        else Formula.mk_unop ~info Formula.Not phi1
    | Formula.BinaryOp (Formula.And, phi1, phi2, info) ->
        let phi1 = fold_ground phi1 and phi2 = fold_ground phi2 in
        if Formula.is_false phi1 || Formula.is_false phi2 then
          Formula.mk_false ()
        else if Formula.is_true phi1 then phi2
        else if Formula.is_true phi2 then phi1
        else Formula.mk_and ~info phi1 phi2
    | Formula.BinaryOp (Formula.Or, phi1, phi2, info) ->
        let phi1 = fold_ground phi1 and phi2 = fold_ground phi2 in
        if Formula.is_true phi1 || Formula.is_true phi2 then Formula.mk_true ()
        else if Formula.is_false phi1 then phi2
        else if Formula.is_false phi2 then phi1
        else Formula.mk_or ~info phi1 phi2
    | Formula.BinaryOp (Formula.Imply, phi1, phi2, info) ->
        let phi1 = fold_ground phi1 and phi2 = fold_ground phi2 in
        if Formula.is_false phi1 || Formula.is_true phi2 then Formula.mk_true ()
        else if Formula.is_true phi1 then phi2
        else Formula.mk_imply ~info phi1 phi2
    | Formula.BinaryOp (op, phi1, phi2, info) ->
        Formula.mk_binop ~info op (fold_ground phi1) (fold_ground phi2)
    | Formula.Bind (binder, senv, phi1, info) ->
        Formula.mk_bind ~info binder senv (fold_ground phi1)
    | Formula.LetFormula (x, s, def, body, info) ->
        Formula.mk_let_formula ~info x s def (fold_ground body)
    | Formula.LetRec _ -> phi

  (* Name every compound subterm.  A let-binding is not inlined: its definition is named
     first, and the bound variable becomes an alias for that one name, so a definition
     used k times costs k references rather than k copies.

     A term mentioning a variable bound inside the formula is left unnamed -- a name
     given outside the binder would capture -- and so is a term the model cannot value,
     which is declined one term at a time rather than abandoning the pass. *)
  let flatten model phi =
    let prefix, phi = peel_exists phi in
    let defs = ref [] in
    let model = ref model in
    let fresh sort t =
      match
        try Some (Evaluator.eval_term @@ Term.subst !model t)
        with exn when not (Common.Timer.is_async exn) -> None
      with
      | None -> t
      | Some value ->
          let x = Ident.mk_fresh_tvar ~prefix:(Some "#df") () in
          defs := (x, sort, t) :: !defs;
          model :=
            Map.Poly.set !model ~key:x
              ~data:(Term.of_value (get_dtenv ()) value);
          Term.mk_var x sort
    in
    (* a term mentioning a variable bound inside the formula keeps its place: a name
       given outside the binder would capture it *)
    let name bvs t =
      if Set.is_empty @@ Set.inter (Term.fvs_of t) bvs then
        fresh (Term.sort_of t) t
      else t
    in
    (* Linear arithmetic over the integers and the reals is left whole.  The theory
       rules read it as it stands, so a name for it only adds an elimination step, and
       since a name is given per occurrence it never saves a copy either.  What it does
       is hide the term from the rewriting the rules depend on: a read [select (store a
       i v) j] is resolved to [v] only when [j] is seen to be [i], and with [j] behind a
       name it is not, so the variable inside [v] is left under the read where no rule
       can remove it except by its model value, and the projection becomes a point.  A
       let-bound definition is still named, whatever it is, so a definition used many
       times is not copied. *)
    let is_linear_arith = function
      | T_int.(Neg | Nop | Add | Sub | Mul) | T_real.(RNeg | RAdd | RSub | RMul) ->
          true
      | _ -> false
    in
    let rec of_term lenv bvs t =
      match t with
      | Term.Var (x, _, _) -> (
          match Map.Poly.find lenv x with Some t' -> t' | None -> t)
      | Term.LetTerm (x, _, def, body, _) ->
          of_term
            (Map.Poly.set lenv ~key:x ~data:(of_def lenv bvs def))
            bvs body
      (* a Bool-sorted term carrying a formula is named as well.  It is where a
         conditional's condition lives, and a circuit decodes one control value in many
         places, so leaving it whole is the one place the copying would come back: the
         alias of a Bool-valued let-binding would carry the whole formula to each of its
         uses. *)
      | Term.FunApp (T_bool.Formula phi, [], info) ->
          name bvs @@ T_bool.of_formula ~info @@ of_formula lenv bvs phi
      | Term.FunApp (_, [], _) -> t
      | Term.FunApp (fsym, ts, info) ->
          let t = Term.mk_fsym_app ~info fsym @@ List.map ts ~f:(of_term lenv bvs) in
          if is_linear_arith fsym then t else name bvs t
    (* a let-bound definition is named even where the term itself would not be *)
    and of_def lenv bvs def =
      match of_term lenv bvs def with
      | Term.FunApp (_, _ :: _, _) as t -> name bvs t
      | t -> t
    and of_atom lenv bvs = function
      | Atom.App (pred, ts, info) ->
          Atom.mk_app ~info pred @@ List.map ts ~f:(of_term lenv bvs)
      | atm -> atm
    and of_formula lenv bvs phi =
      match phi with
      | Formula.Atom (atm, info) -> Formula.mk_atom ~info @@ of_atom lenv bvs atm
      | Formula.UnaryOp (op, phi, info) ->
          Formula.mk_unop ~info op @@ of_formula lenv bvs phi
      | Formula.BinaryOp (op, phi1, phi2, info) ->
          Formula.mk_binop ~info op (of_formula lenv bvs phi1)
            (of_formula lenv bvs phi2)
      | Formula.Bind (binder, senv, phi, info) ->
          let bvs = Set.union bvs @@ Set.Poly.of_list @@ List.map senv ~f:fst in
          Formula.mk_bind ~info binder senv @@ of_formula lenv bvs phi
      | Formula.LetFormula (x, _, def, body, _) ->
          of_formula
            (Map.Poly.set lenv ~key:x ~data:(of_def lenv bvs def))
            bvs body
      | Formula.LetRec (_, _, _) -> phi
    in
    let body = of_formula Map.Poly.empty Set.Poly.empty phi in
    { prefix; defs = List.rev !defs; body; guards = []; facts = []; model = !model }

  (* Settle the conditional definitions against the model and, in the same pass, mark the
     names that still have to be removed.

     A definition v = ite (c, t, e) becomes three things: the definition v = t for the
     branch the model takes, the guard sign(M, c), and the comparison sign(M, t = e).

     The first two are licensed by the identity c /\ v = t  =>  v = ite (c, t, e).  The
     guard cannot be dropped in its place: without c the implication fails.

     The third is what the published rule gives and what settling alone would throw away.
     Naming turns the conditional into (c -> v = t) /\ (~c -> v = e), whose atoms are c,
     v = t and v = e; signing all three -- which is what the rule says to do, every atom
     of the formula -- keeps a literal about the branch the model did not take.  Written
     against t rather than v it says the same thing and does not depend on the definition
     being present.  It is a strengthening of an input that already implies the original,
     so it is optional as far as correctness goes; what it costs is that the other branch
     is now referred to, so [prune] can no longer drop it and it reappears in the result.

     Keeping the definition as v = t rather than as the two implications is what decides
     whether the name can be left alone later.  A name is left alone only when its
     definition mentions nothing being removed, and the two implications mention the
     condition and both branches, so under them a conditional would never cut a
     dependency and every name in the circuit would have to be substituted away.

     Only a conditional that depends on a variable being removed is settled.  For the
     others, what the conditional denotes does not bear on the elimination at all, so
     committing to the model's branch would constrain the other variables for no gain;
     those are carried through whole and put back by [expand].

     Settling and marking are one pass because each answers the other.  Which definitions
     depend on a variable being removed is not the syntactic reachability of the circuit:
     settling a multiplexer whose selected input does not depend on that variable cuts the
     dependency.  The definitions are visited in dependency order, so each is settled with
     the marks of everything below it already known. *)
  let settle ?(compare_branches = true) targets t =
    let holds cond =
      let cond = Formula.subst t.model cond in
      if not @@ Formula.is_ground cond then None
      else
        try Some (Evaluator.eval @@ Evaluator.simplify cond)
        with exn when not (Common.Timer.is_async exn) -> None
    in
    (* the comparison of the two branches, signed.  Nothing is emitted when the model
       cannot decide it: the atoms that remain already imply the definition, so leaving
       it out weakens the projection and breaks nothing. *)
    let compare_branches th el =
      if not compare_branches then []
      else
      let phi = Formula.eq th el in
      match holds phi with
      | Some true -> [ phi ]
      | Some false -> [ Evaluator.simplify_neg phi ]
      | None -> []
    in
    let tainted, guards, facts, defs =
      List.fold t.defs ~init:(targets, [], [], [])
        ~f:(fun (tainted, gs, fs, ds) (x, s, def) ->
          let dirty u =
            Fn.non Set.is_empty @@ Set.inter (Term.fvs_of u) tainted
          in
          let mark u tainted = if dirty u then Set.add tainted x else tainted in
          match def with
          | Term.FunApp (T_bool.IfThenElse, [ c; th; el ], _) when dirty def -> (
              let cond = Formula.of_bool_term c in
              match holds cond with
              | Some true ->
                  ( mark th tainted,
                    cond :: gs,
                    compare_branches th el @ fs,
                    (x, s, th) :: ds )
              | Some false ->
                  ( mark el tainted,
                    Evaluator.simplify_neg cond :: gs,
                    compare_branches th el @ fs,
                    (x, s, el) :: ds )
              (* the model leaves the condition open: the conditional stays, and the name
                 with it, for the theory rules to make what they can of *)
              | None -> (Set.add tainted x, gs, fs, (x, s, def) :: ds))
          | _ -> (mark def tainted, gs, fs, (x, s, def) :: ds))
    in
    ( {
        t with
        defs = List.rev defs;
        guards = t.guards @ List.rev guards;
        facts = t.facts @ List.rev facts;
      },
      tainted )

  (* Drop every definition nothing refers to any more, and with it everything only it
     referred to.  One pass from the outermost definition inwards suffices, because a
     definition's arguments are always defined before it.

     The branch comparisons have to seed this as much as the body does: they are what
     still refers to the branch the model did not take, and dropping its definition would
     leave the comparison mentioning a name that nothing defines. *)
  let prune t =
    let live =
      List.fold (List.rev t.defs)
        ~init:
          (Set.union (Formula.fvs_of t.body)
          @@ Set.Poly.union_list
          @@ List.map (t.guards @ t.facts) ~f:Formula.fvs_of)
        ~f:(fun live (x, _, def) ->
          if Set.mem live x then Set.union live (Term.fvs_of def) else live)
    in
    { t with defs = List.filter t.defs ~f:(fun (x, _, _) -> Set.mem live x) }

  (* Substitute the surviving names back, innermost first, and only those the result
     still mentions. *)
  let expand t phi =
    let needed =
      List.fold (List.rev t.defs) ~init:(Formula.fvs_of phi)
        ~f:(fun need (x, _, def) ->
          if Set.mem need x then Set.union need (Term.fvs_of def) else need)
    in
    let sub =
      List.fold t.defs ~init:Map.Poly.empty ~f:(fun sub (x, _, def) ->
          if Set.mem needed x then
            Map.Poly.set sub ~key:x ~data:(Term.subst sub def)
          else sub)
    in
    if Map.Poly.is_empty sub then phi else Formula.subst sub phi

  let def_atom (x, s, def) = Formula.eq (Term.mk_var x s) def
end

let occur tvar rest =
  Map.Poly.existsi rest ~f:(fun ~key ~data:_ ->
      match key with None -> false | Some t -> Set.mem (Term.fvs_of t) tvar)

module FinDom = struct
  let imin a b = if a < b then a else b

  let pow_upto base exp k =
    if k <= 1 then k
    else
      let rec go acc n =
        if acc >= k || n <= 0 then imin k acc
        else go (imin k (acc * base)) (n - 1)
      in
      go 1 exp

  let rec card_upto his sort k =
    if k <= 1 then k
    else if List.exists his ~f:(fun s -> Stdlib.(s = sort)) then k
    else
      match sort with
      | T_int.SInt | T_real.SReal | T_string.SString -> k
      | T_bool.SBool -> imin 2 k
      | T_bv.SBV (Some w) -> pow_upto 2 w k
      | T_bv.SBV None -> imin 1 k
      | T_tuple.STuple sorts ->
          let his = sort :: his in
          List.fold sorts ~init:1 ~f:(fun p sigma ->
              if k <= p then k else imin k (p * card_upto his sigma k))
      | T_array.SArray (idx_s, elem_s) ->
          let his = sort :: his in
          let ei = card_upto his idx_s k in
          let ee = card_upto his elem_s k in
          pow_upto ee ei k
      | T_dt.SDT dt ->
          let his = sort :: his in
          List.fold (Datatype.conses_of dt) ~init:0 ~f:(fun acc cons ->
              if k <= acc then k
              else
                let prod =
                  List.fold (Datatype.sorts_of_cons dt cons) ~init:1
                    ~f:(fun p sigma ->
                      if k <= p then k else imin k (p * card_upto his sigma k))
                in
                imin k (acc + prod))
      | _ -> imin 1 k

  let rec val_eq v1 v2 =
    match (v1, v2) with
    | Value.BV (s1, b1), Value.BV (s2, b2) -> (
        match (s1, s2) with
        | Some w1, Some w2 -> w1 = w2 && Z.Compare.(b1 = b2)
        | _ -> Z.Compare.(b1 = b2))
    | Value.TupleCons vs1, Value.TupleCons vs2 -> (
        match List.for_all2 vs1 vs2 ~f:val_eq with
        | Ok b -> b
        | Unequal_lengths -> assert false)
    | Value.DTCons (n1, _, vs1), Value.DTCons (n2, _, vs2) -> (
        String.(n1 = n2)
        &&
        match List.for_all2 vs1 vs2 ~f:val_eq with
        | Ok b -> b
        | Unequal_lengths -> assert false)
    | _ -> Value.eq v1 v2

  let group_by_value model terms =
    List.fold terms ~init:[] ~f:(fun classes t ->
        let v = Evaluator.eval_term @@ Term.subst model t in
        let rec add = function
          | [] -> [ (v, [ t ]) ]
          | (v', ts) :: rest ->
              if val_eq v v' then (v', t :: ts) :: rest
              else (v', ts) :: add rest
        in
        add classes)
    |> List.map ~f:snd

  let mk_eq t1 t2 = Atom.mk_app (Predicate.Psym T_bool.Eq) [ t1; t2 ]

  let diseq_atom x = function
    | Atom.App (Predicate.Psym T_bool.Neq, [ Term.Var (y, _, _); t ], _)
      when Ident.tvar_equal y x && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some t
    | Atom.App (Predicate.Psym T_bool.Neq, [ t; Term.Var (y, _, _) ], _)
      when Ident.tvar_equal y x && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some t
    | _ -> None

  let elim_diseq ~print model x sort atoms =
    let partners, rest =
      Set.fold atoms ~init:([], Set.Poly.empty) ~f:(fun (ps, rs) atom ->
          match diseq_atom x atom with
          | Some t -> (t :: ps, rs)
          | None -> (ps, Set.add rs atom))
    in
    let n = List.length partners in
    if card_upto [] sort (n + 1) > n then (
      print
      @@ lazy
           (sprintf "[mbp findom] %s: n=%d < |D| -> top" (Ident.name_of_tvar x)
              n);
      rest)
    else (
      print
      @@ lazy
           (sprintf "[mbp findom] %s: n=%d >= |D| -> class eqs"
              (Ident.name_of_tvar x) n);
      let eqs =
        List.concat_map (group_by_value model partners) ~f:(function
          | rep :: others -> List.map others ~f:(fun t -> mk_eq rep t)
          | [] -> [])
      in
      Set.union rest (Set.Poly.of_list eqs))
end

module LRA = struct
  let let_sort names =
    Map.Poly.fold ~init:Map.Poly.empty ~f:(fun ~key:tvar ~data:term model ->
        if Set.mem names (Ident.name_of_tvar tvar) then model (*ToDo*)
        else
          let data =
            match Evaluator.eval_term term with
            | Value.Bool b -> T_bool.make b
            | Value.Int n -> T_real.mk_real (Q.of_bigint n) (*ToDo*)
            | Value.Real r -> T_real.mk_real r
            | Value.BV (size, n) -> T_bv.mk_bvnum ~size n
            (* an array, a tuple, a datatype or a sequence value stays the
               model's term: the projections of those sorts read it as a
               term, and the arithmetic ones never look inside it *)
            | Value.Arr _ | Value.TupleCons _ | Value.DTCons _ | Value.Seq _ ->
                term
          in
          Map.Poly.add_exn model ~key:tvar ~data)

  let eq_atom tvar = function
    | Atom.App (Predicate.Psym T_bool.Eq, [ t; _ ], _) -> (
        match
          AffineTerm.find_var_monomial (Term.mk_var tvar T_real.SReal)
          @@ Normalizer.linear_real_monomials_of (Value.Real Q.one) t
        with
        | Some (c, rest) ->
            if occur tvar rest then raise NotNormalized;
            Option.return @@ AffineTerm.mk_real_term
            @@ Map.Poly.map rest ~f:(Fn.flip Value.rdiv (Value.neg c))
        | None -> None)
    | _ -> None

  let neq_atom tvar = function
    | Atom.App (Predicate.Psym T_bool.Neq, [ t; _ ], _) as atm -> (
        match
          AffineTerm.find_var_monomial (Term.mk_var tvar T_real.SReal)
          @@ Normalizer.linear_real_monomials_of (Value.Real Q.one) t
        with
        | Some (c, rest) ->
            if occur tvar rest then raise NotNormalized;
            First
              (AffineTerm.mk_real_term
              @@ Map.Poly.map rest ~f:(Fn.flip Value.rdiv (Value.neg c)))
        | None -> Second atm)
    | atm -> Second atm

  (* Splits the atoms into upper bounds, lower bounds and the rest.  The zero-coefficient
     [failwith] is unreachable: [Normalizer.linear_real_monomials_of] drops every
     monomial whose coefficient is zero ([PolyTerm.real_simplify], after the
     coefficients are summed), so a monomial of [tvar] that is found has a nonzero
     coefficient; [x - x >= 0] has no monomial of [x] and goes to the rest.  The same
     holds of the integer [ub_and_lb] through [PolyTerm.int_simplify]. *)
  let ub_and_lb tvar =
    Set.fold ~init:(Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)
      ~f:(fun (ub, lb, others) -> function
      | Atom.App (Predicate.Psym (T_real.(RGeq | RGt) as op), [ t; _ ], _) as
        atom -> (
          match
            AffineTerm.find_var_monomial (Term.mk_var tvar T_real.SReal)
            @@ Normalizer.linear_real_monomials_of (Value.Real Q.one) t
          with
          | Some (Real r, rest) ->
              if occur tvar rest then raise NotNormalized;
              let eps =
                match op with
                | T_real.RGeq -> false
                | T_real.RGt -> true
                | _ -> assert false
              in
              let t =
                AffineTerm.mk_real_term
                @@ Map.Poly.map rest
                     ~f:(Fn.flip Value.rdiv (Value.neg (Real r)))
              in
              if Q.(r < zero) then (Set.add ub (t, eps), lb, others)
              else if Q.(r > zero) then (ub, Set.add lb (t, eps), others)
              else failwith "ub_and_lb"
          | _ -> (ub, lb, Set.add others atom))
      | atom -> (ub, lb, Set.add others atom))

  let lt (r1, eps1) (r2, eps2) = Q.(r1 < r2) || (Q.(r1 = r2) && eps1 && not eps2)

  let lub model ub =
    match
      Set.fold
        ~init:(None, (Q.inf, false))
        ub
        ~f:(fun (lub, (lub_val, lub_eps)) (t, eps) ->
          match Evaluator.eval_term @@ Term.subst model t with
          | Real r ->
              if lt (r, eps) (lub_val, lub_eps) then (Some t, (r, eps))
              else (lub, (lub_val, lub_eps))
          | _ -> failwith "lub")
    with
    | None, _ -> None
    | Some t, (_, eps) -> Some (t, eps)

  let gt (r1, eps1) (r2, eps2) = Q.(r1 > r2) || (Q.(r1 = r2) && eps1 && not eps2)

  let glb model lb =
    match
      Set.fold
        ~init:(None, (Q.minus_inf, false))
        lb
        ~f:(fun (glb, (glb_val, glb_eps)) (t, eps) ->
          match Evaluator.eval_term @@ Term.subst model t with
          | Real r ->
              if gt (r, eps) (glb_val, glb_eps) then (Some t, (r, eps))
              else (glb, (glb_val, glb_eps))
          | _ -> failwith "glb")
    with
    | None, _ -> None
    | Some t, (_, eps) -> Some (t, eps)

  let model_based_projection ~print model tvar atoms =
    match Set.find_map atoms ~f:(eq_atom tvar) with
    | Some t ->
        let sub = Map.Poly.singleton tvar t in
        Set.concat_map atoms ~f:(Atom.subst sub >> normalize_mbp model)
    | None -> (
        let atoms =
          Set.Poly.map atoms
            ~f:
              ( neq_atom tvar >> function
                | First t ->
                    let tx = Term.mk_var tvar T_real.SReal in
                    Normalizer.normalize_atom
                    @@
                    let lhs =
                      Evaluator.eval_term @@ Map.Poly.find_exn model tvar
                    in
                    let rhs = Evaluator.eval_term @@ Term.subst model t in
                    if Value.gt lhs rhs then T_real.mk_rgt tx t
                    else if Value.lt lhs rhs then T_real.mk_rgt t tx
                    else failwith "elim_neq"
                | Second atm -> atm )
        in
        let ub, lb, rest = ub_and_lb tvar atoms in
        (* The witness substituted below into [rest] is the midpoint of [glb] and
           [lub] (or one past the single bound), which is a witness for the bounds
           only.  An atom of [rest] that still mentions [tvar] -- a read [a[tvar]]
           of an array with a real index, which no bound rule reads -- need not hold
           at it: the midpoint is neither the model's value, so the result can be
           false in the model, nor below every upper bound off the model, since the
           result does not require [lub] to stay the least one; with [0 <= x <= y],
           [x <= w] and [a[x] = 1] the result [a[y / 2] = 1] holds at [y = 10, w = 0,
           a[5] = 1], where no [x] fits.  Such a variable is eliminated by its model
           value instead, as the integer projection does. *)
        if Set.exists rest ~f:(fun atm -> Set.mem (Atom.fvs_of atm) tvar) then
          match Map.Poly.find model tvar with
          | Some v ->
              let sub = Map.Poly.singleton tvar v in
              Set.concat_map atoms ~f:(Atom.subst sub >> normalize_mbp model)
          | None -> raise NotNormalized
        else
        let lub = lub model ub in
        let glb = glb model lb in
        print
        @@ lazy
             (sprintf "[mbp lra] lb: %s"
             @@ String.concat_map_set ~sep:", " lb ~f:(fun (t, eps) ->
                 sprintf "%s %s %s" (Term.str_of t)
                   (if eps then "<" else "<=")
                   (Ident.name_of_tvar tvar)));
        print
        @@ lazy
             (sprintf "[mbp lra] ub: %s"
             @@ String.concat_map_set ~sep:", " ub ~f:(fun (t, eps) ->
                 sprintf "%s %s %s" (Term.str_of t)
                   (if eps then ">" else ">=")
                   (Ident.name_of_tvar tvar)));
        (match glb with
        | None -> ()
        | Some (t, eps) ->
            print
            @@ lazy
                 (sprintf "[mbp lra] glb: %s %s %s" (Term.str_of t)
                    (if eps then "<" else "<=")
                    (Ident.name_of_tvar tvar)));
        (match lub with
        | None -> ()
        | Some (t, eps) ->
            print
            @@ lazy
                 (sprintf "[mbp lra] lub: %s %s %s" (Term.str_of t)
                    (if eps then ">" else ">=")
                    (Ident.name_of_tvar tvar)));
        print
        @@ lazy
             (sprintf "[mbp lra] rest: %s"
             @@ String.concat_map_set ~sep:", " rest ~f:(fun atm ->
                 sprintf "%s" (Atom.str_of atm)));
        match (lub, glb) with
        | Some (lub, _), Some (glb, glb_eps) ->
            Set.Poly.union_list
              [
                (let sub =
                   Map.Poly.singleton tvar
                   @@ T_real.mk_rmul (T_real.mk_radd lub glb)
                        (T_real.mk_real (Q.of_float 0.5))
                 in
                 Set.Poly.map rest ~f:(Atom.subst sub));
                Set.concat_map lb ~f:(fun (t, eps) ->
                    normalize_mbp model
                    @@
                    if Stdlib.(glb_eps = eps) || glb_eps (*ToDo*) then
                      T_real.mk_rgeq glb t
                    else T_real.mk_rgt glb t);
                Set.concat_map ub ~f:(fun (t, eps) ->
                    normalize_mbp model
                    @@
                    if (not glb_eps) && not eps then T_real.mk_rgeq t glb
                    else T_real.mk_rgt t glb);
              ]
        | Some (lub, lub_eps), None ->
            Set.union
              (let sub =
                 Map.Poly.singleton tvar @@ T_real.mk_rsub lub (T_real.rone ())
               in
               Set.Poly.map rest ~f:(Atom.subst sub))
              (Set.concat_map ub ~f:(fun (t, eps) ->
                   normalize_mbp model
                   @@
                   if Stdlib.(lub_eps = eps) || lub_eps (*ToDo*) then
                     T_real.mk_rgeq t lub
                   else T_real.mk_rgt t lub))
        | None, Some (glb, glb_eps) ->
            Set.union
              (let sub =
                 Map.Poly.singleton tvar @@ T_real.mk_radd glb (T_real.rone ())
               in
               Set.Poly.map rest ~f:(Atom.subst sub))
              (Set.concat_map lb ~f:(fun (t, eps) ->
                   normalize_mbp model
                   @@
                   if Stdlib.(glb_eps = eps) || glb_eps (*ToDo*) then
                     T_real.mk_rgeq glb t
                   else T_real.mk_rgt glb t))
        | None, None ->
            let sub = Map.Poly.singleton tvar @@ Term.mk_dummy T_real.SReal in
            Set.Poly.map rest ~f:(Atom.subst sub))
end

module LIA = struct
  let let_sort names =
    Map.Poly.fold ~init:Map.Poly.empty ~f:(fun ~key:tvar ~data:term model ->
        if Set.mem names (Ident.name_of_tvar tvar) then model (*ToDo*)
        else
          let data =
            match Evaluator.eval_term term with
            | Value.Bool b -> T_bool.make b
            | Value.Int n -> T_int.mk_int n
            | Value.Real _ -> failwith "LIA: real not supported"
            | Value.BV (size, n) -> T_bv.mk_bvnum ~size n
            (* an array, a tuple, a datatype or a sequence value stays the
               model's term: the projections of those sorts read it as a
               term, and the arithmetic ones never look inside it *)
            | Value.Arr _ | Value.TupleCons _ | Value.DTCons _ | Value.Seq _ ->
                term
          in
          Map.Poly.add_exn model ~key:tvar ~data)

  let is_pdiv tvar = function
    | Atom.App (Predicate.Psym (T_int.(PDiv | NotPDiv) as psym), [ d; t ], _) as
      atm -> (
        match
          AffineTerm.find_var_monomial (Term.mk_var tvar T_int.SInt)
          @@ Normalizer.linear_int_monomials_of (Value.Int Z.one) t
        with
        | Some (c, rest) ->
            if occur tvar rest then raise NotNormalized;
            First (psym, Evaluator.eval_term d, c, rest)
        | None -> Second atm)
    | atm -> Second atm

  (* Pre: every divisor in [pdivs] is a nonzero integer constant, so [lcm > 0] and the
     remainder and quotient below are defined.  No frontend, reader or decoder builds a
     divisibility atom: the only ones are made in this module -- by [resolve], whose
     divisor is a bound's coefficient, positive by [ub_and_lb]; by [pdiv_of_not_pdiv],
     which keeps the divisor of the negated atom; and below, which keeps [d] -- and
     every coefficient [ub_and_lb] returns is nonzero.  A divisor of zero ([0 | t],
     meaning [t = 0]) would have to be handed in from outside; it is not supported, and
     [pdiv_of_not_pdiv] fails on its negation the same way. *)
  let rm_pdiv ~print pdivs model tvar =
    let lcm =
      Set.fold pdivs ~init:Z.one ~f:(fun d1 -> function
        | _, Value.Int d2, _, _ -> Z.lcm d1 d2
        | _ -> d1)
    in
    print @@ lazy ("[mbp lia] lcm: " ^ Z.to_string lcm);
    let varmodel = Term.subst model (Term.mk_var tvar T_int.SInt) in
    let u_val =
      Evaluator.eval_term
      @@ T_int.mk_rem Value.Euclidean varmodel (T_int.mk_int lcm)
    in
    let u = Term.of_value (get_dtenv ()) u_val in
    let newtvar = Ident.mk_fresh_tvar () in
    let newterm =
      T_int.(mk_add u (mk_mul (mk_int lcm) (Term.mk_var newtvar SInt)))
    in
    (* The fresh variable must be bound in the model handed to the recursive call: an atom
       no bound rule reads (an array read [a[x]], a product [x * y]) makes that call
       eliminate it by its model value, and without one the call raised [NotNormalized] on
       [2 | x /\ 0 <= x /\ a[x] = 1].  The value [(M(x) - u) div lcm] is exact, since
       [u = M(x) mod lcm] (Euclidean, [lcm > 0]), so [u + lcm * newvalue = M(x)] and the
       extended model still satisfies every atom after the substitution. *)
    let newmodel =
      let newvalue =
        Term.of_value (get_dtenv ())
        @@ Evaluator.eval_term
        @@ T_int.(mk_div Value.Euclidean (mk_sub varmodel u) (mk_int lcm))
      in
      print
      @@ lazy
           (sprintf "[mbp lia] newvar: %s |-> %s"
              (Ident.name_of_tvar newtvar)
              (Term.str_of newvalue));
      Map.Poly.add_exn model ~key:newtvar ~data:newvalue
    in
    let pdivs =
      Set.Poly.map pdivs ~f:(function
        | T_int.PDiv, d, c, t ->
            Normalizer.normalize_atom
            @@ Atom.mk_app (Predicate.Psym T_int.PDiv)
                 [
                   Term.of_value (get_dtenv ()) d;
                   T_int.mk_add
                     (T_int.mk_int
                        Z.(mul (Value.int_of c) (Value.int_of u_val)))
                     (AffineTerm.mk_int_term t);
                 ]
        | psym, _, _, _ ->
            failwith
            @@ sprintf "[rm_pdiv] %s not supported" (Predicate.str_of_psym psym))
    in
    (newmodel, newtvar, newterm, pdivs)

  let eq_atom tvar = function
    | Atom.App (Predicate.Psym T_bool.Eq, [ t; _ ], _) as atm -> (
        match
          AffineTerm.find_var_monomial (Term.mk_var tvar T_int.SInt)
          @@ Normalizer.linear_int_monomials_of (Value.Int Z.one) t
        with
        | Some (c, rest) ->
            if occur tvar rest then raise NotNormalized;
            if
              Map.Poly.for_all rest ~f:(fun v ->
                  Z.Compare.(Value.(int_of @@ rem Euclidean v c = Z.zero)))
            then
              Some
                ( Z.one,
                  AffineTerm.mk_int_term
                  @@ Map.Poly.map rest
                       ~f:(Fn.flip (Value.div Value.Euclidean) (Value.neg c)),
                  atm )
            else if Z.Compare.(Value.int_of c > Z.zero) then
              Some
                ( Value.int_of c,
                  AffineTerm.mk_int_term
                  @@ Map.Poly.map rest ~f:(Fn.flip Value.mul (Int Z.minus_one)),
                  atm )
            else Some (Z.(-Value.int_of c), AffineTerm.mk_int_term rest, atm)
        | _ -> None)
    | _ -> None

  let neq_atom tvar = function
    | Atom.App (Predicate.Psym T_bool.Neq, [ t; _ ], _) as atm -> (
        match
          AffineTerm.find_var_monomial (Term.mk_var tvar T_int.SInt)
          @@ Normalizer.linear_int_monomials_of (Value.Int Z.one) t
        with
        | Some (c, rest) ->
            if occur tvar rest then raise NotNormalized;
            if
              Map.Poly.for_all rest ~f:(fun v ->
                  Z.Compare.(Value.(int_of @@ rem Euclidean v c = Z.zero)))
            then
              First
                ( Z.one,
                  AffineTerm.mk_int_term
                  @@ Map.Poly.map rest
                       ~f:(Fn.flip (Value.div Value.Euclidean) (Value.neg c)) )
            else if Z.Compare.(Value.int_of c > Z.zero) then
              First
                ( Value.int_of c,
                  AffineTerm.mk_int_term
                  @@ Map.Poly.map rest ~f:(Fn.flip Value.mul (Int Z.minus_one))
                )
            else First (Z.(-Value.int_of c), AffineTerm.mk_int_term rest)
        | None -> Second atm)
    | atm -> Second atm

  let ub_and_lb tvar =
    Set.fold ~init:(Set.Poly.empty, Set.Poly.empty, Set.Poly.empty)
      ~f:(fun (ub, lb, others) -> function
      | Atom.App (Predicate.Psym T_int.Geq, [ t; _ ], _) as atom -> (
          match
            AffineTerm.find_var_monomial (Term.mk_var tvar T_int.SInt)
            @@ Normalizer.linear_int_monomials_of (Value.Int Z.one) t
          with
          | Some (Int n, rest) ->
              if occur tvar rest then raise NotNormalized;
              if Z.Compare.(n < Z.zero) then
                (Set.add ub (Z.(-n), AffineTerm.mk_int_term rest), lb, others)
              else if Z.Compare.(n > Z.zero) then
                ( ub,
                  Set.add lb
                    ( n,
                      AffineTerm.mk_int_term
                      @@ Map.Poly.map rest
                           ~f:(Fn.flip Value.mul (Int Z.minus_one)) ),
                  others )
              else failwith "ub_and_lb"
          | _ -> (ub, lb, Set.add others atom))
      | atom -> (ub, lb, Set.add others atom))

  let lub model ub =
    fst
    @@ Set.fold ub ~init:(None, Q.inf) ~f:(fun (lub, lub_val) (c, t) ->
        let tv = Evaluator.eval_term @@ Term.subst model t in
        let v = Q.make (Value.int_of tv) c in
        if Q.(lub_val > v) then (Some (c, t), v) else (lub, lub_val))

  let glb model lb =
    fst
    @@ Set.fold lb ~init:(None, Q.minus_inf) ~f:(fun (glb, glb_val) (c, t) ->
        let tv = Evaluator.eval_term @@ Term.subst model t in
        let v = Q.make (Value.int_of tv) c in
        if Q.(glb_val < v) then (Some (c, t), v) else (glb, glb_val))

  (* resolve(M, ax <= t, bx >= s) *)
  let resolve model av t bv s =
    let tv = Value.int_of @@ Evaluator.eval_term (Term.subst model t) in
    let sv = Value.int_of @@ Evaluator.eval_term (Term.subst model s) in
    let btt = T_int.mk_mul (T_int.mk_int bv) t in
    let ast = T_int.mk_mul (T_int.mk_int av) s in
    let a_1b_1 = Z.((av - one) * (bv - one)) in
    let bt_as = Z.((bv * tv) - (av * sv)) in
    if Z.Compare.(a_1b_1 <= bt_as) then
      Set.Poly.singleton
      @@ T_int.mk_leq (T_int.mk_add ast (T_int.mk_int a_1b_1)) btt
    else if Z.Compare.(av >= bv) then
      let d = Z.erem (Z.neg sv) bv in
      let sd = T_int.mk_add s (T_int.mk_int d) in
      Set.Poly.of_list
        [
          T_int.mk_leq ast btt;
          T_int.mk_pdiv (T_int.mk_int bv) sd;
          T_int.(mk_leq (mk_mul (mk_int av) sd) btt);
        ]
    else
      let d = Z.erem tv av in
      let td = T_int.mk_sub t (T_int.mk_int d) in
      Set.Poly.of_list
        [
          T_int.mk_leq ast btt;
          T_int.mk_pdiv (T_int.mk_int av) td;
          T_int.(mk_leq ast (mk_mul (mk_int bv) td));
        ]

  let model_based_projection_by_bounds ~print model tvar ub lb rest =
    print
    @@ lazy
         ("[mbp lia] ub: "
         ^ List.to_string
             ~f:(fun (t1, t2) -> Z.to_string t1 ^ "," ^ Term.str_of t2)
             (Set.to_list ub));
    print
    @@ lazy
         ("[mbp lia] lb: "
         ^ List.to_string
             ~f:(fun (t1, t2) -> Z.to_string t1 ^ "," ^ Term.str_of t2)
             (Set.to_list lb));
    print
    @@ lazy
         ("[mbp lia] rest: " ^ List.to_string ~f:Atom.str_of (Set.to_list rest));
    (* if Set.mem (Set.concat_map ~f:Formula.fvs_of rest) tvar then
       let sub = Map.Poly.singleton tvar (Map.Poly.find_exn model tvar) in
       Set.concat_map atoms ~f:(Atom.subst sub >> Formula.mk_atom)
       else *)
    match (lub model ub, glb model lb) with
    | Some (cub, tub), Some (clb, tlb) ->
        let lbformulas =
          Set.Poly.map lb ~f:(fun (c, t) ->
              T_int.mk_leq
                (T_int.mk_mul t @@ T_int.mk_int clb)
                (T_int.mk_mul tlb @@ T_int.mk_int c))
        in
        let ubformulas =
          Set.concat_map ub ~f:(fun (c, t) -> resolve model c t clb tlb)
        in
        let rest =
          let sub =
            let glb = T_int.mk_div Value.Euclidean tlb @@ T_int.mk_int clb in
            let lub =
              T_int.(mk_add (mk_div Value.Euclidean tub @@ mk_int cub) (one ()))
            in
            Map.Poly.singleton tvar
              T_int.(mk_div Value.Euclidean (mk_add glb lub) (from_int 2))
          in
          Set.Poly.map rest ~f:(Atom.subst sub)
        in
        print
        @@ lazy
             ("[mbp lia] lbformulas: "
             ^ String.concat_map_set ~sep:", " ~f:Atom.str_of lbformulas);
        print
        @@ lazy
             ("[mbp lia] ubformulas: "
             ^ String.concat_map_set ~sep:", " ~f:Atom.str_of ubformulas);
        Set.concat_map ~f:(normalize_mbp model)
        @@ Set.Poly.union_list [ lbformulas; ubformulas; rest ]
    | Some (cub, tub), None ->
        let ubformulas =
          Set.Poly.map ub ~f:(fun (c, t) ->
              T_int.mk_leq
                (T_int.mk_mul tub @@ T_int.mk_int c)
                (T_int.mk_mul t @@ T_int.mk_int cub))
        in
        let rest =
          let sub =
            Map.Poly.singleton tvar
            @@ T_int.mk_div Value.Euclidean tub
            @@ T_int.mk_int cub
          in
          Set.Poly.map rest ~f:(Atom.subst sub)
        in
        Set.concat_map ~f:(normalize_mbp model)
        @@ Set.Poly.union_list [ ubformulas; rest ]
    | None, Some (clb, tlb) ->
        let lbformulas =
          Set.Poly.map lb ~f:(fun (c, t) ->
              T_int.mk_leq
                (T_int.mk_mul t @@ T_int.mk_int clb)
                (T_int.mk_mul tlb @@ T_int.mk_int c))
        in
        let rest =
          let sub =
            Map.Poly.singleton tvar
            @@ T_int.mk_add
                 (T_int.mk_div Value.Euclidean tlb @@ T_int.mk_int clb)
                 (T_int.one ())
          in
          Set.Poly.map rest ~f:(Atom.subst sub)
        in
        Set.concat_map ~f:(normalize_mbp model)
        @@ Set.Poly.union_list [ lbformulas; rest ]
    | None, None ->
        let sub = Map.Poly.singleton tvar @@ Term.mk_dummy T_int.SInt in
        Set.Poly.map rest ~f:(Atom.subst sub)

  let model_based_projection_aux ~print model tvar atoms =
    let ub, lb, rest = ub_and_lb tvar atoms in
    (* a bound witness substituted into an atom outside linear arithmetic (e.g. an array store
       that fixes [tvar]) need not hold in the model; such a variable is eliminated by its model
       value instead, as in the ARR+LIA projection of Komuravelli et al. (2015) *)
    if Set.exists rest ~f:(fun atm -> Set.mem (Atom.fvs_of atm) tvar) then
      match Map.Poly.find model tvar with
      | Some v ->
          let sub = Map.Poly.singleton tvar v in
          Set.concat_map atoms ~f:(Atom.subst sub >> normalize_mbp model)
      | None -> raise NotNormalized
    else model_based_projection_by_bounds ~print model tvar ub lb rest

  let rec model_based_projection ~print model tvar atoms =
    match Set.find_map atoms ~f:(eq_atom tvar) with
    | Some (c, t, atom) ->
        if Z.Compare.(c = Z.one) then
          let sub = Map.Poly.singleton tvar t in
          Set.concat_map atoms ~f:(Atom.subst sub >> normalize_mbp model)
        else
          let cx = T_int.(mk_mul (mk_int c) @@ Term.mk_var tvar SInt) in
          model_based_projection ~print model tvar
          @@ Set.union (Set.remove atoms atom)
          @@ Set.concat_map ~f:(normalize_mbp model)
          @@ Set.Poly.of_list [ T_int.mk_geq t cx; T_int.mk_geq cx t ]
    | None ->
        let atoms =
          Set.Poly.map atoms
            ~f:
              ( neq_atom tvar >> function
                | First (c, t) ->
                    let cx =
                      T_int.(mk_mul (mk_int c) @@ Term.mk_var tvar SInt)
                    in
                    Normalizer.normalize_atom
                    @@
                    let lhs = Evaluator.eval_term @@ Term.subst model cx in
                    let rhs = Evaluator.eval_term @@ Term.subst model t in
                    if Value.gt lhs rhs then T_int.mk_gt cx t
                    else if Value.lt lhs rhs then T_int.mk_gt t cx
                    else failwith "elim_neq"
                | Second atm -> atm )
        in
        let atoms =
          Set.Poly.map atoms ~f:(function
            | Atom.App (Predicate.Psym T_int.NotPDiv, [ d; t ], _)
              when T_int.is_int d && Set.mem (Term.fvs_of t) tvar ->
                pdiv_of_not_pdiv model d t
            | atm -> atm)
        in
        let pdivs, rest = Set.partition_map atoms ~f:(is_pdiv tvar) in
        if Set.is_empty pdivs then
          model_based_projection_aux ~print model tvar rest
        else
          let newmodel, newtvar, newterm, pdivs =
            rm_pdiv ~print pdivs model tvar
          in
          print
          @@ lazy
               (sprintf "[mbp lia] newterm: %s -> %s" (Ident.name_of_tvar tvar)
                  (Term.str_of newterm));
          print
          @@ lazy (sprintf "[mbp lia] newmodel: %s" (TermSubst.str_of newmodel));
          Set.union (Set.concat_map pdivs ~f:(normalize_mbp model))
          @@ model_based_projection ~print newmodel newtvar
          @@
          let sub = Map.Poly.singleton tvar newterm in
          Set.concat_map rest ~f:(Atom.subst sub >> normalize_mbp model)
end

module Boolean = struct
  let let_sort names =
    Map.Poly.fold ~init:Map.Poly.empty ~f:(fun ~key:tvar ~data:term model ->
        if Set.mem names (Ident.name_of_tvar tvar) then model (*ToDo*)
        else
          let data =
            match Evaluator.eval_term term with
            | Value.Bool b -> T_bool.make b
            | Value.Int _ -> failwith "Boolean: int not supported"
            | Value.Real _ -> failwith "Boolean: real not supported"
            | Value.BV (size, n) -> T_bv.mk_bvnum ~size n
            (* an array, a tuple, a datatype or a sequence value stays the
               model's term: the projections of those sorts read it as a
               term, and the arithmetic ones never look inside it *)
            | Value.Arr _ | Value.TupleCons _ | Value.DTCons _ | Value.Seq _ ->
                term
          in
          Map.Poly.add_exn model ~key:tvar ~data)

  let eq_atom tvar = function
    | Atom.App (Predicate.Psym T_bool.Eq, [ Term.Var (x, _, _); t ], _)
      when Ident.tvar_equal x tvar && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some t
    | Atom.App (Predicate.Psym T_bool.Eq, [ t; Term.Var (x, _, _) ], _)
      when Ident.tvar_equal x tvar && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some t
    | Atom.App (Predicate.Psym T_bool.Neq, [ Term.Var (x, _, _); t ], _)
      when Ident.tvar_equal x tvar && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some (Evaluator.simplify_term @@ T_bool.negate t)
    | Atom.App (Predicate.Psym T_bool.Neq, [ t; Term.Var (x, _, _) ], _)
      when Ident.tvar_equal x tvar && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some (Evaluator.simplify_term @@ T_bool.negate t)
    | _ -> None

  let model_based_projection ~print:_ model tvar atoms =
    match Set.find_map atoms ~f:(eq_atom tvar) with
    | Some t ->
        let sub = Map.Poly.singleton tvar t in
        Set.concat_map atoms ~f:(Atom.subst sub >> normalize_mbp model)
    | None ->
        if Set.exists atoms ~f:(fun atom -> Set.mem (Atom.fvs_of atom) tvar)
        then raise NotNormalized
          (*failwith @@ "no constraint on " ^ Ident.name_of_tvar tvar*)
        else atoms (* reachable here when simplification eliminated tvar *)
end

module BV = struct
  (* Canonicalize a model returned by the SMT solver into literal terms, one per
     variable, dropping the entries whose name is in [names] (the clause
     indicators the caller added to the query, which are not variables of the
     formula).  A bit-vector prefix may still carry Boolean variables -- the
     projection loop sends those to the Boolean module -- so both values are
     accepted here and everything else is a variable the bit-vector projection
     was never meant to see. *)
  let let_sort names =
    Map.Poly.fold ~init:Map.Poly.empty ~f:(fun ~key:tvar ~data:term model ->
        if Set.mem names (Ident.name_of_tvar tvar) then model (*ToDo*)
        else
          let data =
            match Evaluator.eval_term term with
            | Value.Bool b -> T_bool.make b
            | Value.BV (size, n) -> T_bv.mk_bvnum ~size n
            | Value.Int _ -> failwith "BV: int not supported"
            | Value.Real _ -> failwith "BV: real not supported"
            | Value.Arr _ -> failwith "BV: array not supported"
            | Value.TupleCons _ -> failwith "BV: tuple not supported"
            | Value.DTCons _ -> failwith "BV: datatype not supported"
            | Value.Seq _ -> failwith "BV: sequence not supported"
          in
          Map.Poly.add_exn model ~key:tvar ~data)

  let model_value model t = Evaluator.simplify_term @@ Term.subst model t

  (* comparison operand width: the psym's size, else the other side's sort *)
  let cmp_size ~size other =
    match size with
    | Some _ -> size
    | None -> ( match Term.sort_of other with T_bv.SBV s -> s | _ -> None)

  (* normalization *)

  (* subtraction: a-b -> a+(-b) *)
  let rec desub = function
    | Term.FunApp (T_bv.BVSub size, [ t1; t2 ], _) ->
        T_bv.mk_bvadd ~size (desub t1) (T_bv.mk_bvneg ~size (desub t2))
    | Term.FunApp (fsym, args, info) ->
        Term.mk_fsym_app fsym (List.map args ~f:desub) ~info
    | t -> t

  (* derived operators expanded into primitive ones, on every occurrence
     whether or not the target variable is below it, so that no rule ever
     sees one: nand(a,b) -> ~(a&b), nor(a,b) -> ~(a|b), xnor(a,b) -> ~(a^b).
     The rewriting is bit-for-bit the SMT-LIB definition, introduces no
     derived operator and duplicates no subterm, so one bottom-up pass reaches
     the fixpoint. It runs first among the normalizations: an expansion can
     expose a form a rule handles (a mask form, say), and the termination of
     the normalization counts such forms only once no derived operator is
     left *)
  let rec dederived = function
    | Term.FunApp (fsym, args, info) -> (
        let args = List.map args ~f:dederived in
        match (fsym, args) with
        | T_bv.BVNand size, [ a; b ] ->
            T_bv.mk_bvnot ~size (T_bv.mk_bvand ~size a b)
        | T_bv.BVNor size, [ a; b ] ->
            T_bv.mk_bvnot ~size (T_bv.mk_bvor ~size a b)
        | T_bv.BVXnor size, [ a; b ] ->
            T_bv.mk_bvnot ~size (T_bv.mk_bvxor ~size a b)
        | _ -> Term.mk_fsym_app fsym args ~info)
    | t -> t

  (* bitwise negation, arithmetic layer only: ~u -> -(u+1) *)
  let denot ~size (c, r) =
    ( Z.neg c,
      T_bv.mk_bvneg ~size (T_bv.mk_bvadd ~size r (T_bv.mk_bvnum ~size Z.one)) )

  (* constant left shift, arithmetic form: u<<c -> 2^c*u, c<w *)
  let deshl ~size c (coef, r) =
    let pow2c = Z.pow (Z.of_int 2) (Z.to_int c) in
    (Z.(coef * pow2c), T_bv.mk_bvmul ~size (T_bv.mk_bvnum ~size pow2c) r)

  (* [affine_of tvar t] = (a, r) with t = a*x + r (r x-free), or None.
     Together with [transpose] this is how the procedure moves terms to one
     side of an equality: a reading taken when a rule is tried, never a
     rewriting of the atom. The rule that uses it removes the atom, so the
     reading never meets its own output, and an atom already of the form
     a*x + r = 0 is not rewritten into a*x + (r - 0) = 0 *)
  let rec affine_of tvar t =
    match desub t with
    | Term.Var (v, T_bv.SBV size, _) when Ident.tvar_equal v tvar ->
        Some (Z.one, T_bv.mk_bvnum ~size Z.zero)
    | Term.FunApp (T_bv.BVNeg size, [ t1 ], _) -> (
        match affine_of tvar t1 with
        | Some (c, r) -> Some (Z.neg c, T_bv.mk_bvneg ~size r)
        | None -> None)
    | Term.FunApp (T_bv.BVNot size, [ t1 ], _) -> (
        match affine_of tvar t1 with
        | Some cr -> Some (denot ~size cr)
        | None -> None)
    | Term.FunApp
        (T_bv.BVSHL size, [ t1; Term.FunApp (T_bv.BVNum (_, c), [], _) ], _)
      when Z.Compare.(Z.zero <= c && c < Z.of_int (T_bv.bits_of size)) -> (
        match affine_of tvar t1 with
        | Some cr -> Some (deshl ~size c cr)
        | None -> None)
    | Term.FunApp (T_bv.BVAdd size, [ t1; t2 ], _) -> (
        match (affine_of tvar t1, affine_of tvar t2) with
        | Some (c1, r1), Some (c2, r2) ->
            Some (Z.(c1 + c2), T_bv.mk_bvadd ~size r1 r2)
        | _ -> None)
    | Term.FunApp
        (T_bv.BVMul size, [ Term.FunApp (T_bv.BVNum (_, n), [], _); t1 ], _)
    | Term.FunApp
        (T_bv.BVMul size, [ t1; Term.FunApp (T_bv.BVNum (_, n), [], _) ], _)
      -> (
        match affine_of tvar t1 with
        | Some (c, r) ->
            Some (Z.(n * c), T_bv.mk_bvmul ~size (T_bv.mk_bvnum ~size n) r)
        | None -> None)
    | t when not (Set.mem (Term.fvs_of t) tvar) -> Some (Z.zero, t)
    | _ -> None

  (* transposition, equality only *)
  let transpose ~size (c1, r1) (c2, r2) =
    let w = T_bv.bits_of size in
    let coeff = Z.erem Z.(c1 - c2) (Z.pow (Z.of_int 2) w) in
    if Z.Compare.(coeff = Z.zero) then None
    else Some (coeff, Evaluator.simplify_term @@ T_bv.mk_bvsub ~size r1 r2)

  (* mask form: f(x) -> (x&m)|c, m = f[x:=1...1], c = f[x:=0...0].
     Like [affine_of], a reading taken when a rule is tried: [mask_of] never
     writes (x&m)|c back into an atom, so a side already in mask form is not
     expanded again into (x & ((1&m)|c)) | ((0&m)|c), which would grow without
     end when m or c is not a numeral. The mask-form rules remove the atom
     they read: [eq-mask] substitutes x away, [neq-mask] and [cmp-mask]
     replace the atom by bit or slice atoms, or (when the two sides agree in
     the model) by the equality that [eq-mask] then removes *)
  let rec is_monotone_in tvar t =
    if not (Set.mem (Term.fvs_of t) tvar) then true
    else
      match t with
      | Term.Var (v, _, _) -> Ident.tvar_equal v tvar
      | Term.FunApp ((T_bv.BVAnd _ | T_bv.BVOr _), [ a; b ], _) ->
          is_monotone_in tvar a && is_monotone_in tvar b
      | _ -> false

  let mask_of tvar t =
    if (not (Set.mem (Term.fvs_of t) tvar)) || not (is_monotone_in tvar t) then
      None
    else
      match Term.sort_of t with
      | T_bv.SBV size ->
          let inst v =
            Evaluator.simplify_term @@ Term.subst (Map.Poly.singleton tvar v) t
          in
          Some
            ( size,
              inst (T_bv.bvminus_one ~size ()),
              inst (T_bv.mk_bvnum ~size Z.zero) )
      | _ -> None

  (* whether [t] has a [sign_extend] whose operand mentions [tvar]. Only such
     an extension is a rewriting site of the [sign_extend] rows for [tvar]; an
     extension of a term free of [tvar] is never rewritten and must not hold
     back the signed-comparison row (it would leave a [tvar]-free [sext_k(y)]
     side blocking [cmp-interval] and fall back to the model point) *)
  let rec has_sext_of tvar = function
    | Term.FunApp (T_bv.BVSEXT _, [ t ], _) when Set.mem (Term.fvs_of t) tvar ->
        true
    | Term.FunApp (_, args, _) -> List.exists args ~f:(has_sext_of tvar)
    | _ -> false

  (* signed comparison: a <s b -> (a + 2^(w-1)) <u (b + 2^(w-1)), applied only
     after the [sign_extend] rows for [tvar] are done, i.e. when no side has a
     [sign_extend] of a term mentioning [tvar] *)
  let unsign_cmp tvar = function
    | Atom.App (Predicate.Psym psym, [ t1; t2 ], info)
      when not (has_sext_of tvar t1 || has_sext_of tvar t2) -> (
        let width size =
          Option.first_some (cmp_size ~size t1) (cmp_size ~size t2)
        in
        let shifted psym' size =
          let shift t =
            T_bv.mk_bvadd ~size t
              (T_bv.mk_bvnum ~size (Z.pow (Z.of_int 2) (T_bv.bits_of size - 1)))
          in
          Some (Atom.mk_app ~info (Predicate.Psym psym') [ shift t1; shift t2 ])
        in
        match psym with
        | T_bv.BVLeq (size, Some true) ->
            let w = width size in
            shifted (T_bv.BVLeq (w, Some false)) w
        | T_bv.BVGeq (size, Some true) ->
            let w = width size in
            shifted (T_bv.BVGeq (w, Some false)) w
        | T_bv.BVLt (size, Some true) ->
            let w = width size in
            shifted (T_bv.BVLt (w, Some false)) w
        | T_bv.BVGt (size, Some true) ->
            let w = width size in
            shifted (T_bv.BVGt (w, Some false)) w
        | _ -> None)
    | _ -> None

  (* trivial extract: u[w-1:0] -> u, w = |u| *)
  let mk_extract h l t =
    match Term.sort_of t with
    | T_bv.SBV (Some w) when l = 0 && h = w - 1 -> t
    | _ -> T_bv.mk_bvextract ~size:(Some (h - l + 1)) h l t

  (* [extract] normalization: concat slicing *)
  let rec fold_extract = function
    | Term.FunApp (T_bv.BVEXTRACT (_, h, l), [ t1 ], _) -> (
        match fold_extract t1 with
        | Term.FunApp (T_bv.BVCONCAT (_, size2), [ u1; u2 ], _) ->
            let w2 = T_bv.bits_of size2 in
            if h < w2 then fold_extract (mk_extract h l u2)
            else if l >= w2 then fold_extract (mk_extract (h - w2) (l - w2) u1)
            else
              T_bv.mk_bvconcat
                ~size1:(Some (h - w2 + 1))
                ~size2:(Some (w2 - l))
                (fold_extract (mk_extract (h - w2) 0 u1))
                (fold_extract (mk_extract (w2 - 1) l u2))
        | t1' -> mk_extract h l t1')
    | Term.FunApp (fsym, args, info) ->
        Term.mk_fsym_app fsym (List.map args ~f:fold_extract) ~info
    | t -> t

  (* the width of [tvar] at its first occurrence in [t] *)
  let rec tvar_width tvar = function
    | Term.Var (v, T_bv.SBV (Some w), _) when Ident.tvar_equal v tvar -> Some w
    | Term.FunApp (_, args, _) -> List.find_map args ~f:(tvar_width tvar)
    | _ -> None

  (* unit and absorbing elements, and constants in an add chain.
     With [tvar] = Some x the folding is restricted below a maximal arithmetic
     x-term T (head +, -, unary -, * ; containing x; of the width of x) whose
     parent is a non-arithmetic operator (a T at the top of an atom's side does
     not count): anywhere in T, an absorbing element is not folded over an
     operand containing x (u & 0, u | 1..1, u * 0), and the bitwise units and
     the double complement (u & 1..1, u | 0, u xor 0, ~~u) are not folded when
     u is x or an affine term in x. Without this restriction the termination
     measure of the projection does not decrease: in
     (((x[3:2] ++ y) & 0011) + x) & m = d, |x| = 4, distributing the mask over
     the concat and folding x[3:2] & 00 to 00 leaves ((00 ++ y) + x) & m = d,
     whose sum below the mask has become affine in x. The price is coverage:
     that atom keeps x[3:2] & 00 and x is projected by the model fallback.
     Numeral-only terms, the add-chain constants, u * 1, -(-u) and every
     x-free redex are folded everywhere *)
  let fold_bv ?tvar t =
    let width = Option.bind tvar ~f:(fun x -> tvar_width x t) in
    let has_x u =
      match tvar with Some x -> Set.mem (Term.fvs_of u) x | None -> false
    in
    let affine_x u =
      has_x u
      &&
      match tvar with
      | Some x -> Option.is_some (affine_of x u)
      | None -> false
    in
    let is_arith = function
      | T_bv.(BVAdd _ | BVSub _ | BVNeg _ | BVMul _) -> true
      | _ -> false
    in
    let rec num = function
      | Term.FunApp (T_bv.BVNum (_, n), [], _) -> Some n
      | Term.FunApp (T_bv.BVNeg _, [ u ], _) -> Option.map (num u) ~f:Z.neg
      | _ -> None
    in
    let is_num n u =
      match num u with Some m -> Z.Compare.(m = n) | None -> false
    in
    let ones size = Z.sub (Z.pow (Z.of_int 2) (T_bv.bits_of size)) Z.one in
    (* [under_op]: the parent is a non-arithmetic operator; [inside]: below T *)
    let rec go ~under_op ~inside t =
      match t with
      | Term.FunApp (fsym, args, info) -> (
          let inside =
            inside
            || under_op && is_arith fsym && has_x t
               &&
               match (width, Term.sort_of t) with
               | Some w, T_bv.SBV (Some w') -> w = w'
               | _ -> false
          in
          let args =
            List.map args
              ~f:(go ~under_op:(not (is_arith fsym)) ~inside)
          in
          let absorb u = not (inside && has_x u) in
          let unit u = not (inside && affine_x u) in
          let dflt () = Term.mk_fsym_app fsym args ~info in
          match (fsym, args) with
          | T_bv.BVAnd size, [ a; b ] ->
              if (is_num Z.zero a && absorb b) || (is_num Z.zero b && absorb a)
              then T_bv.mk_bvnum ~size Z.zero
              else if is_num (ones size) a && unit b then b
              else if is_num (ones size) b && unit a then a
              else dflt ()
          | T_bv.BVOr size, [ a; b ] ->
              if
                (is_num (ones size) a && absorb b)
                || (is_num (ones size) b && absorb a)
              then T_bv.mk_bvnum ~size (ones size)
              else if is_num Z.zero a && unit b then b
              else if is_num Z.zero b && unit a then a
              else dflt ()
          | T_bv.BVXor _, [ a; b ] ->
              if is_num Z.zero a && unit b then b
              else if is_num Z.zero b && unit a then a
              else dflt ()
          | T_bv.BVMul size, [ a; b ] ->
              if (is_num Z.zero a && absorb b) || (is_num Z.zero b && absorb a)
              then T_bv.mk_bvnum ~size Z.zero
              else if is_num Z.one a then b
              else if is_num Z.one b then a
              else dflt ()
          | T_bv.BVNeg _, [ Term.FunApp (T_bv.BVNeg _, [ u ], _) ] -> u
          | T_bv.BVNot _, [ Term.FunApp (T_bv.BVNot _, [ u ], _) ] when unit u
            ->
              u
        | T_bv.BVAdd size, [ _; _ ] -> (
            let rec summands = function
              | Term.FunApp (T_bv.BVAdd _, [ a; b ], _) ->
                  summands a @ summands b
              | u -> [ u ]
            in
            let consts, rest =
              List.partition_tf
                (summands (dflt ()))
                ~f:(fun u -> Option.is_some (num u))
            in
            let total =
              List.fold consts ~init:Z.zero ~f:(fun acc u ->
                  Z.add acc (Option.value_exn (num u)))
            in
            let c = Z.erem total (Z.pow (Z.of_int 2) (T_bv.bits_of size)) in
            let base =
              List.reduce rest ~f:(fun acc u -> T_bv.mk_bvadd ~size acc u)
            in
            match base with
            | None -> T_bv.mk_bvnum ~size c
            | Some b ->
                if Z.Compare.(c = Z.zero) then b
                else T_bv.mk_bvadd ~size b (T_bv.mk_bvnum ~size c))
        | _ -> dflt ())
      | t -> t
    in
    go ~under_op:false ~inside:false t

  (* unsigned division and remainder by 0 or by a power of two *)
  let rec fold_divrem t =
    match t with
    | Term.FunApp (fsym, args, info) -> (
        let args = List.map args ~f:fold_divrem in
        let dflt () = Term.mk_fsym_app fsym args ~info in
        match (fsym, args) with
        | ( (T_bv.BVDiv (size, signed) | T_bv.BVRem (size, signed)),
            [ u; Term.FunApp (T_bv.BVNum (_, n), [], _) ] )
          when not (T_bv.is_signed signed) -> (
            let w = T_bv.bits_of size in
            let is_div = match fsym with T_bv.BVDiv _ -> true | _ -> false in
            let n = Z.erem n (Z.pow (Z.of_int 2) w) in
            if Z.Compare.(n = Z.zero) then
              if is_div then
                T_bv.mk_bvnum ~size (Z.sub (Z.pow (Z.of_int 2) w) Z.one)
              else u
            else if Z.popcount n <> 1 then dflt ()
            else
              let c = Z.trailing_zeros n in
              if c = 0 then if is_div then u else T_bv.mk_bvnum ~size Z.zero
              else if is_div then
                T_bv.mk_bvconcat
                  ~size1:(Some c)
                  ~size2:(Some (w - c))
                  (T_bv.mk_bvnum ~size:(Some c) Z.zero)
                  (mk_extract (w - 1) c u)
              else
                T_bv.mk_bvconcat
                  ~size1:(Some (w - c))
                  ~size2:(Some c)
                  (T_bv.mk_bvnum ~size:(Some (w - c)) Z.zero)
                  (mk_extract (c - 1) 0 u))
        | _ -> dflt ())
    | t -> t

  (* the sign bit of [u] repeated to the full width *)
  let sign_fill ~size u =
    let w = T_bv.bits_of size in
    let bit = mk_extract (w - 1) (w - 1) u in
    let rec go k acc =
      if k >= w then acc
      else go (k + 1) (T_bv.mk_bvconcat ~size1:(Some 1) ~size2:(Some k) bit acc)
    in
    go 1 bit

  (* a shift by a non-numeral inside [t] *)
  let rec has_sym_shift = function
    | Term.FunApp
        ( (T_bv.BVSHL _ | T_bv.BVLSHR _ | T_bv.BVASHR _),
          [ _; Term.FunApp (T_bv.BVNum _, [], _) ],
          _ ) as t -> (
        match t with
        | Term.FunApp (_, args, _) -> List.exists args ~f:has_sym_shift
        | _ -> false)
    | Term.FunApp ((T_bv.BVSHL _ | T_bv.BVLSHR _ | T_bv.BVASHR _), _, _) -> true
    | Term.FunApp (_, args, _) -> List.exists args ~f:has_sym_shift
    | _ -> false

  (* u >>u c -> 0^c o u[w-1:c] and u >>s c -> sext_c(u[w-1:c]) (u when c = 0); at the width or more:
     << and >>u give 0, >>s the sign bit, except when u has a shift by a
     non-numeral inside: the w copies of the sign bit would multiply that
     shift, which has no rewriting (its atom is projected by the fallback
     either way), and termination counts shifts before everything else in an
     atom. This normalization does not know the eliminated variable, so it
     declines for such a shift over any variable. A shift by a numeral inside
     u is copied as before: << by a numeral is kept in the arithmetic
     reading and rewritten only on the slice layer *)
  let rec fold_shift t =
    match t with
    | Term.FunApp (fsym, args, info) -> (
        let args = List.map args ~f:fold_shift in
        let dflt () = Term.mk_fsym_app fsym args ~info in
        match (fsym, args) with
        | ( (T_bv.BVSHL size | T_bv.BVLSHR size | T_bv.BVASHR size),
            [ u; Term.FunApp (T_bv.BVNum (_, n), [], _) ] ) -> (
            let size = cmp_size ~size u in
            let w = T_bv.bits_of size in
            let c = Z.erem n (Z.pow (Z.of_int 2) w) in
            if Z.Compare.(c >= Z.of_int w) then
              match fsym with
              | T_bv.BVASHR _ ->
                  if has_sym_shift u then dflt () else sign_fill ~size u
              | _ -> T_bv.mk_bvnum ~size Z.zero
            else
              let c = Z.to_int c in
              match fsym with
              | T_bv.BVLSHR _ ->
                  if c = 0 then u
                  else
                    T_bv.mk_bvconcat
                      ~size1:(Some c)
                      ~size2:(Some (w - c))
                      (T_bv.mk_bvnum ~size:(Some c) Z.zero)
                      (mk_extract (w - 1) c u)
              | T_bv.BVASHR _ ->
                  (* a sign extension, not the concat of c sign bits: [extend]
                     then projects it with one range guard instead of c atoms *)
                  if c = 0 then u
                  else
                    T_bv.mk_bvsext
                      ~size:(Some (w - c))
                      c
                      (mk_extract (w - 1) c u)
              | _ -> dflt ())
        | _ -> dflt ())
    | t -> t

  (* arithmetic through a low slice: (a + b)[h:0] -> a[h:0] + b[h:0], and the product and the negation *)
  let rec fold_low_slice t =
    match t with
    | Term.FunApp (fsym, args, info) -> (
        let args = List.map args ~f:fold_low_slice in
        let dflt () = Term.mk_fsym_app fsym args ~info in
        match (fsym, args) with
        | T_bv.BVEXTRACT (_, h, 0), [ inner ] -> (
            let sz = Some (h + 1) in
            let slice u = mk_extract h 0 u in
            match inner with
            | Term.FunApp (T_bv.BVAdd _, [ a; b ], _) ->
                fold_low_slice (T_bv.mk_bvadd ~size:sz (slice a) (slice b))
            | Term.FunApp (T_bv.BVMul _, [ a; b ], _) ->
                fold_low_slice (T_bv.mk_bvmul ~size:sz (slice a) (slice b))
            | Term.FunApp (T_bv.BVNeg _, [ a ], _) ->
                fold_low_slice (T_bv.mk_bvneg ~size:sz (slice a))
            | _ -> dflt ())
        | _ -> dflt ())
    | t -> t

  (* bitwise through a slice: (u op v)[h:l] -> u[h:l] op v[h:l], and through a concat *)
  let rec fold_distrib t =
    match t with
    | Term.FunApp (fsym, args, info) -> (
        let args = List.map args ~f:fold_distrib in
        let dflt () = Term.mk_fsym_app fsym args ~info in
        let binary op ~size a b =
          match op with
          | T_bv.BVAnd _ -> Some (T_bv.mk_bvand ~size a b)
          | T_bv.BVOr _ -> Some (T_bv.mk_bvor ~size a b)
          | T_bv.BVXor _ -> Some (T_bv.mk_bvxor ~size a b)
          | _ -> None
        in
        match (fsym, args) with
        | T_bv.BVEXTRACT (_, h, l), [ inner ] -> (
            let sz = Some (h - l + 1) in
            match inner with
            | Term.FunApp
                ((T_bv.BVAnd _ | T_bv.BVOr _ | T_bv.BVXor _) as op, [ a; b ], _) -> (
                match binary op ~size:sz (mk_extract h l a) (mk_extract h l b) with
                | Some t' -> fold_distrib t'
                | None -> dflt ())
            | Term.FunApp (T_bv.BVNot _, [ a ], _) ->
                fold_distrib (T_bv.mk_bvnot ~size:sz (mk_extract h l a))
            | _ -> dflt ())
        | ( ((T_bv.BVAnd _ | T_bv.BVOr _ | T_bv.BVXor _) as op),
            [
              Term.FunApp (T_bv.BVCONCAT (s1, s2), [ u1; u2 ], _);
              Term.FunApp (T_bv.BVCONCAT (_, t2), [ v1; v2 ], _);
            ] )
          when T_bv.bits_of s2 = T_bv.bits_of t2 -> (
            match
              ( binary op ~size:s1 u1 v1,
                binary op ~size:s2 u2 v2 )
            with
            | Some hi, Some lo ->
                T_bv.mk_bvconcat ~size1:s1 ~size2:s2 (fold_distrib hi)
                  (fold_distrib lo)
            | _ -> dflt ())
        | T_bv.BVNot _, [ Term.FunApp (T_bv.BVCONCAT (s1, s2), [ u1; u2 ], _) ] ->
            T_bv.mk_bvconcat ~size1:s1 ~size2:s2
              (fold_distrib (T_bv.mk_bvnot ~size:s1 u1))
              (fold_distrib (T_bv.mk_bvnot ~size:s2 u2))
        | _ -> dflt ())
    | t -> t

  (* u << c -> u[w-1-c:0] o 0^c (u when c = 0), for the slice layer only *)
  let rec fold_shl_slice t =
    match t with
    | Term.FunApp (fsym, args, info) -> (
        let args = List.map args ~f:fold_shl_slice in
        let dflt () = Term.mk_fsym_app fsym args ~info in
        match (fsym, args) with
        | T_bv.BVSHL size, [ u; Term.FunApp (T_bv.BVNum (_, n), [], _) ] ->
            let size = cmp_size ~size u in
            let w = T_bv.bits_of size in
            let c = Z.erem n (Z.pow (Z.of_int 2) w) in
            if Z.Compare.(c >= Z.of_int w) then dflt ()
            else
              let c = Z.to_int c in
              if c = 0 then u
              else
                T_bv.mk_bvconcat
                  ~size1:(Some (w - c))
                  ~size2:(Some c)
                  (mk_extract (w - 1 - c) 0 u)
                  (T_bv.mk_bvnum ~size:(Some c) Z.zero)
        | _ -> dflt ())
    | t -> t

  (* bitwise through a one-sided concatenation, for a target-free other side *)
  let rec fold_distrib1 tvar t =
    match t with
    | Term.FunApp (fsym, args, info) -> (
        let args = List.map args ~f:(fold_distrib1 tvar) in
        let dflt () = Term.mk_fsym_app fsym args ~info in
        let binary op ~size a b =
          match op with
          | T_bv.BVAnd _ -> Some (T_bv.mk_bvand ~size a b)
          | T_bv.BVOr _ -> Some (T_bv.mk_bvor ~size a b)
          | T_bv.BVXor _ -> Some (T_bv.mk_bvxor ~size a b)
          | _ -> None
        in
        let split op s1 s2 u1 u2 v =
          let k = T_bv.bits_of s2 and hi = T_bv.bits_of s1 in
          if k < 1 || hi < 1 then None
          else
            let n = hi + k in
            match
              ( binary op ~size:s1 u1 (mk_extract (n - 1) k v),
                binary op ~size:s2 u2 (mk_extract (k - 1) 0 v) )
            with
            | Some h, Some l ->
                Some
                  (T_bv.mk_bvconcat ~size1:s1 ~size2:s2 (fold_distrib1 tvar h)
                     (fold_distrib1 tvar l))
            | _ -> None
        in
        match (fsym, args) with
        | ((T_bv.BVAnd _ | T_bv.BVOr _ | T_bv.BVXor _) as op), [ a; b ] -> (
            let one_sided u v =
              match u with
              | Term.FunApp (T_bv.BVCONCAT (s1, s2), [ u1; u2 ], _)
                when not (Set.mem (Term.fvs_of v) tvar) ->
                  split op s1 s2 u1 u2 v
              | _ -> None
            in
            match one_sided a b with
            | Some t' -> t'
            | None -> (
                match one_sided b a with Some t' -> t' | None -> dflt ()))
        | _ -> dflt ())
    | t -> t

  (* a trivial extension: ext_0 u -> u *)
  let rec fold_ext0 t =
    match t with
    | Term.FunApp (fsym, args, info) -> (
        let args = List.map args ~f:fold_ext0 in
        match (fsym, args) with
        | T_bv.(BVSEXT (_, 0) | BVZEXT (_, 0)), [ u ] -> u
        | _ -> Term.mk_fsym_app fsym args ~info)
    | t -> t

  (* unconditional normalizations, applied to every atom before the rules;
     [tvar] is the variable being eliminated, which restricts [fold_bv] *)
  let unconditional ?tvar () =
    [
      dederived;
      desub;
      fold_ext0;
      fold_extract;
      fold_bv ?tvar;
      fold_divrem;
      fold_shift;
      fold_distrib;
      fold_low_slice;
    ]

  let rec normalize_term ?tvar ?only t =
    let only =
      match only with Some only -> only | None -> unconditional ?tvar ()
    in
    let t' = List.fold only ~init:t ~f:(fun t f -> f t) in
    if Stdlib.(t' = t) then t else normalize_term ~only t'

  let normalize_atoms ?tvar ?only model atoms =
    Set.concat_map atoms ~f:(function
      | Atom.App (pred, args, info) ->
          let args =
            Common.PhaseTime.with_phase "folds" (fun () ->
                List.map args ~f:(normalize_term ?tvar ?only))
          in
          Common.PhaseTime.with_phase "nmbp" (fun () ->
              normalize_mbp_memo model (Atom.mk_app ~info pred args))
      | atom -> Set.Poly.singleton atom)

  (* Literals by physical identity: the literals of one projection are large trees that
     often agree far down, so a structural lookup can walk most of a tree to tell two of
     them apart, while the literals passed back to a later step are the very values this
     module returned. *)
  module PhysAtoms = Stdlib.Hashtbl.Make (struct
    type t = Atom.t

    let equal = phys_equal
    let hash = Stdlib.Hashtbl.hash
  end)

  let known_create () : unit PhysAtoms.t = PhysAtoms.create 1024

  (* [normalize_atoms], except that a literal in [known] is kept as it is.  [known] holds,
     by physical identity, the literals this module returned from an earlier step of the
     same projection exactly as its own normalization produced them (the final
     normalization of a step, below), so keeping them skips a second normalization of a
     literal already in normal form.  That this is the identity rests on the
     normalization being idempotent, which is observed for most inputs but fails for a
     few literals (a count of the skipped literals a normalization would change found
     some); a
     skipped literal is still equivalent to its normalization, so only the form the
     rules see can differ.  The final normalization runs with no variable and the
     later one with [tvar], under which [fold_bv] folds a subset of the redexes, so a
     literal normal without a variable is taken to be normal with one; that rests on
     the subset, not on a proof.  A literal of the caller's own, never normalized here,
     is not in [known]. *)
  let normalize_atoms_known ?tvar ~known model atoms =
    match known with
    | None -> normalize_atoms ?tvar model atoms
    | Some known ->
        let kept, rest = Set.partition_tf atoms ~f:(PhysAtoms.mem known) in
        Set.union kept (normalize_atoms ?tvar model rest)

  (* rules *)

  (* [eq-odd]/[eq-even] shared *)
  let affine_eq_atom tvar = function
    | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _) as atom -> (
        match (affine_of tvar t1, affine_of tvar t2) with
        | Some (c1, r1), Some (c2, r2) -> (
            match Term.sort_of t1 with
            | T_bv.SBV size -> (
                match transpose ~size (c1, r1) (c2, r2) with
                | Some (coeff, rest) -> Some (size, coeff, rest, atom)
                | None -> None)
            | _ -> None)
        | _ -> None)
    | _ -> None

  (* [eq-odd] detection *)
  let eq_odd_atom tvar atom =
    match affine_eq_atom tvar atom with
    | Some (size, coeff, rest, atom) when Z.testbit coeff 0 ->
        Some (size, coeff, rest, atom)
    | _ -> None

  let eq_odd ~print model tvar ~size ~coeff ~rest atom atoms =
    print @@ lazy (sprintf "[mbp bv] eq-odd x=%s" (Ident.name_of_tvar tvar));
    let w = T_bv.bits_of size in
    let a_inv = Z.invert coeff (Z.pow (Z.of_int 2) w) in
    let tau =
      Evaluator.simplify_term
      @@ T_bv.mk_bvmul ~size
           (T_bv.mk_bvnum ~size a_inv)
           (T_bv.mk_bvneg ~size rest)
    in
    let sub = Map.Poly.singleton tvar tau in
    Set.remove atoms atom
    |> Set.concat_map ~f:(Atom.subst sub >> normalize_mbp model)

  (* [eq-even] detection *)
  let eq_even_atom tvar atoms =
    Set.to_list atoms
    |> List.filter_map ~f:(fun atom ->
        match affine_eq_atom tvar atom with
        | Some (size, coeff, rest, atom) when not (Z.testbit coeff 0) ->
            Some (Z.trailing_zeros coeff, size, coeff, rest, atom)
        | _ -> None)
    |> List.min_elt ~compare:(fun (e1, _, _, _, _) (e2, _, _, _, _) ->
        Int.compare e1 e2)

  let eq_even ~print model tvar ~size ~coeff ~rest atom atoms =
    let w = T_bv.bits_of size in
    let e = Z.trailing_zeros coeff in
    print
    @@ lazy (sprintf "[mbp bv] eq-even x=%s e=%d" (Ident.name_of_tvar tvar) e);
    let a' = Z.shift_right coeff e in
    let a_inv = Z.invert a' (Z.pow (Z.of_int 2) (w - e)) in
    let neg_r = T_bv.mk_bvneg ~size rest in
    let neg_r_high = T_bv.mk_bvextract ~size:(Some (w - e)) (w - 1) e neg_r in
    let sigma =
      Evaluator.simplify_term
      @@ T_bv.mk_bvmul
           ~size:(Some (w - e))
           (T_bv.mk_bvnum ~size:(Some (w - e)) a_inv)
           neg_r_high
    in
    let y_h = Ident.mk_fresh_tvar () in
    let y_h_sort = T_bv.SBV (Some e) in
    let y_h_var = Term.mk_var y_h y_h_sort in
    let xvar = Term.mk_var tvar (T_bv.SBV size) in
    let model' =
      Map.Poly.set model ~key:y_h
        ~data:
          (model_value model
          @@ T_bv.mk_bvextract ~size:(Some e) (w - 1) (w - e) xvar)
    in
    let repl =
      T_bv.mk_bvconcat ~size1:(Some e) ~size2:(Some (w - e)) y_h_var sigma
    in
    let sub = Map.Poly.singleton tvar repl in
    let guard =
      T_bool.mk_eq
        (T_bv.mk_bvextract ~size:(Some e) (e - 1) 0 rest)
        (T_bv.mk_bvnum ~size:(Some e) Z.zero)
    in
    let atoms' =
      Set.remove atoms atom
      |> Set.concat_map ~f:(Atom.subst sub >> normalize_mbp model)
      |> Fn.flip Set.union (normalize_mbp model guard)
    in
    (model', y_h, atoms')

  (* [eq-mask]/[neq-mask]/[cmp-mask] detection *)
  let eq_mask_atom tvar = function
    | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _) as atom -> (
        let is_xfree u = not (Set.mem (Term.fvs_of u) tvar) in
        let try_side u other =
          match mask_of tvar u with
          | Some (size, m, c) when is_xfree other ->
              Some (size, m, c, other, atom)
          | _ -> None
        in
        match try_side t1 t2 with Some r -> Some r | None -> try_side t2 t1)
    | _ -> None

  let eq_mask ~print model tvar ~size m c t atom atoms =
    print @@ lazy (sprintf "[mbp bv] eq-mask x=%s" (Ident.name_of_tvar tvar));
    let not_c = T_bv.mk_bvnot ~size c in
    let f = T_bv.mk_bvand ~size m not_c in
    let not_f = T_bv.mk_bvnot ~size f in
    let z = Ident.mk_fresh_tvar () in
    let z_var = Term.mk_var z (T_bv.SBV size) in
    let xvar = Term.mk_var tvar (T_bv.SBV size) in
    let model' = Map.Poly.set model ~key:z ~data:(model_value model xvar) in
    let repl =
      T_bv.mk_bvor ~size (T_bv.mk_bvand ~size t f)
        (T_bv.mk_bvand ~size z_var not_f)
    in
    let sub = Map.Poly.singleton tvar repl in
    let guard1 = T_bool.mk_eq (T_bv.mk_bvand ~size c t) c in
    let guard2 =
      T_bool.mk_eq (T_bv.mk_bvand ~size t (T_bv.mk_bvor ~size m c)) t
    in
    let atoms' =
      Set.remove atoms atom
      |> Set.concat_map ~f:(Atom.subst sub >> normalize_mbp model)
      |> Fn.flip Set.union (normalize_mbp model guard1)
      |> Fn.flip Set.union (normalize_mbp model guard2)
    in
    (model', z, atoms')

  (* [eq-mask] over all k mask equalities (x & m_i) | c_i = t_i of x in one
     step. With F_i = m_i & ~c_i (the bits E_i fixes), T = \/_i (t_i & F_i),
     U = \/_i F_i and N = \/_i (F_i & ~t_i), the output is the two guards of
     every E_i, the agreement atom T & N = 0 (no bit fixed to 1 by one literal
     and to 0 by another), and the other atoms with x := T | (z & ~U), z fresh
     with M'(z) = M(x). Exact: under the guards and the agreement atom the
     solutions of /\_i E_i are exactly the values T | (u & ~U), bit by bit.
     Applying the one-literal rule k times instead projects the same set, but
     each step reads the previous step's fixed-bit term twice (in the new mask
     and the new constant), so the substituted term at least doubles in tree
     size per step; here it is linear in k. Off unless the environment
     variable COAR_MBP_BV_EQ_MASK_JOINT is 1, true or yes *)
  let eq_mask_joint_enabled =
    lazy
      (match Sys.getenv "COAR_MBP_BV_EQ_MASK_JOINT" with
      | Some ("1" | "true" | "yes") -> true
      | _ -> false)

  (* requires: [lits] nonempty, every element a mask equality of [tvar] at
     width [size] as returned by [eq_mask_atom], pairwise distinct atoms *)
  let eq_mask_joint ~print model tvar ~size lits atoms =
    print
    @@ lazy
         (sprintf "[mbp bv] eq-mask-joint x=%s k=%d" (Ident.name_of_tvar tvar)
            (List.length lits));
    let fixed (_, m, c, _, _) = T_bv.mk_bvand ~size m (T_bv.mk_bvnot ~size c) in
    let disj = function
      | [] -> T_bv.mk_bvnum ~size Z.zero
      | u :: us -> List.fold us ~init:u ~f:(T_bv.mk_bvor ~size)
    in
    let fs = List.map lits ~f:(fun lit -> (lit, fixed lit)) in
    let tt =
      disj
      @@ List.map fs ~f:(fun ((_, _, _, t, _), f) -> T_bv.mk_bvand ~size t f)
    in
    let uu = disj @@ List.map fs ~f:snd in
    let nn =
      disj
      @@ List.map fs ~f:(fun ((_, _, _, t, _), f) ->
          T_bv.mk_bvand ~size f (T_bv.mk_bvnot ~size t))
    in
    let z = Ident.mk_fresh_tvar () in
    let z_var = Term.mk_var z (T_bv.SBV size) in
    let xvar = Term.mk_var tvar (T_bv.SBV size) in
    let model' = Map.Poly.set model ~key:z ~data:(model_value model xvar) in
    let repl =
      T_bv.mk_bvor ~size tt (T_bv.mk_bvand ~size z_var (T_bv.mk_bvnot ~size uu))
    in
    let sub = Map.Poly.singleton tvar repl in
    let guards =
      List.concat_map lits ~f:(fun (_, m, c, t, _) ->
          [
            T_bool.mk_eq (T_bv.mk_bvand ~size c t) c;
            T_bool.mk_eq (T_bv.mk_bvand ~size t (T_bv.mk_bvor ~size m c)) t;
          ])
    in
    let agree =
      T_bool.mk_eq (T_bv.mk_bvand ~size tt nn) (T_bv.mk_bvnum ~size Z.zero)
    in
    let atoms' =
      List.fold lits ~init:atoms ~f:(fun acc (_, _, _, _, atom) ->
          Set.remove acc atom)
      |> Set.concat_map ~f:(Atom.subst sub >> normalize_mbp model)
      |> fun acc ->
      List.fold (agree :: guards) ~init:acc ~f:(fun acc g ->
          Set.union acc (normalize_mbp model g))
    in
    (model', z, atoms')

  (* [neq-mask] detection: (x&m)|c != t, bare x excluded *)
  let neq_mask_atom tvar atoms = function
    | Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _) as atom -> (
        let is_xfree u = not (Set.mem (Term.fvs_of u) tvar) in
        let is_bare = function
          | Term.Var (v, _, _) -> Ident.tvar_equal v tvar
          | _ -> false
        in
        let try_side u other =
          match mask_of tvar u with
          | Some (size, m, c) when is_xfree other && not (is_bare u) ->
              Some (size, m, c, other)
          | _ -> None
        in
        match
          match try_side t1 t2 with Some r -> Some r | None -> try_side t2 t1
        with
        | Some (size, m, c, t)
          when Set.exists (Set.remove atoms atom) ~f:(fun a ->
                   Set.mem (Atom.fvs_of a) tvar) ->
            Some (size, m, c, t, atom)
        | _ -> None)
    | _ -> None

  let neq_mask ~print model tvar ~size m c t atom atoms =
    print @@ lazy (sprintf "[mbp bv] neq-mask x=%s" (Ident.name_of_tvar tvar));
    let g1 = T_bool.mk_eq (T_bv.mk_bvand ~size c t) c in
    let g2 = T_bool.mk_eq (T_bv.mk_bvand ~size t (T_bv.mk_bvor ~size m c)) t in
    let holds g =
      Evaluator.eval @@ Evaluator.simplify_atom @@ Atom.subst model g
    in
    let gamma =
      if not (holds g1) then [ T_bool.mk_neq (T_bv.mk_bvand ~size c t) c ]
      else if not (holds g2) then
        [ T_bool.mk_neq (T_bv.mk_bvand ~size t (T_bv.mk_bvor ~size m c)) t ]
      else
        let xvar = Term.mk_var tvar (T_bv.SBV size) in
        let lhs =
          model_value model (T_bv.mk_bvor ~size (T_bv.mk_bvand ~size xvar m) c)
        in
        let rhs = model_value model t in
        let _, lhs_n = T_bv.let_bv lhs in
        let _, rhs_n = T_bv.let_bv rhs in
        let b = Z.trailing_zeros (Z.logxor lhs_n rhs_n) in
        let bit1 u = T_bv.mk_bvextract ~size:(Some 1) b b u in
        [
          T_bool.mk_eq (bit1 m) (T_bv.mk_bvnum ~size:(Some 1) Z.one);
          T_bool.mk_eq (bit1 c) (T_bv.mk_bvnum ~size:(Some 1) Z.zero);
          T_bool.mk_neq (bit1 xvar) (bit1 t);
        ]
    in
    let gamma_atoms =
      List.concat_map gamma ~f:(fun g -> Set.to_list (normalize_mbp model g))
      |> Set.Poly.of_list
    in
    Set.union (Set.remove atoms atom) gamma_atoms

  (* [cmp-mask] detection: (x&m)|c ~ t, bare x excluded *)
  let cmp_mask_atom tvar atoms = function
    | Atom.App
        ( Predicate.Psym
            (T_bv.(
               ( BVLeq (size, Some _)
               | BVGeq (size, Some _)
               | BVLt (size, Some _)
               | BVGt (size, Some _) )) as psym),
          [ t1; t2 ],
          _ ) as atom
      when Set.exists (Set.remove atoms atom) ~f:(fun a ->
               Set.mem (Atom.fvs_of a) tvar) -> (
        let is_bare = function
          | Term.Var (v, _, _) -> Ident.tvar_equal v tvar
          | _ -> false
        in
        let try_side u other =
          if is_bare u || Set.mem (Term.fvs_of other) tvar then None
          else
            Option.map (mask_of tvar u) ~f:(fun (msize, m, c) ->
                (Option.first_some msize (cmp_size ~size other), m, c, other))
        in
        match try_side t1 t2 with
        | Some (size', m, c, other) -> Some (psym, size', m, c, other, atom)
        | None ->
            Option.map (try_side t2 t1) ~f:(fun (size', m, c, other) ->
                (Predicate.flip_psym psym, size', m, c, other, atom)))
    | _ -> None

  let cmp_mask ~print model tvar psym ~size m c t atom atoms =
    print @@ lazy (sprintf "[mbp bv] cmp-mask x=%s" (Ident.name_of_tvar tvar));
    let w = T_bv.bits_of size in
    let xvar = Term.mk_var tvar (T_bv.SBV size) in
    let mask_term = T_bv.mk_bvor ~size (T_bv.mk_bvand ~size xvar m) c in
    (* v_[h:l] = (x[h:l] & m[h:l]) | c[h:l] *)
    let v_slice h l =
      let sz = Some (h - l + 1) in
      T_bv.mk_bvor ~size:sz
        (T_bv.mk_bvand ~size:sz (mk_extract h l xvar) (mk_extract h l m))
        (mk_extract h l c)
    in
    let bit1 n = T_bv.mk_bvnum ~size:(Some 1) (Z.of_int n) in
    let _, lhs_n = T_bv.let_bv (model_value model mask_term) in
    let _, rhs_n = T_bv.let_bv (model_value model t) in
    let diff = Z.logxor lhs_n rhs_n in
    let gamma =
      if Z.Compare.(diff = Z.zero) then [ T_bool.mk_eq mask_term t ]
        (* gamma_1 *)
      else
        let b = Z.numbits diff - 1 in
        if b = 0 then
          (* gamma_2a/gamma_2b *)
          let beta = if Z.testbit lhs_n 0 then 1 else 0 in
          (if w = 1 then []
           else [ T_bool.mk_eq (v_slice (w - 1) 1) (mk_extract (w - 1) 1 t) ])
          @ [
              T_bool.mk_eq (v_slice 0 0) (bit1 beta);
              T_bool.mk_eq (mk_extract 0 0 t) (bit1 (1 - beta));
            ]
        else
          (* gamma_3, strict *)
          let sz = Some (w - b) in
          let vh = v_slice (w - 1) b and th = mk_extract (w - 1) b t in
          [
            (match psym with
            | T_bv.(BVLeq (_, signed) | BVLt (_, signed)) ->
                T_bv.mk_bvlt ~size:sz ~signed vh th
            | T_bv.(BVGeq (_, signed) | BVGt (_, signed)) ->
                T_bv.mk_bvgt ~size:sz ~signed vh th
            | _ -> failwith "[mbp bv] cmp-mask: unexpected predicate");
          ]
    in
    let gamma_atoms =
      List.concat_map gamma ~f:(fun g -> Set.to_list (normalize_mbp model g))
      |> Set.Poly.of_list
    in
    Set.union (Set.remove atoms atom) gamma_atoms

  (* [bitwise-both]: x on both sides of bitwise atoms. A side built from x,
     x-free terms and &, |, xor, not alone is, bit by bit, a function of the
     same bit of x (bitwise Shannon expansion: t = (t0 & ~x) | (t1 & x) with
     t0 := t[0...0/x], t1 := t[1...1/x]), so every bit of x is chosen
     independently of the others and the projection is exact. With
     D_b := f_b xor g_b, N := D_0 & D_1 and L := (~f_0 & g_0) | (~f_1 & g_1)
     (N_i: no choice of x_i makes bit i of f and g equal; L_i: some choice
     makes it f_i = 0, g_i = 1):
       exists x. f = g    iff  N = 0
       exists x. f != g   iff  D_0 | D_1 != 0
       exists x. f <=u g  iff  N & ~L <=u L
       exists x. f <u g   iff  N & ~L <u L
     (the highest bit of L is not below the highest bit of N; >=u, >u
     exchange f and g; the signed orders xor every instance with 2^(w-1)), and
       exists x. /\_j f^j = g^j  iff  (\/_j D^j_0) & (\/_j D^j_1) = 0.
     Exact only when these atoms are all the atoms mentioning x: one atom of
     any predicate, or equalities only (a conjunction of disequalities or
     orders couples the choice at the deciding bits). Some atom must have x on
     both sides; otherwise the mask rules apply. The output writes no value of
     the model. Off unless the environment variable COAR_MBP_BV_BITWISE_BOTH
     is 1, true or yes *)
  let bitwise_both_enabled =
    lazy
      (match Sys.getenv "COAR_MBP_BV_BITWISE_BOTH" with
      | Some ("1" | "true" | "yes") -> true
      | _ -> false)

  let rec is_bitwise_in tvar t =
    if not (Set.mem (Term.fvs_of t) tvar) then true
    else
      match t with
      | Term.Var (v, _, _) -> Ident.tvar_equal v tvar
      | Term.FunApp ((T_bv.BVAnd _ | T_bv.BVOr _ | T_bv.BVXor _), [ a; b ], _)
        ->
          is_bitwise_in tvar a && is_bitwise_in tvar b
      | Term.FunApp (T_bv.BVNot _, [ a ], _) -> is_bitwise_in tvar a
      | _ -> false

  (* the predicate, the width and the sides of an atom mentioning [tvar] whose
     sides are both bitwise in [tvar] *)
  let bitwise_atom tvar = function
    | Atom.App (Predicate.Psym psym, [ t1; t2 ], _)
      when is_bitwise_in tvar t1 && is_bitwise_in tvar t2 -> (
        let xside = if Set.mem (Term.fvs_of t1) tvar then t1 else t2 in
        match (psym, Term.sort_of xside) with
        | ( ( T_bool.Eq | T_bool.Neq
            | T_bv.(
                ( BVLeq (_, Some _)
                | BVGeq (_, Some _)
                | BVLt (_, Some _)
                | BVGt (_, Some _) )) ),
            T_bv.SBV size ) ->
            Some (psym, size, t1, t2)
        | _ -> None)
    | _ -> None

  let bitwise_both_atom tvar atoms =
    if not (Lazy.force bitwise_both_enabled) then None
    else
      let xatoms =
        Set.filter atoms ~f:(fun a -> Set.mem (Atom.fvs_of a) tvar)
      in
      let parts = List.map (Set.to_list xatoms) ~f:(bitwise_atom tvar) in
      if not (List.for_all parts ~f:Option.is_some) then None
      else
        let parts = List.filter_opt parts in
        let both (_, _, t1, t2) =
          Set.mem (Term.fvs_of t1) tvar && Set.mem (Term.fvs_of t2) tvar
        in
        let is_eq (psym, _, _, _) =
          match psym with T_bool.Eq -> true | _ -> false
        in
        if not (List.exists parts ~f:both) then None
        else
          match parts with
          | [ _ ] -> Some (xatoms, parts)
          | _ when List.for_all parts ~f:is_eq -> Some (xatoms, parts)
          | _ -> None

  let bitwise_both ~print model tvar xatoms parts atoms =
    print
    @@ lazy (sprintf "[mbp bv] bitwise-both x=%s" (Ident.name_of_tvar tvar));
    let inst ~size n t =
      Evaluator.simplify_term
      @@ Term.subst
           (Map.Poly.singleton tvar (T_bv.mk_bvnum ~size n))
           t
    in
    let instances ~size t =
      (inst ~size Z.zero t, inst ~size (Z.pred (Z.shift_left Z.one (T_bv.bits_of size))) t)
    in
    let gamma =
      match parts with
      | [ (psym, size, f, g) ] -> (
          let zero = T_bv.mk_bvnum ~size Z.zero in
          let xor = T_bv.mk_bvxor ~size and band = T_bv.mk_bvand ~size in
          let bor = T_bv.mk_bvor ~size and bnot = T_bv.mk_bvnot ~size in
          let f0, f1 = instances ~size f and g0, g1 = instances ~size g in
          match psym with
          | T_bool.Eq -> T_bool.mk_eq (band (xor f0 g0) (xor f1 g1)) zero
          | T_bool.Neq -> T_bool.mk_neq (bor (xor f0 g0) (xor f1 g1)) zero
          | T_bv.(
              ( BVLeq (_, Some signed)
              | BVGeq (_, Some signed)
              | BVLt (_, Some signed)
              | BVGt (_, Some signed) )) ->
              let flip u =
                if signed then
                  xor u
                    (T_bv.mk_bvnum ~size
                       (Z.shift_left Z.one (T_bv.bits_of size - 1)))
                else u
              in
              (* f <= g or f < g after exchanging the sides of >= and > *)
              let (f0, f1, g0, g1), strict =
                match psym with
                | T_bv.BVLeq _ -> ((f0, f1, g0, g1), false)
                | T_bv.BVLt _ -> ((f0, f1, g0, g1), true)
                | T_bv.BVGeq _ -> ((g0, g1, f0, f1), false)
                | _ -> ((g0, g1, f0, f1), true)
              in
              let f0 = flip f0 and f1 = flip f1 in
              let g0 = flip g0 and g1 = flip g1 in
              let n = band (xor f0 g0) (xor f1 g1) in
              let l = bor (band (bnot f0) g0) (band (bnot f1) g1) in
              let lhs = band n (bnot l) in
              if strict then
                T_bv.mk_bvlt ~size ~signed:(Some false) lhs l
              else T_bv.mk_bvleq ~size ~signed:(Some false) lhs l
          | _ -> failwith "[mbp bv] bitwise-both: unexpected predicate")
      | (_, size, _, _) :: _ ->
          let ds =
            List.map parts ~f:(fun (_, _, f, g) ->
                let f0, f1 = instances ~size f and g0, g1 = instances ~size g in
                (T_bv.mk_bvxor ~size f0 g0, T_bv.mk_bvxor ~size f1 g1))
          in
          let join = List.reduce_exn ~f:(T_bv.mk_bvor ~size) in
          T_bool.mk_eq
            (T_bv.mk_bvand ~size (join (List.map ds ~f:fst))
               (join (List.map ds ~f:snd)))
            (T_bv.mk_bvnum ~size Z.zero)
      | [] -> failwith "[mbp bv] bitwise-both: no atom"
    in
    Set.union (Set.diff atoms xatoms) (normalize_mbp model gamma)

  (* leftmost-innermost subterm of [atom] accepted by [p] *)
  let find_innermost p atom =
    let rec find t =
      match t with
      | Term.FunApp (_, args, _) -> (
          match List.find_map args ~f:find with Some r -> Some r | None -> p t)
      | _ -> None
    in
    match atom with
    | Atom.App (_, args, _) -> List.find_map args ~f:find
    | _ -> None

  (* replace the leftmost-innermost subterm of [atom] rewritten by [g] *)
  let rewrite_innermost g atom =
    let rec scan go acc = function
      | [] -> None
      | a :: rest -> (
          match go a with
          | Some a' -> Some (List.rev_append acc (a' :: rest))
          | None -> scan go (a :: acc) rest)
    in
    let rec go t =
      match t with
      | Term.FunApp (fsym, args, info) -> (
          match scan go [] args with
          | Some args' -> Some (Term.mk_fsym_app fsym args' ~info)
          | None -> g t)
      | _ -> None
    in
    match atom with
    | Atom.App (pred, args, info) ->
        Option.map (scan go [] args) ~f:(fun args' -> Atom.mk_app ~info pred args')
    | _ -> None

  (* [sdiv]/[srem] detection: a signed division or remainder subterm *)
  let sign_split_shape = function
    | Term.FunApp (T_bv.BVDiv (size, signed), [ s; t ], _)
      when T_bv.is_signed signed ->
        Some (cmp_size ~size:(cmp_size ~size s) t, true, s, t)
    | Term.FunApp (T_bv.BVRem (size, signed), [ s; t ], _)
      when T_bv.is_signed signed ->
        Some (cmp_size ~size:(cmp_size ~size s) t, false, s, t)
    | _ -> None

  let sign_split_atom tvar atom =
    if not (Set.mem (Atom.fvs_of atom) tvar) then None
    else
      Option.map (find_innermost sign_split_shape atom)
        ~f:(fun (size, is_div, s, t) -> (size, is_div, s, t, atom))

  let sign_split ~print model tvar ~size ~is_div s t atom atoms =
    let w = T_bv.bits_of size in
    let half = T_bv.mk_bvnum ~size (Z.pow (Z.of_int 2) (w - 1)) in
    let ult a b = T_bv.mk_bvlt ~size ~signed:(Some false) a b in
    let ule a b = T_bv.mk_bvleq ~size ~signed:(Some false) a b in
    let holds g = Evaluator.eval @@ Evaluator.simplify_atom @@ Atom.subst model g in
    let guard u =
      if holds (ule half u) then (true, ule half u) else (false, ult u half)
    in
    let sneg, g1 = guard s in
    let tneg, g2 = guard t in
    let neg u = T_bv.mk_bvneg ~size u in
    let op a b =
      if is_div then T_bv.mk_bvdiv ~size ~signed:(Some false) a b
      else T_bv.mk_bvrem ~size ~signed:(Some false) a b
    in
    (* SMT-LIB sign cases, in the order (+,+), (-,+), (+,-), (-,-) *)
    let theta =
      match (sneg, tneg, is_div) with
      | false, false, _ -> op s t
      | true, false, _ -> neg (op (neg s) t)
      | false, true, true -> neg (op s (neg t))
      | false, true, false -> op s (neg t)
      | true, true, true -> op (neg s) (neg t)
      | true, true, false -> neg (op (neg s) (neg t))
    in
    match
      rewrite_innermost
        (fun u -> Option.map (sign_split_shape u) ~f:(fun _ -> theta))
        atom
    with
    | None -> None
    | Some atom' ->
        print
        @@ lazy
             (sprintf "[mbp bv] %s x=%s"
                (if is_div then "sdiv" else "srem")
                (Ident.name_of_tvar tvar));
        Some
          (Set.union (Set.remove atoms atom)
             (Set.Poly.of_list
             @@ List.concat_map [ atom'; g1; g2 ] ~f:(fun a ->
                    Set.to_list (normalize_mbp model a))))

  (* an unsigned division or remainder, of any divisor *)
  let rec has_udivrem t =
    match t with
    | Term.FunApp ((T_bv.BVDiv (_, signed) | T_bv.BVRem (_, signed)), args, _)
      when not (T_bv.is_signed signed) ->
        ignore args;
        true
    | Term.FunApp (_, args, _) -> List.exists args ~f:has_udivrem
    | _ -> false

  (* [urem-const] detection: f %u delta, delta not 0 and not 2^c, f free of /u and %u *)
  let urem_const_shape = function
    | Term.FunApp
        ( T_bv.BVRem (size, signed),
          [ f; Term.FunApp (T_bv.BVNum (_, n), [], _) ],
          _ )
      when not (T_bv.is_signed signed) ->
        let size = cmp_size ~size f in
        let delta = Z.erem n (Z.pow (Z.of_int 2) (T_bv.bits_of size)) in
        if Z.Compare.(delta = Z.zero) || Z.popcount delta = 1 || has_udivrem f
        then None
        else Some (size, f, delta)
    | _ -> None

  let urem_const_atom tvar atom =
    if not (Set.mem (Atom.fvs_of atom) tvar) then None
    else
      Option.map (find_innermost urem_const_shape atom)
        ~f:(fun (size, f, delta) -> (size, f, delta, atom))

  (* [udiv-const] detection: (f /u delta) ~ d, delta not 0 and not 2^c *)
  let udiv_const_atom tvar atoms atom =
    let div_of = function
      | Term.FunApp
          ( T_bv.BVDiv (size, signed),
            [ f; Term.FunApp (T_bv.BVNum (_, n), [], _) ],
            _ )
        when not (T_bv.is_signed signed) ->
          let size = cmp_size ~size f in
          let delta = Z.erem n (Z.pow (Z.of_int 2) (T_bv.bits_of size)) in
          if Z.Compare.(delta = Z.zero) || Z.popcount delta = 1 then None
          else Some (size, f, delta)
      | _ -> None
    in
    (* -(f /u delta) = d is f /u delta = -d *)
    let split_div psym = function
      | Term.FunApp (T_bv.BVNeg _, [ u ], _) -> (
          match psym with
          | T_bool.Eq -> Option.map (div_of u) ~f:(fun r -> (r, true))
          | _ -> None)
      | t -> Option.map (div_of t) ~f:(fun r -> (r, false))
    in
    let accepted = function
      | T_bool.Eq | T_bool.Neq -> true
      | T_bv.(BVLeq (_, s) | BVLt (_, s) | BVGeq (_, s) | BVGt (_, s)) ->
          not (T_bv.is_signed s)
      | _ -> false
    in
    (* the rows that weaken: they need every other x-bearing atom to be an inequality *)
    let weakening = function
      | T_bool.Neq -> true
      | T_bv.(BVLeq (_, _) | BVLt (_, _)) -> true
      | _ -> false
    in
    let others_all_ineq () =
      let others =
        Set.filter (Set.remove atoms atom) ~f:(fun a ->
            Set.mem (Atom.fvs_of a) tvar)
      in
      (not (Set.is_empty others))
      && Set.for_all others ~f:(function
           | Atom.App
               (Predicate.Psym T_bv.(BVLeq _ | BVLt _ | BVGeq _ | BVGt _), _, _) ->
               true
           | _ -> false)
    in
    let admit ((psym, _, _, _, _, _) as r) =
      if weakening psym && not (others_all_ineq ()) then None else Some r
    in
    match atom with
    | Atom.App (Predicate.Psym psym, [ t1; t2 ], _)
      when accepted psym && Set.mem (Atom.fvs_of atom) tvar -> (
        let other size negd t =
          if negd then T_bv.mk_bvneg ~size t else t
        in
        match split_div psym t1 with
        | Some ((size, f, delta), negd) when not (Set.mem (Term.fvs_of t2) tvar) ->
            let size = cmp_size ~size t2 in
            admit (psym, size, f, delta, other size negd t2, atom)
        | _ -> (
            match split_div psym t2 with
            | Some ((size, f, delta), negd)
              when not (Set.mem (Term.fvs_of t1) tvar) ->
                let size = cmp_size ~size t1 in
                admit
                  ( Predicate.flip_psym psym,
                    size,
                    f,
                    delta,
                    other size negd t1,
                    atom )
            | _ -> None))
    | _ -> None

  let udiv_const ~print model tvar psym ~size f delta d atom atoms =
    let w = T_bv.bits_of size in
    let cap = Z.sub (Z.pow (Z.of_int 2) w) Z.one in
    let bigd = Z.div cap delta in
    let numt n = T_bv.mk_bvnum ~size n in
    let times_delta t = T_bv.mk_bvmul ~size (numt delta) t in
    let succ t = T_bv.mk_bvadd ~size t (numt Z.one) in
    let sub a b = T_bv.mk_bvsub ~size a b in
    let ult a b = T_bv.mk_bvlt ~size ~signed:(Some false) a b in
    let ule a b = T_bv.mk_bvleq ~size ~signed:(Some false) a b in
    let holds g = Evaluator.eval @@ Evaluator.simplify_atom @@ Atom.subst model g in
    let dd = numt bigd in
    let d_delta = times_delta d in
    let hi = sub (times_delta (succ d)) (numt Z.one) in
    (* (guard, consequent); an empty consequent is top *)
    let branches =
      match psym with
      | T_bv.BVLeq (_, _) -> [ (ult d dd, [ ule f hi ]); (ule dd d, []) ]
      | T_bv.BVLt (_, _) -> [ (ule d dd, [ ult f d_delta ]); (ult dd d, []) ]
      | T_bv.BVGt (_, _) -> [ (ult d dd, [ ult hi f ]) ]
      | T_bv.BVGeq (_, _) -> [ (ule d dd, [ ule d_delta f ]) ]
      | T_bool.Eq ->
          [ (ule d dd, [ ule d_delta f; ult (sub f d_delta) (numt delta) ]) ]
      | T_bool.Neq ->
          (* extra branch: D <u d, consequent top *)
          let below = ult f d_delta in
          let above = ule (numt delta) (sub f d_delta) in
          [
            (ule d dd, [ (if holds below then below else above) ]);
            (ult dd d, []);
          ]
      | _ -> []
    in
    match List.find branches ~f:(fun (g, _) -> holds g) with
    | None -> None
    | Some (g, rho) ->
        print
        @@ lazy (sprintf "[mbp bv] udiv-const x=%s" (Ident.name_of_tvar tvar));
        Some
          (Set.union (Set.remove atoms atom)
             (Set.Poly.of_list
             @@ List.concat_map (g :: rho) ~f:(fun a ->
                    Set.to_list (normalize_mbp model a))))

  let urem_const ~print model tvar ~size f delta atom atoms =
    let w = T_bv.bits_of size in
    let two_w = Z.pow (Z.of_int 2) w in
    let numt n = T_bv.mk_bvnum ~size n in
    match model_value model f with
    | Term.FunApp (T_bv.BVNum (_, fv), [], _) -> (
        let k0 = Z.div (Z.erem fv two_w) delta in
        let dk = numt (Z.mul delta k0) in
        let diff = T_bv.mk_bvsub ~size f dk in
        match
          rewrite_innermost
            (fun t -> Option.map (urem_const_shape t) ~f:(fun _ -> diff))
            atom
        with
        | None -> None
        | Some atom' ->
            print
            @@ lazy
                 (sprintf "[mbp bv] urem-const x=%s k0=%s" (Ident.name_of_tvar tvar)
                    (Z.to_string k0));
            let ult a b = T_bv.mk_bvlt ~size ~signed:(Some false) a b in
            let ule a b = T_bv.mk_bvleq ~size ~signed:(Some false) a b in
            let guards = [ ule dk f; ult diff (numt delta) ] in
            Some
              (Set.union (Set.remove atoms atom)
                 (Set.Poly.of_list
                 @@ List.concat_map (atom' :: guards) ~f:(fun a ->
                        Set.to_list (normalize_mbp model a)))))
    | _ -> None

  (* [extract] detection. A sum is read as n-ary: an addition that is itself
     an operand of an addition is not an operand to judge, its own operands
     are (x[h:l] + q + c, as [mask-carry] leaves it, is not blocked) *)
  let arith_blocked tvar atoms =
    (* a slice of x is the one operand that suppresses nothing *)
    let is_slice = function
      | Term.FunApp (T_bv.BVEXTRACT _, [ Term.Var (v, _, _) ], _) ->
          Ident.tvar_equal v tvar
      | _ -> false
    in
    Set.exists atoms ~f:(fun atom ->
        not @@ Set.is_empty
        @@ Atom.filtered_terms_of atom ~f:(function
             | Term.FunApp
                 (((T_bv.BVAdd _ | T_bv.BVSub _ | T_bv.BVMul _ | T_bv.BVNeg _) as op), args, _)
               ->
                 List.exists args ~f:(fun a ->
                     Set.mem (Term.fvs_of a) tvar
                     && (match (op, a) with
                        | T_bv.BVAdd _, Term.FunApp (T_bv.BVAdd _, _, _) -> false
                        | _ -> true)
                     && (Option.is_some (affine_of tvar a) || not (is_slice a)))
             | _ -> false))

  let sort_of_tvar tvar atoms =
    Set.find_map atoms ~f:(fun atom ->
        Set.find_map
          (Atom.filtered_terms_of atom ~f:(function
            | Term.Var (v, T_bv.SBV _, _) -> Ident.tvar_equal v tvar
            | _ -> false))
          ~f:(function
            | Term.Var (_, T_bv.SBV size, _) -> Some size | _ -> None))

  let cut_points_of tvar size atoms =
    let w = T_bv.bits_of size in
    Set.fold atoms
      ~init:(Set.Poly.of_list [ 0; w ])
      ~f:(fun acc atom ->
        Set.fold
          (Atom.filtered_terms_of atom ~f:(function
            | Term.FunApp (T_bv.BVEXTRACT _, [ Term.Var (v, _, _) ], _) ->
                Ident.tvar_equal v tvar
            | _ -> false))
          ~init:acc
          ~f:(fun acc -> function
            | Term.FunApp (T_bv.BVEXTRACT (_, h, l), _, _) ->
                Set.add (Set.add acc l) (h + 1)
            | _ -> acc))

  let extract_atom tvar atoms =
    match sort_of_tvar tvar atoms with
    | Some size when not (arith_blocked tvar atoms) ->
        let cuts =
          cut_points_of tvar size atoms
          |> Set.to_list
          |> List.sort ~compare:Int.compare
        in
        if List.length cuts < 3 then None else Some (size, cuts)
    | _ -> None

  (* y_k = x[c_k-1:c_{k-1}], k=1..m, low to high *)
  let extract ~print model tvar ~size cuts atoms =
    print @@ lazy (sprintf "[mbp bv] extract x=%s" (Ident.name_of_tvar tvar));
    let xvar = Term.mk_var tvar (T_bv.SBV size) in
    let rec slices = function
      | c0 :: (c1 :: _ as rest) ->
          let width = c1 - c0 in
          let y = Ident.mk_fresh_tvar () in
          let sort = T_bv.SBV (Some width) in
          let value =
            model_value model
              (T_bv.mk_bvextract ~size:(Some width) (c1 - 1) c0 xvar)
          in
          (y, sort, width, value) :: slices rest
      | _ -> []
    in
    let ys = slices cuts in
    let model' =
      List.fold ys ~init:model ~f:(fun m (y, _, _, value) ->
          Map.Poly.set m ~key:y ~data:value)
    in
    let repl =
      match ys with
      | (y1, sort1, w1, _) :: rest ->
          List.fold rest
            ~init:(w1, Term.mk_var y1 sort1)
            ~f:(fun (accw, acct) (yk, sortk, wk, _) ->
              ( accw + wk,
                T_bv.mk_bvconcat ~size1:(Some wk) ~size2:(Some accw)
                  (Term.mk_var yk sortk) acct ))
          |> snd
      | [] -> xvar
    in
    let sub = Map.Poly.singleton tvar repl in
    let atoms' =
      Set.concat_map atoms ~f:(Atom.subst sub >> normalize_mbp model)
    in
    (model', List.map ys ~f:(fun (y, _, _, _) -> y), atoms')

  (* [eq-concat]/[neq-concat] detection: pick the concat side *)
  let concat_side_with_tvar tvar u =
    match u with
    | Term.FunApp (T_bv.BVCONCAT (size1, size2), [ uh; ul ], _)
      when Set.mem (Term.fvs_of u) tvar ->
        Some (size1, size2, uh, ul)
    | _ -> None

  let pick_concat_sides tvar t1 t2 =
    match concat_side_with_tvar tvar t1 with
    | Some (s1, s2, uh, ul) -> Some (s1, s2, uh, ul, t2)
    | None -> (
        match concat_side_with_tvar tvar t2 with
        | Some (s1, s2, uh, ul) -> Some (s1, s2, uh, ul, t1)
        | None -> None)

  (* an atom where x is an operand of an addition, a product or a negation *)
  let arith_layer tvar atom =
    not
    @@ Set.is_empty
    @@ Atom.filtered_terms_of atom ~f:(function
         | Term.FunApp
             ((T_bv.BVAdd _ | T_bv.BVSub _ | T_bv.BVMul _ | T_bv.BVNeg _), args, _)
           ->
             List.exists args ~f:(fun a -> Set.mem (Term.fvs_of a) tvar)
         | _ -> false)

  (* a shift by a non-numeral or an extension over x inside [t] *)
  let rec has_shift_ext_of tvar = function
    | Term.FunApp
        ( (T_bv.BVSHL _ | T_bv.BVLSHR _ | T_bv.BVASHR _),
          [ u; Term.FunApp (T_bv.BVNum _, [], _) ],
          _ ) ->
        has_shift_ext_of tvar u
    | Term.FunApp
        ( ( T_bv.BVSHL _ | T_bv.BVLSHR _ | T_bv.BVASHR _ | T_bv.BVSEXT _
          | T_bv.BVZEXT _ ),
          args,
          _ )
      when List.exists args ~f:(fun a -> Set.mem (Term.fvs_of a) tvar) ->
        true
    | Term.FunApp (_, args, _) -> List.exists args ~f:(has_shift_ext_of tvar)
    | _ -> false

  (* x itself or a slice of bare x *)
  let bare_x_or_slice tvar = function
    | Term.Var (v, _, _)
    | Term.FunApp (T_bv.BVEXTRACT _, [ Term.Var (v, _, _) ], _) ->
        Ident.tvar_equal v tvar
    | _ -> false

  (* the expansion of an extension: zext_k u -> 0^k o u, sext_k u off the
     arithmetic layer and only when u has no shift and no extension over x
     inside, a shift by a numeral excepted: the k copies of the sign bit
     would multiply them, and termination counts shifts and extensions before
     everything else in an atom. The arguments are expanded first, so an
     inner extension left over is one this condition declined; a shift by a
     non-numeral has no rewriting, and its atom is projected by the fallback
     either way.
     A zext_k u over x that is a direct operand of +, * or unary minus is
     kept: the sum's isolation (normalization 31 or [add-interval]) takes it
     as one operand and [extend] drops it to u; expanded, it would be a
     concat under the sum, which [cmp-concat] takes only with x bare.
     In the arithmetic layer a sext_k u over x, u neither x nor a slice of
     bare x, becomes zext_k (u + 2^(m-1)) - 2^(m-1) (m = |u|; the inner
     numeral has width m, the outer one m + k), the zero_extend form of
     [IJCAR 2020] Fig. 3: the same value, since adding 2^(m-1) maps the signed
     range of u onto the unsigned one in order, and its extension is again a
     direct operand of the sum, so it is isolated and dropped as above. A
     bare u is left to the sign-bit concat, which keeps x bare for
     [cmp-concat]; rewritten, it would leave x + 2^(m-1), whose interval the
     fallback receives once a slice of x stands beside it. Termination: the
     sign extension is replaced by a zero extension, which the measure counts
     after it *)
  let rec expand_extend ?(under_arith = false) ~slice_layer tvar t =
    match t with
    | Term.FunApp (fsym, args, info) -> (
        let arith_here =
          match fsym with
          | T_bv.(BVAdd _ | BVSub _ | BVMul _ | BVNeg _) -> true
          | _ -> false
        in
        let args =
          List.map args
            ~f:(expand_extend ~under_arith:arith_here ~slice_layer tvar)
        in
        let dflt () = Term.mk_fsym_app fsym args ~info in
        match (fsym, args) with
        | T_bv.BVZEXT (_, k), [ u ]
          when k >= 1 && under_arith && Set.mem (Term.fvs_of u) tvar ->
            dflt ()
        | T_bv.BVSEXT (size, k), [ u ]
          when k >= 1 && (not slice_layer)
               && Set.mem (Term.fvs_of u) tvar
               && not (bare_x_or_slice tvar u) ->
            let m = T_bv.bits_of (cmp_size ~size u) in
            let half w =
              T_bv.mk_bvnum ~size:(Some w) (Z.pow (Z.of_int 2) (m - 1))
            in
            T_bv.mk_bvsub ~size:(Some (m + k))
              (T_bv.mk_bvzext ~size:(Some m) k
                 (T_bv.mk_bvadd ~size:(Some m) u (half m)))
              (half (m + k))
        | T_bv.BVZEXT (size, k), [ u ] when k >= 1 ->
            let m = T_bv.bits_of (cmp_size ~size u) in
            T_bv.mk_bvconcat ~size1:(Some k) ~size2:(Some m)
              (T_bv.mk_bvnum ~size:(Some k) Z.zero)
              u
        | T_bv.BVSEXT (size, k), [ u ]
          when k >= 1 && slice_layer && not (has_shift_ext_of tvar u) ->
            let m = T_bv.bits_of (cmp_size ~size u) in
            let bit = mk_extract (m - 1) (m - 1) u in
            let rec fill j acc =
              if j >= k then acc
              else
                fill (j + 1)
                  (T_bv.mk_bvconcat ~size1:(Some 1) ~size2:(Some (m + j)) bit acc)
            in
            fill 0 u
        | _ -> dflt ())
    | t -> t

  (* [extend] detection: ext_k u ~ t, with the extension moved to the left *)
  let extend_atom tvar atom =
    match atom with
    | Atom.App (Predicate.Psym psym, [ t1; t2 ], _)
      when Set.mem (Atom.fvs_of atom) tvar -> (
        let ext_of = function
          | Term.FunApp (T_bv.BVSEXT (size, k), [ u ], _) when k >= 1 ->
              Some (true, size, k, u)
          | Term.FunApp (T_bv.BVZEXT (size, k), [ u ], _) when k >= 1 ->
              Some (false, size, k, u)
          | _ -> None
        in
        (* sign_extend has a value range that unsigned order splits in two *)
        let accepted signed_ext = function
          | T_bool.Eq | T_bool.Neq -> true
          | T_bv.(BVLeq (_, s) | BVLt (_, s) | BVGeq (_, s) | BVGt (_, s)) ->
              (not signed_ext) || T_bv.is_signed s
          | _ -> false
        in
        let oriented =
          match ext_of t1 with
          | Some (se, size, k, u) -> Some (psym, se, size, k, u, t2)
          | None ->
              Option.map (ext_of t2) ~f:(fun (se, size, k, u) ->
                  (Predicate.flip_psym psym, se, size, k, u, t1))
        in
        match oriented with
        | Some (psym', se, size, k, u, t)
          when accepted se psym' && not (Set.mem (Term.fvs_of t) tvar) ->
            Some (psym', se, cmp_size ~size u, k, u, t, atom)
        | _ -> None)
    | _ -> None

  let extend ~print model tvar psym ~signed_ext ~size k u t atom atoms =
    print @@ lazy (sprintf "[mbp bv] extend x=%s" (Ident.name_of_tvar tvar));
    let m = T_bv.bits_of size in
    let n = m + k in
    let szn = Some n in
    let num v = T_bv.mk_bvnum ~size:szn v in
    let pow e = Z.pow (Z.of_int 2) e in
    (* the order the range is measured in, and the order after the width drops *)
    let sigma =
      match psym with
      | T_bv.(BVLeq (_, s) | BVLt (_, s) | BVGeq (_, s) | BVGt (_, s)) ->
          Some (T_bv.is_signed s)
      | _ -> Some signed_ext
    in
    let sigma' = Some (signed_ext && Option.value sigma ~default:false) in
    let lo, hi =
      if signed_ext then
        (num (Z.sub (pow n) (pow (m - 1))), num (Z.sub (pow (m - 1)) Z.one))
      else (num Z.zero, num (Z.sub (pow m) Z.one))
    in
    let leq a b = T_bv.mk_bvleq ~size:szn ~signed:sigma a b in
    let lt a b = T_bv.mk_bvlt ~size:szn ~signed:sigma a b in
    let holds g = Evaluator.eval @@ Evaluator.simplify_atom @@ Atom.subst model g in
    let low = mk_extract (m - 1) 0 t in
    let rho =
      match psym with
      | T_bool.Eq -> [ T_bool.mk_eq u low ]
      | T_bool.Neq -> [ T_bool.mk_neq u low ]
      | T_bv.BVLeq (_, _) -> [ T_bv.mk_bvleq ~size ~signed:sigma' u low ]
      | T_bv.BVLt (_, _) -> [ T_bv.mk_bvlt ~size ~signed:sigma' u low ]
      | T_bv.BVGeq (_, _) -> [ T_bv.mk_bvgeq ~size ~signed:sigma' u low ]
      | T_bv.BVGt (_, _) -> [ T_bv.mk_bvgt ~size ~signed:sigma' u low ]
      | _ -> []
    in
    let branches =
      [ ([ leq lo t; leq t hi ], rho); ([ lt t lo ], []); ([ lt hi t ], []) ]
    in
    match List.find branches ~f:(fun (g, _) -> List.for_all g ~f:holds) with
    | None -> None
    | Some (g, r) ->
        Some
          (List.fold (g @ r)
             ~init:(Set.remove atoms atom)
             ~f:(fun acc a -> Set.union acc (normalize_mbp model a)))

  let eq_concat_atom tvar = function
    | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _) as atom ->
        Option.map (pick_concat_sides tvar t1 t2) ~f:(fun (s1, s2, uh, ul, t) ->
            (s1, s2, uh, ul, t, atom))
    | _ -> None

  (* t_H = t[w-1:k], t_L = t[k-1:0], k = |u_L| *)
  let hi_lo_of ~size1 ~size2 t =
    let w2 = T_bv.bits_of size2 in
    let w = T_bv.bits_of size1 + w2 in
    (mk_extract (w - 1) w2 t, mk_extract (w2 - 1) 0 t)

  let eq_concat ~print model tvar ~size1 ~size2 uh ul t atom atoms =
    print @@ lazy (sprintf "[mbp bv] eq-concat x=%s" (Ident.name_of_tvar tvar));
    let th, tl = hi_lo_of ~size1 ~size2 t in
    Set.remove atoms atom
    |> Fn.flip Set.union (normalize_mbp model (T_bool.mk_eq uh th))
    |> Fn.flip Set.union (normalize_mbp model (T_bool.mk_eq ul tl))

  let neq_concat_atom tvar = function
    | Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _) as atom ->
        Option.map (pick_concat_sides tvar t1 t2) ~f:(fun (s1, s2, uh, ul, t) ->
            (s1, s2, uh, ul, t, atom))
    | _ -> None

  let neq_concat ~print model tvar ~size1 ~size2 uh ul t atom atoms =
    print @@ lazy (sprintf "[mbp bv] neq-concat x=%s" (Ident.name_of_tvar tvar));
    let th, tl = hi_lo_of ~size1 ~size2 t in
    let m_neq a b =
      Evaluator.eval @@ Evaluator.simplify_atom
      @@ Atom.subst model (T_bool.mk_neq a b)
    in
    let neq_lit =
      if m_neq uh th then T_bool.mk_neq uh th else T_bool.mk_neq ul tl
    in
    Set.remove atoms atom |> Fn.flip Set.union (normalize_mbp model neq_lit)

  (* concat widths, filled in from the total width when missing *)
  let concat_sizes ~size other size1 size2 =
    match (size1, size2, cmp_size ~size other) with
    | None, Some w2, Some w -> (Some (w - w2), size2)
    | Some w1, None, Some w -> (size1, Some (w - w1))
    | _ -> (size1, size2)

  (* [cmp-concat] detection: (u_H o u_L) ~ t *)
  let cmp_concat_atom tvar = function
    | Atom.App
        ( Predicate.Psym
            (T_bv.(
               ( BVLeq (size, Some _)
               | BVGeq (size, Some _)
               | BVLt (size, Some _)
               | BVGt (size, Some _) )) as psym),
          [ t1; t2 ],
          _ ) as atom ->
        let oriented =
          match concat_side_with_tvar tvar t1 with
          | Some (s1, s2, uh, ul) -> Some (psym, s1, s2, uh, ul, t2)
          | None ->
              Option.map (concat_side_with_tvar tvar t2)
                ~f:(fun (s1, s2, uh, ul) ->
                  (Predicate.flip_psym psym, s1, s2, uh, ul, t1))
        in
        Option.map oriented ~f:(fun (psym', s1, s2, uh, ul, other) ->
            let s1, s2 = concat_sizes ~size other s1 s2 in
            (psym', s1, s2, uh, ul, other, atom))
    | _ -> None

  let cmp_concat ~print model tvar psym ~size1 ~size2 uh ul t atom atoms =
    print @@ lazy (sprintf "[mbp bv] cmp-concat x=%s" (Ident.name_of_tvar tvar));
    let th, tl = hi_lo_of ~size1 ~size2 t in
    (* B1 strict, B2 low part unsigned *)
    let b1, b2_low =
      let unsigned = Some false in
      match psym with
      | T_bv.BVLeq (_, signed) ->
          ( T_bv.mk_bvlt ~size:size1 ~signed uh th,
            T_bv.mk_bvleq ~size:size2 ~signed:unsigned ul tl )
      | T_bv.BVLt (_, signed) ->
          ( T_bv.mk_bvlt ~size:size1 ~signed uh th,
            T_bv.mk_bvlt ~size:size2 ~signed:unsigned ul tl )
      | T_bv.BVGeq (_, signed) ->
          ( T_bv.mk_bvgt ~size:size1 ~signed uh th,
            T_bv.mk_bvgeq ~size:size2 ~signed:unsigned ul tl )
      | T_bv.BVGt (_, signed) ->
          ( T_bv.mk_bvgt ~size:size1 ~signed uh th,
            T_bv.mk_bvgt ~size:size2 ~signed:unsigned ul tl )
      | _ -> failwith "[mbp bv] cmp-concat: unexpected predicate"
    in
    let holds g =
      Evaluator.eval @@ Evaluator.simplify_atom @@ Atom.subst model g
    in
    let lits = if holds b1 then [ b1 ] else [ T_bool.mk_eq uh th; b2_low ] in
    let lit_atoms =
      List.concat_map lits ~f:(fun g -> Set.to_list (normalize_mbp model g))
      |> Set.Poly.of_list
    in
    Set.union (Set.remove atoms atom) lit_atoms

  (* q when t is x + q, read through additions and unary minuses, with x of
     coefficient 1 and q the sum of the other addends, all x-free *)
  let offset_sum_q tvar t =
    let mem t = Set.mem (Term.fvs_of t) tvar in
    let rec addends = function
      | Term.FunApp (T_bv.BVAdd _, [ a; b ], _) -> addends a @ addends b
      | Term.FunApp (T_bv.BVNeg _, [ a ], _) ->
          List.map (addends a) ~f:(fun (s, u) -> (not s, u))
      | u -> [ (false, u) ]
    in
    match desub t with
    | Term.FunApp (T_bv.BVAdd size, _, _) as t -> (
        let xs, rs = List.partition_tf (addends t) ~f:(fun (_, u) -> mem u) in
        match xs with
        | [ (false, Term.Var (v, _, _)) ] when Ident.tvar_equal v tvar ->
            Some
              (Evaluator.simplify_term
              @@ List.fold rs ~init:(T_bv.mk_bvnum ~size Z.zero)
                   ~f:(fun acc (s, u) ->
                     T_bv.mk_bvadd ~size acc
                       (if s then T_bv.mk_bvneg ~size u else u)))
        | _ -> None)
    | _ -> None

  (* the operators below which a sum x + q is of kind (a) for [offset] *)
  let offset_non_arith = function
    | T_bv.(
        ( BVAnd _ | BVOr _ | BVXor _ | BVNot _ | BVEXTRACT _ | BVCONCAT _
        | BVSHL _ | BVLSHR _ | BVASHR _ | BVSEXT _ | BVZEXT _ )) ->
        true
    | _ -> false

  (* [offset] detection. Every occurrence of x must be either (a) the operand
     x of a sum x + q (as in [offset_sum_q]) that is a direct operand of a
     bitwise operator, a negation, a slice, a concat, a shift or an
     extension, whatever lies above that operator; or (b) inside a side of an
     atom that is affine in x as a whole. All the sums of kind (a) must share
     one q (compared syntactically after simplification, so a reordered q
     declines), and there must be at least one. Returns (size, q). A slice
     directly over x, a bare x under a bitwise operator, a product or a
     second x-operand in the sum, and a sum that is an operand of an
     arithmetic operator decline *)
  let offset_atom tvar atoms =
    let mem t = Set.mem (Term.fvs_of t) tvar in
    let rec occ ~under t =
      if not (mem t) then Some []
      else
        match if under then offset_sum_q tvar t else None with
        | Some q -> Some [ q ]
        | None -> (
            match t with
            | Term.FunApp (fsym, args, _) ->
                Option.all
                  (List.map args ~f:(occ ~under:(offset_non_arith fsym)))
                |> Option.map ~f:List.concat
            | _ -> None)
    in
    let side t =
      if Option.is_some (affine_of tvar t) then Some [] else occ ~under:false t
    in
    match sort_of_tvar tvar atoms with
    | None -> None
    | Some size -> (
        let qs =
          Set.to_list atoms
          |> List.map ~f:(fun atom ->
              if not (Set.mem (Atom.fvs_of atom) tvar) then Some []
              else
                match atom with
                | Atom.App (Predicate.Psym _, [ t1; t2 ], _) ->
                    Option.map2 (side t1) (side t2) ~f:( @ )
                | _ -> None)
          |> Option.all |> Option.map ~f:List.concat
        in
        match qs with
        | Some (q :: qs) when List.for_all qs ~f:(fun q' -> Stdlib.(q' = q)) ->
            Some (size, q)
        | _ -> None)

  (* [offset]: the change of variable x := y - q, exact because z -> z + q is
     a bijection of the bit-vectors of width w. Every sum x + q of kind (a)
     becomes the fresh y, with M'(y) = M(x + q), and every affine side
     a*x + r becomes a*y + (r - a*q). The rewriting walks the terms as
     [offset_atom] did, which has checked that every sum it meets is x + q
     with the one q. The output has y bare under the operators that had
     x + q below them and no occurrence of kind (a), so the rule does not
     apply to it again *)
  let offset ~print model tvar ~size q atoms =
    print @@ lazy (sprintf "[mbp bv] offset x=%s" (Ident.name_of_tvar tvar));
    let mem t = Set.mem (Term.fvs_of t) tvar in
    let xvar = Term.mk_var tvar (T_bv.SBV size) in
    let y = Ident.mk_fresh_tvar () in
    let yvar = Term.mk_var y (T_bv.SBV size) in
    let model' =
      Map.Poly.set model ~key:y
        ~data:(model_value model (T_bv.mk_bvadd ~size xvar q))
    in
    let rec repl ~under t =
      if not (mem t) then t
      else
        match if under then offset_sum_q tvar t else None with
        | Some _ -> yvar
        | None -> (
            match t with
            | Term.FunApp (fsym, args, info) ->
                Term.mk_fsym_app fsym
                  (List.map args ~f:(repl ~under:(offset_non_arith fsym)))
                  ~info
            | t -> t)
    in
    let side t =
      if not (mem t) then t
      else
        match affine_of tvar t with
        | Some (a, r) ->
            let an = T_bv.mk_bvnum ~size a in
            Evaluator.simplify_term
            @@ T_bv.mk_bvadd ~size (T_bv.mk_bvmul ~size an yvar)
                 (T_bv.mk_bvsub ~size r (T_bv.mk_bvmul ~size an q))
        | None -> repl ~under:false t
    in
    let atoms' =
      Set.concat_map atoms ~f:(function
        | Atom.App (pred, [ t1; t2 ], info) as atom
          when Set.mem (Atom.fvs_of atom) tvar ->
            normalize_mbp model (Atom.mk_app ~info pred [ side t1; side t2 ])
        | atom -> Set.Poly.singleton atom)
    in
    (model', y, atoms')

  (* the side (x + q) & m of a [mask-carry] literal: q as in [offset_sum_q],
     m a numeral other than 0 and 2^w - 1. Returns (q, m) *)
  let mask_carry_side tvar ~w t =
    let two_w = Z.pow (Z.of_int 2) w in
    let with_mask m u =
      let m = Z.erem m two_w in
      if Z.Compare.(m = Z.zero || m = Z.pred two_w) then None
      else Option.map (offset_sum_q tvar u) ~f:(fun q -> (q, m))
    in
    match t with
    | Term.FunApp
        (T_bv.BVAnd _, [ u; Term.FunApp (T_bv.BVNum (_, m), [], _) ], _)
    | Term.FunApp
        (T_bv.BVAnd _, [ Term.FunApp (T_bv.BVNum (_, m), [], _); u ], _) ->
        with_mask m u
    | _ -> None

  (* the literals (x + q) & m ~ t (either side) with ~ an equality, a
     disequality or a comparison and t x-free, as (atom, q, m, mask side
     first) *)
  let mask_carry_lits tvar ~w atoms =
    let free t = not (Set.mem (Term.fvs_of t) tvar) in
    Set.to_list atoms
    |> List.filter_map ~f:(function
      | Atom.App
          ( Predicate.Psym
              T_bv.(
                ( T_bool.Eq | T_bool.Neq | BVLt _ | BVLeq _ | BVGt _
                | BVGeq _ )),
            [ t1; t2 ],
            _ ) as atom -> (
          match (mask_carry_side tvar ~w t1, mask_carry_side tvar ~w t2) with
          | Some (q, m), _ when free t2 -> Some (atom, q, m, true)
          | _, Some (q, m) when free t1 -> Some (atom, q, m, false)
          | _ -> None)
      | _ -> None)

  (* [mask-carry] detection: a literal of [mask_carry_lits] such that, once
     every such literal is split, [extract] is not blocked, i.e. every other
     operand of arithmetic containing x is a slice of x. Without this the
     split would reach [fallback] anyway, and its guards, instantiated at
     M(x), would only narrow the fallback's output. Returns
     (size, w, atom, q, m, mask side first) *)
  let mask_carry_atom tvar atoms =
    match sort_of_tvar tvar atoms with
    | None -> None
    | Some size -> (
        let w = T_bv.bits_of size in
        match mask_carry_lits tvar ~w atoms with
        | [] -> None
        | (atom, q, m, left) :: _ as lits ->
            let zero = T_bv.mk_bvnum ~size Z.zero in
            let rest =
              Set.Poly.map atoms ~f:(fun a ->
                  match
                    List.find lits ~f:(fun (a', _, _, _) -> Stdlib.(a == a'))
                  with
                  | Some (_, _, _, l) -> (
                      match a with
                      | Atom.App (pred, [ t1; t2 ], info) ->
                          Atom.mk_app ~info pred
                            (if l then [ zero; t2 ] else [ t1; zero ])
                      | a -> a)
                  | None -> a)
            in
            if arith_blocked tvar rest then None
            else Some (size, w, atom, q, m, left))

  (* [mask-carry]: for each run of ones [h:l] of m, from the top, the carry c
     into bit l of x + q is read from M (c = 1 iff M(x[l-1:0]) >u
     M(~q[l-1:0]), c = 0 when l = 0) and fixed by a guard on l bits; under
     the guards (x + q) & m is the concat, from the top, of 0^z for each run
     of zeros of length z and of x[h:l] + q[h:l] + c for each run of ones.
     The guards hold in M, so the result holds in M and implies the literal;
     it is an equivalence when m = 2^k - 1. Every x-operand of arithmetic in
     the result is a slice of x, and the guards compare a slice of x with an
     x-free term, so [extract] applies next. Identity: the carry
     decomposition of a ripple-carry adder. Declines (None) when M does not
     evaluate q to a numeral *)
  let mask_carry ~print model tvar ~size ~w q m atom left atoms =
    let xvar = Term.mk_var tvar (T_bv.SBV size) in
    let qv = model_value model q and xv = model_value model xvar in
    match (qv, xv) with
    | ( Term.FunApp (T_bv.BVNum (_, qn), [], _),
        Term.FunApp (T_bv.BVNum (_, xn), [], _) ) ->
        print
        @@ lazy (sprintf "[mbp bv] mask-carry x=%s" (Ident.name_of_tvar tvar));
        let pow2 k = Z.pow (Z.of_int 2) k in
        let low k n = Z.erem n (pow2 k) in
        (* the runs of m from the bit 0 up, as (bit, width, ones) *)
        let rec runs i acc =
          if i >= w then List.rev acc
          else
            let b = Z.testbit m i in
            let rec len j = if j < w && Bool.(Z.testbit m j = b) then len (j + 1) else j in
            let j = len i in
            runs j ((i, j - i, b) :: acc)
        in
        let pieces, guards =
          List.fold (runs 0 []) ~init:([], [])
            ~f:(fun (pieces, guards) (l, k, ones) ->
              if not ones then
                ((k, T_bv.mk_bvnum ~size:(Some k) Z.zero) :: pieces, guards)
              else
                let h = l + k - 1 in
                let c =
                  l > 0 && Z.Compare.(Z.(low l xn + low l qn) >= pow2 l)
                in
                let sz = Some k in
                (* x[h:l] is kept a direct operand of the sum, the shape
                   [extract] accepts *)
                let qc =
                  Evaluator.simplify_term
                  @@
                  if c then
                    T_bv.mk_bvadd ~size:sz (mk_extract h l q)
                      (T_bv.mk_bvnum ~size:sz Z.one)
                  else mk_extract h l q
                in
                let run = T_bv.mk_bvadd ~size:sz (mk_extract h l xvar) qc in
                let guard =
                  if l = 0 then []
                  else
                    let szl = Some l in
                    let xl = mk_extract (l - 1) 0 xvar in
                    let nql =
                      Evaluator.simplify_term
                      @@ T_bv.mk_bvnot ~size:szl (mk_extract (l - 1) 0 q)
                    in
                    [
                      (if c then T_bv.mk_bvlt ~size:szl ~signed:(Some false) nql xl
                       else T_bv.mk_bvleq ~size:szl ~signed:(Some false) xl nql);
                    ]
                in
                ((k, run) :: pieces, guard @ guards))
        in
        (* pieces is from the top down; fold the concat from the bottom up *)
        let pi =
          match List.rev pieces with
          | (k0, t0) :: higher ->
              List.fold higher ~init:(k0, t0) ~f:(fun (accw, acc) (k, t) ->
                  ( accw + k,
                    T_bv.mk_bvconcat ~size1:(Some k) ~size2:(Some accw) t acc ))
              |> snd
          | [] -> assert false
        in
        let atom' =
          match atom with
          | Atom.App (pred, [ t1; t2 ], info) ->
              Atom.mk_app ~info pred (if left then [ pi; t2 ] else [ t1; pi ])
          | a -> a
        in
        Some
          (Set.union (Set.remove atoms atom)
             (Set.Poly.of_list
             @@ List.concat_map (atom' :: guards) ~f:(fun a ->
                    Set.to_list (normalize_mbp model a))))
    | _ -> None

  (* signed comparison normalization, after [cmp-concat] *)
  let signed_cmp_atom tvar atom =
    if Set.mem (Atom.fvs_of atom) tvar then
      Option.map (unsign_cmp tvar atom) ~f:(fun atom' -> (atom, atom'))
    else None

  let signed_cmp ~print model tvar atom atom' atoms =
    print @@ lazy (sprintf "[mbp bv] signed-cmp x=%s" (Ident.name_of_tvar tvar));
    Set.union (Set.remove atoms atom) (normalize_mbp model atom')

  (* forbidden interval [lo; hi) of a comparison literal, by the shape row *)
  let cmp_rows ~size (nz1, nz2) psym r1 r2 =
    let simp = Evaluator.simplify_term in
    let neg t = simp @@ T_bv.mk_bvneg ~size t in
    let sub a b = simp @@ T_bv.mk_bvsub ~size a b in
    let succ t = simp @@ T_bv.mk_bvadd ~size t (T_bv.mk_bvnum ~size Z.one) in
    match (nz1, nz2, psym) with
    | 1, 0, T_bv.BVLt (_, Some false) -> Some (sub r2 r1, neg r1)
    | 1, 0, T_bv.BVLeq (_, Some false) -> Some (succ (sub r2 r1), neg r1)
    | 1, 0, T_bool.Neq -> Some (sub r2 r1, succ (sub r2 r1))
    | 0, 1, T_bv.BVLt (_, Some false) -> Some (neg r2, succ (sub r1 r2))
    | 0, 1, T_bv.BVLeq (_, Some false) -> Some (neg r2, sub r1 r2)
    | 0, 1, T_bool.Neq -> Some (sub r1 r2, succ (sub r1 r2))
    | 1, 1, T_bv.(BVLt (_, Some false) | BVLeq (_, Some false)) ->
        Some (neg r2, neg r1)
    | _ -> None

  (* coefficient -1: the table read for -x, reversed to [1-hi; 1-lo) *)
  let reflect_interval ~size (lo, hi) =
    let one_minus t =
      Evaluator.simplify_term
      @@ T_bv.mk_bvsub ~size (T_bv.mk_bvnum ~size Z.one) t
    in
    (one_minus hi, one_minus lo)

  (* [cmp-interval] detection: forbidden interval [lo, hi) of one literal *)
  let interval_of tvar ~size atom =
    let two_w = Z.pow (Z.of_int 2) (T_bv.bits_of size) in
    let unit_coeff c =
      let c' = Z.erem c two_w in
      if Z.Compare.(c' = Z.zero) then Some 0
      else if Z.Compare.(c' = Z.one) then Some 1
      else if Z.Compare.(c' = Z.(two_w - one)) then Some (-1)
      else None
    in
    let reverse = reflect_interval ~size in
    match atom with
    | Atom.App (Predicate.Psym psym, [ t1; t2 ], _) -> (
        let psym, t1, t2 =
          match psym with
          | T_bv.(BVGeq (_, Some false) | BVGt (_, Some false)) ->
              (Predicate.flip_psym psym, t2, t1)
          | _ -> (psym, t1, t2)
        in
        match (affine_of tvar t1, affine_of tvar t2) with
        | Some (c1, r1), Some (c2, r2) -> (
            match (unit_coeff c1, unit_coeff c2) with
            | Some a1, Some a2 ->
                let nzs = List.filter [ a1; a2 ] ~f:(fun a -> a <> 0) in
                let neg_sgn = List.exists nzs ~f:(fun a -> a < 0) in
                let pos_sgn = List.exists nzs ~f:(fun a -> a > 0) in
                if neg_sgn && pos_sgn then None
                else
                  let nz a = if a = 0 then 0 else 1 in
                  let iv = cmp_rows ~size (nz a1, nz a2) psym r1 r2 in
                  Option.map iv ~f:(fun iv -> if neg_sgn then reverse iv else iv)
            | _ -> None)
        | _ -> None)
    | _ -> None

  let cmp_interval_atoms tvar atoms =
    match sort_of_tvar tvar atoms with
    | None -> None
    | Some size ->
        let ivs =
          Set.to_list atoms
          |> List.filter ~f:(fun a -> Set.mem (Atom.fvs_of a) tvar)
          |> List.map ~f:(interval_of tvar ~size)
        in
        if List.exists ivs ~f:Option.is_none then None
        else Some (size, List.filter_opt ivs)

  let cmp_interval ~print model tvar ~size ivs atoms =
    print
    @@ lazy (sprintf "[mbp bv] cmp-interval x=%s" (Ident.name_of_tvar tvar));
    let two_w = Z.pow (Z.of_int 2) (T_bv.bits_of size) in
    let mval t = snd @@ T_bv.let_bv (model_value model t) in
    let v = mval (Term.mk_var tvar (T_bv.SBV size)) in
    let cands =
      List.filter_map ivs ~f:(fun (lo, hi) ->
          let mhi = mval hi in
          if Z.Compare.(mval lo = mhi) then None
          else
            let e = Z.erem Z.(mhi - v) two_w in
            Some ((if Z.Compare.(e = Z.zero) then two_w else e), hi))
    in
    let tau =
      match
        List.max_elt cands ~compare:(fun (e1, _) (e2, _) -> Z.compare e1 e2)
      with
      | Some (_, hi) -> hi
      | None -> T_bv.mk_bvnum ~size Z.zero
    in
    let sub = Map.Poly.singleton tvar tau in
    Set.concat_map atoms ~f:(Atom.subst sub >> normalize_mbp model)

  (* the one non-affine x-operand of a sum.
     [isolate_of tvar t] = Some (size, neg, g, r) when t, read through
     additions and unary minuses, is g + r (neg = false) or -g + r
     (neg = true) with r the sum of the x-free addends (0 when there is none)
     and g the only addend mentioning x, under at least one addition or minus.
     g must be a form a rule consumes once it stands alone on its side: a
     bitwise and/or, a concat, a shift by a numeral, an extension, or, when
     [~quotient] holds, an unsigned quotient or remainder by a numeral that
     [udiv-const] and [urem-const] take (neither 0 nor a power of two), with
     its dividend as it is. A quotient by any other divisor (a symbolic one,
     as [sdiv] and [srem] leave) has no rule to consume it once isolated, and
     choosing an [add-interval] branch for it only weakens what the fallback
     returns (enumerated at widths up to 3). g may contain
     arithmetic over x ((x + q) & m, zero_extend (x + q), (x + 1) /u d):
     termination is charged to the sum that leaves the top of the side, and
     the isolated g is not a sum, so the step does not repeat. An affine g is
     not isolated (it is read by [cmp-interval] and the affine equality rules
     as it is), nor are a numeral coefficient other than +-1 on g, a bitwise
     negation (whose arithmetic reading must come first) and a slice *)
  let isolable_quotient = function
    | Term.FunApp
        ( (T_bv.BVDiv (size, signed) | T_bv.BVRem (size, signed)),
          [ f; Term.FunApp (T_bv.BVNum (_, n), [], _) ],
          _ )
      when not (T_bv.is_signed signed) ->
        let size = cmp_size ~size f in
        let delta = Z.erem n (Z.pow (Z.of_int 2) (T_bv.bits_of size)) in
        Z.Compare.(delta <> Z.zero) && Z.popcount delta <> 1
    | _ -> false

  let isolable_head = function
    | Term.FunApp
        ( ( T_bv.BVAnd _ | T_bv.BVOr _ | T_bv.BVCONCAT _ | T_bv.BVSEXT _
          | T_bv.BVZEXT _ ),
          _,
          _ )
    | Term.FunApp
        ( (T_bv.BVSHL _ | T_bv.BVLSHR _ | T_bv.BVASHR _),
          [ _; Term.FunApp (T_bv.BVNum _, [], _) ],
          _ ) ->
        true
    | _ -> false

  let isolate_of ~quotient tvar t =
    let rec addends = function
      | Term.FunApp (T_bv.BVAdd _, [ a; b ], _) -> addends a @ addends b
      | Term.FunApp (T_bv.BVNeg _, [ a ], _) ->
          List.map (addends a) ~f:(fun (s, u) -> (not s, u))
      | u -> [ (false, u) ]
    in
    match desub t with
    | Term.FunApp ((T_bv.BVAdd size | T_bv.BVNeg size), _, _) as t -> (
        let xs, rs =
          List.partition_tf (addends t) ~f:(fun (_, u) ->
              Set.mem (Term.fvs_of u) tvar)
        in
        match xs with
        | [ (neg, g) ]
          when (isolable_head g || (quotient && isolable_quotient g))
               && Option.is_none (affine_of tvar g) ->
            let r =
              List.fold rs ~init:(T_bv.mk_bvnum ~size Z.zero)
                ~f:(fun acc (s, u) ->
                  T_bv.mk_bvadd ~size acc
                    (if s then T_bv.mk_bvneg ~size u else u))
            in
            Some (size, neg, g, Evaluator.simplify_term r)
        | _ -> None)
    | _ -> None

  (* the x-side of a binary atom as an isolable sum, the other side x-free:
     (size, neg, g, r, t, x-side on the left?) *)
  let isolated_sides ~quotient tvar t1 t2 =
    let free t = not (Set.mem (Term.fvs_of t) tvar) in
    match isolate_of ~quotient tvar t1 with
    | Some (size, neg, g, r) when free t2 -> Some (size, neg, g, r, t2, true)
    | _ -> (
        match isolate_of ~quotient tvar t2 with
        | Some (size, neg, g, r) when free t1 -> Some (size, neg, g, r, t1, false)
        | _ -> None)

  (* isolating the x-operand of an equality or a disequality, exact (the
     inverse of the sum): g + r = t -> g = t - r, -g + r = t -> g = r - t.
     The output has g alone on its side, which is not a sum, so the row does
     not apply to it again. A quotient or remainder g is isolated in an
     equality only: in a disequality [udiv-const] would weaken the literal,
     and the fallback's substitution is preferred *)
  let isolate_eq tvar = function
    | Atom.App (Predicate.Psym ((T_bool.Eq | T_bool.Neq) as psym), [ t1; t2 ], info)
      -> (
        let quotient =
          match psym with T_bool.Eq -> true | _ -> false
        in
        match isolated_sides ~quotient tvar t1 t2 with
        | Some (size, neg, g, r, t, _) ->
            let t' =
              Evaluator.simplify_term
              @@ if neg then T_bv.mk_bvsub ~size r t else T_bv.mk_bvsub ~size t r
            in
            Some (Atom.mk_app ~info (Predicate.Psym psym) [ g; t' ])
        | None -> None)
    | _ -> None

  (* whether the bounds [add-interval] leaves on an isolated g reach a rule:
     a concat (also the one a shift by a numeral becomes) is taken by
     [cmp-concat] only with each part mentioning x being x or a slice of bare
     x; any other part (a slice of x + q) sends the chosen branch to the
     fallback, whose output the branch's then implies and is in general
     strictly stronger than the fallback applied to the input. A quotient's
     divisor is checked in [isolable_quotient]. Normalization 31 is exact and
     needs no such condition *)
  let bounds_consumed tvar g =
    let rec bare_parts = function
      | Term.Var _ -> true (* x itself, or an x-free variable *)
      | Term.FunApp (T_bv.BVEXTRACT _, [ Term.Var (v, _, _) ], _)
        when Ident.tvar_equal v tvar ->
          true
      | Term.FunApp (T_bv.BVCONCAT _, [ a; b ], _) -> bare_parts a && bare_parts b
      | u -> not (Set.mem (Term.fvs_of u) tvar)
    in
    match g with
    | Term.FunApp (T_bv.BVCONCAT _, _, _) -> bare_parts g
    | Term.FunApp
        ( (T_bv.BVSHL _ | T_bv.BVLSHR _ | T_bv.BVASHR _),
          [ u; Term.FunApp (T_bv.BVNum _, [], _) ],
          _ ) ->
        bare_parts u
    | _ -> true

  (* [add-interval] detection: an unsigned comparison +-g + r <| t with g as
     in [isolate_of], a quotient or remainder included (the bounds left on it
     reach [udiv-const] and [urem-const]), x occurring in another atom as
     well. Returns the
     forbidden interval [lo; hi) of g, read from the [cmp-interval] table with
     g in place of x (both bounds x-free terms) *)
  let add_interval_atom tvar atoms atom =
    match atom with
    | Atom.App (Predicate.Psym psym, [ t1; t2 ], _)
      when Set.exists (Set.remove atoms atom) ~f:(fun a ->
               Set.mem (Atom.fvs_of a) tvar) -> (
        let psym, t1, t2 =
          match psym with
          | T_bv.(BVGeq (_, Some false) | BVGt (_, Some false)) ->
              (Predicate.flip_psym psym, t2, t1)
          | _ -> (psym, t1, t2)
        in
        match psym with
        | T_bv.(BVLt (_, Some false) | BVLeq (_, Some false)) -> (
            match isolated_sides ~quotient:true tvar t1 t2 with
            | Some (size, neg, g, r, t, left) when bounds_consumed tvar g ->
                let nzs, r1, r2 = if left then ((1, 0), r, t) else ((0, 1), t, r) in
                cmp_rows ~size nzs psym r1 r2
                |> Option.map ~f:(fun iv ->
                       let lo, hi =
                         if neg then reflect_interval ~size iv else iv
                       in
                       (size, g, lo, hi, atom))
            | _ -> None)
        | _ -> None)
    | _ -> None

  (* [add-interval]: the literal holds iff g lies outside the cyclic interval
     [lo; hi). Its complement is chosen by the model: lo <u hi gives the two
     half-lines g <u lo or hi <=u g, of which the one M satisfies is kept with
     the guard lo <u hi; hi <u lo gives the one interval hi <=u g <u lo,
     exact under its guard; lo = hi leaves no forbidden value. Every output
     atom is x-free or compares g alone with an x-free term, and nothing is
     substituted *)
  let add_interval ~print model tvar ~size g lo hi atom atoms =
    print
    @@ lazy (sprintf "[mbp bv] add-interval x=%s" (Ident.name_of_tvar tvar));
    let two_w = Z.pow (Z.of_int 2) (T_bv.bits_of size) in
    let mval t = Z.erem (snd @@ T_bv.let_bv (model_value model t)) two_w in
    let ult a b = T_bv.mk_bvlt ~size ~signed:(Some false) a b in
    let ule a b = T_bv.mk_bvleq ~size ~signed:(Some false) a b in
    let mlo = mval lo and mhi = mval hi in
    let gamma =
      if Z.Compare.(mlo < mhi) then
        [ ult lo hi; (if Z.Compare.(mval g < mlo) then ult g lo else ule hi g) ]
      else if Z.Compare.(mhi < mlo) then [ ult hi lo; ule hi g; ult g lo ]
      else [ Atom.mk_app (Predicate.Psym T_bool.Eq) [ lo; hi ] ]
    in
    Set.union (Set.remove atoms atom)
      (Set.Poly.of_list
      @@ List.concat_map gamma ~f:(fun a -> Set.to_list (normalize_mbp model a)))

  (* [neq-card] detection: forbidden region size of one literal, x-free and M-free *)
  let card_of tvar ~size atom =
    let w = T_bv.bits_of size in
    let two_w = Z.pow (Z.of_int 2) w in
    let numeral t =
      match Evaluator.simplify_term t with
      | Term.FunApp (T_bv.BVNum (_, n), [], _) -> Some (Z.erem n two_w)
      | _ -> None
    in
    (* smallest multiple of 2^e that is at least len *)
    let rounded e len =
      let p = Z.pow (Z.of_int 2) e in
      Z.mul p (Z.cdiv len p)
    in
    let pow2 e = Z.pow (Z.of_int 2) e in
    match atom with
    | Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _) ->
        (* affine: 2^e values, a single point when e = 0 *)
        let by_affine () =
          match (affine_of tvar t1, affine_of tvar t2) with
          | Some cr1, Some cr2 -> (
              match transpose ~size cr1 cr2 with
              | Some (coeff, rest) ->
                  let e = Z.trailing_zeros coeff in
                  let point =
                    if e = 0 then
                      Some
                        (normalize_term @@ Evaluator.simplify_term
                        @@ T_bv.mk_bvmul ~size
                             (T_bv.mk_bvnum ~size (Z.invert coeff two_w))
                             (T_bv.mk_bvneg ~size rest))
                    else None
                  in
                  Some (pow2 e, point)
              | None -> None)
          | _ -> None
        in
        (* mask form: 2^(w - popcount (m land lnot c)) values *)
        let by_mask () =
          let is_xfree u = not (Set.mem (Term.fvs_of u) tvar) in
          let try_side u other =
            match mask_of tvar u with
            | Some (_, m, c) when is_xfree other -> (
                match (numeral m, numeral c) with
                | Some m, Some c ->
                    Some (pow2 (w - Z.popcount (Z.logand m (Z.lognot c))), None)
                | _ -> None)
            | _ -> None
          in
          match try_side t1 t2 with Some r -> Some r | None -> try_side t2 t1
        in
        (match by_affine () with Some r -> Some r | None -> by_mask ())
    | Atom.App (Predicate.Psym psym, [ t1; t2 ], _) -> (
        let psym, t1, t2 =
          match psym with
          | T_bv.(BVGeq (_, Some false) | BVGt (_, Some false)) ->
              (Predicate.flip_psym psym, t2, t1)
          | _ -> (psym, t1, t2)
        in
        match (affine_of tvar t1, affine_of tvar t2) with
        | Some (c1, r1), Some (c2, r2) -> (
            let nz c = if Z.Compare.(Z.erem c two_w = Z.zero) then 0 else 1 in
            let coeff = Z.erem (if nz c1 = 1 then c1 else c2) two_w in
            match (numeral r1, numeral r2) with
            | Some _, Some _ when nz c1 + nz c2 = 1 -> (
                match cmp_rows ~size (nz c1, nz c2) psym r1 r2 with
                | Some (lo, hi) -> (
                    match (numeral lo, numeral hi) with
                    | Some lo, Some hi ->
                        let len = Z.erem (Z.sub hi lo) two_w in
                        let len = if Z.Compare.(len = Z.zero) then two_w else len in
                        Some (rounded (Z.trailing_zeros coeff) len, None)
                    | _ -> None)
                | None -> None)
            | _ -> None)
        | _ -> None)
    | _ -> None

  (* None: the rule declines. Some None: n < |D|. Some (Some ps): x <> p for each p *)
  let neq_card_atoms tvar atoms =
    match sort_of_tvar tvar atoms with
    | None -> None
    | Some size -> (
        let cards =
          Set.to_list atoms
          |> List.filter ~f:(fun a -> Set.mem (Atom.fvs_of a) tvar)
          |> List.map ~f:(card_of tvar ~size)
        in
        if List.exists cards ~f:Option.is_none then None
        else
          let cards = List.filter_opt cards in
          let n = List.fold cards ~init:Z.zero ~f:(fun acc (nl, _) -> Z.add acc nl) in
          if Z.Compare.(n < Z.pow (Z.of_int 2) (T_bv.bits_of size)) then Some None
          else
            let points = List.map cards ~f:snd in
            if List.for_all points ~f:Option.is_some then
              Some (Some (List.filter_opt points))
            else None)

  (* [FinDom.group_by_value] on bit-vector numerals, skipping [Evaluator.eval_term] *)
  let group_by_model_value model ps =
    let mval t = snd @@ T_bv.let_bv (model_value model t) in
    List.fold ps ~init:[] ~f:(fun classes t ->
        let v = mval t in
        let rec add = function
          | [] -> [ (v, [ t ]) ]
          | (v', ts) :: rest ->
              if Z.Compare.(v = v') then (v', t :: ts) :: rest
              else (v', ts) :: add rest
        in
        add classes)
    |> List.map ~f:snd

  let neq_card ~print model tvar points atoms =
    let others =
      Set.filter atoms ~f:(fun a -> not (Set.mem (Atom.fvs_of a) tvar))
    in
    match points with
    | None ->
        print
        @@ lazy (sprintf "[mbp bv] neq-card top x=%s" (Ident.name_of_tvar tvar));
        others
    | Some ps ->
        print
        @@ lazy
             (sprintf "[mbp bv] neq-card class-eq x=%s" (Ident.name_of_tvar tvar));
        group_by_model_value model ps
        |> List.concat_map ~f:(function
             | rep :: rest -> List.map rest ~f:(T_bool.mk_eq rep)
             | [] -> [])
        |> Set.Poly.of_list
        |> Set.concat_map ~f:(normalize_mbp model)
        |> Set.union others

  (* The shape of [atom] as [tvar] sees it, for the trace only: a maximal subterm free of
     [tvar] prints as [c] when it is ground and as [_] otherwise, so the atoms that left a
     variable to the fallback can be tallied by shape across calls and inputs. *)
  let shape_of tvar atom =
    let rec term t =
      if not (Set.mem (Term.fvs_of t) tvar) then
        if Set.is_empty (Term.fvs_of t) then "c" else "_"
      else
        match t with
        | Term.Var _ -> "x"
        | Term.FunApp (sym, args, _) ->
            sprintf "%s(%s)"
              (try Term.str_of_funsym sym with Failure _ -> "?")
              (String.concat ~sep:"," (List.map args ~f:term))
        | _ -> Term.str_of t
    in
    match atom with
    | Atom.App (Predicate.Psym psym, args, _) ->
        sprintf "%s(%s)"
          (try Predicate.str_of_psym psym with Failure _ -> "?")
          (String.concat ~sep:"," (List.map args ~f:term))
    | _ -> Atom.str_of atom

  (* the width of [tvar] as its model value gives it; [None] when the model does not bind it *)
  let width_in_model model tvar =
    match Map.Poly.find model tvar with
    | Some v -> (
        match Term.sort_of v with
        | T_bv.SBV size -> Some (T_bv.bits_of size)
        | _ -> None)
    | None -> None

  (* A census for the record, not a rule: the slices of a concat that the concat-slicing
     normalization reduces to one part of the concat (the slice lies inside the low part
     or inside the high part), counted on the atoms at the entry of every projection step, as
     the first normalization round meets them (after [dederived], [desub] and
     [fold_ext0]), and only where the concat mentions a variable still to be projected
     ([tvars]; a rule that substitutes a concat of new variables for x makes the slices of
     x slices of that concat).  Each such slice is classed by where it sits: [op] inside a maximal
     arithmetic term (sum, product, negation, difference) whose parent is an operator
     rather than the atom, [top] inside a maximal arithmetic term that is a side of the
     atom, [none] not inside an arithmetic term.  A slice inside a slice is classed as a
     child of an operator.  Slices that the later normalizations of a round (a shift
     rewritten as a concat) produce are not seen, so the counts are lower bounds. *)
  let slice_census tvars atoms =
    let op = ref 0 and top = ref 0 and none = ref 0 in
    let is_arith = function
      | T_bv.(BVAdd _ | BVMul _ | BVNeg _ | BVSub _) -> true
      | _ -> false
    in
    (* [ctx]: [`None] outside arithmetic; otherwise whether the enclosing maximal
       arithmetic term is a side of the atom ([`Top]) or the child of an operator ([`Op]) *)
    let rec walk ~at_side ~ctx t =
      match t with
      | Term.FunApp (fsym, args, _) when is_arith fsym ->
          let ctx =
            match ctx with
            | `None -> if at_side then `Top else `Op
            | c -> c
          in
          List.iter args ~f:(walk ~at_side:false ~ctx)
      | Term.FunApp (T_bv.BVEXTRACT (_, h, l), [ t1 ], _) ->
          (match fold_extract t1 with
          | Term.FunApp (T_bv.BVCONCAT (_, size2), [ _; _ ], _) as c
            when List.exists tvars ~f:(Set.mem (Term.fvs_of c)) ->
              let w2 = T_bv.bits_of size2 in
              if h < w2 || l >= w2 then
                incr (match ctx with `Op -> op | `Top -> top | `None -> none)
          | _ -> ());
          walk ~at_side:false ~ctx:`None t1
      | Term.FunApp (_, args, _) ->
          List.iter args ~f:(walk ~at_side:false ~ctx:`None)
      | _ -> ()
    in
    Set.iter atoms ~f:(function
      | Atom.App (_, args, _) ->
          List.iter args ~f:(fun t ->
              walk ~at_side:true ~ctx:`None
                (List.fold [ dederived; desub; fold_ext0 ] ~init:t ~f:(fun t f ->
                     f t)))
      | _ -> ());
    (!op, !top, !none)

  (* What one projection call took from the model, for the trace and the per-call record of
     [model_based_projection] only: [bits] is the sum of the widths of the variables the
     fallback replaced by their model values, [fallbacks] the number of those replacements;
     [slices] sums [slice_census] over the steps, and is filled only when [census] is set. *)
  type tally = {
    mutable bits : int;
    mutable fallbacks : int;
    census : bool;
    mutable slices : int * int * int;
  }

  let fallback ~print ~(filled : tally) model tvar atoms =
    let w = width_in_model model tvar in
    filled.bits <- filled.bits + Option.value w ~default:0;
    filled.fallbacks <- filled.fallbacks + 1;
    print
    @@ lazy
         (sprintf "[mbp bv] fallback x=%s w=%s shapes=[%s]"
            (Ident.name_of_tvar tvar)
            (Option.value_map w ~default:"?" ~f:string_of_int)
            (Set.to_list atoms
            |> List.filter ~f:(fun a -> Set.mem (Atom.fvs_of a) tvar)
            |> List.map ~f:(shape_of tvar)
            |> List.dedup_and_sort ~compare:String.compare
            |> String.concat ~sep:"; "));
    match Map.Poly.find model tvar with
    | Some value ->
        let sub = Map.Poly.singleton tvar value in
        Set.concat_map atoms ~f:(Atom.subst sub >> normalize_mbp model)
    | None ->
        failwith
        @@ sprintf
             "[mbp bv] the model does not bind %s: model-based projection \
              requires a model of its input"
             (Ident.name_of_tvar tvar)

  (* the same extension off both sides: ext_k u ~ ext_k v -> u ~' v *)
  let drop_same_extend = function
    | Atom.App (Predicate.Psym psym, [ t1; t2 ], info) -> (
        let ext_of = function
          | Term.FunApp (T_bv.BVSEXT (size, k), [ u ], _) -> Some (true, size, k, u)
          | Term.FunApp (T_bv.BVZEXT (size, k), [ u ], _) -> Some (false, size, k, u)
          | _ -> None
        in
        match (ext_of t1, ext_of t2) with
        (* an extension of no bits is left to the trivial-extension normalization *)
        | Some (s1, sz1, k1, u), Some (s2, sz2, k2, v)
          when Bool.equal s1 s2 && k1 = k2 && k1 >= 1
               && Stdlib.(cmp_size ~size:sz1 u = cmp_size ~size:sz2 v) ->
            let sz = cmp_size ~size:sz1 u in
            let psym' =
              match psym with
              | T_bv.(BVLeq (_, signed)) ->
                  T_bv.BVLeq (sz, if s1 then signed else Some false)
              | T_bv.(BVLt (_, signed)) ->
                  T_bv.BVLt (sz, if s1 then signed else Some false)
              | T_bv.(BVGeq (_, signed)) ->
                  T_bv.BVGeq (sz, if s1 then signed else Some false)
              | T_bv.(BVGt (_, signed)) ->
                  T_bv.BVGt (sz, if s1 then signed else Some false)
              | p -> p
            in
            Some (Atom.mk_app ~info (Predicate.Psym psym') [ u; v ])
        | _ -> None)
    | _ -> None

  let rec model_based_projection_aux ?(reuse_unchanged = false) ?known ~print
      ~filled model tvars atoms =
    (if filled.census then
       let o, t, n = slice_census tvars atoms and o', t', n' = filled.slices in
       filled.slices <- (o + o', t + t', n + n'));
    let final = List.is_empty tvars in
    let atoms =
      (* [bv-post] is the same pass on what a rule returned, once no target is left *)
      Common.PhaseTime.with_phase
        (if List.is_empty tvars then "bv-post" else "bv-pre")
      @@ fun () ->
      let atoms0 = normalize_atoms_known ?tvar:(List.hd tvars) ~known model atoms in
      let atoms = atoms0 in
      (* the same extension on both sides *)
      let atoms =
        Common.PhaseTime.with_phase "drop-ext" @@ fun () ->
        Set.concat_map atoms ~f:(fun atom ->
            match drop_same_extend atom with
            | Some atom' -> normalize_mbp model atom'
            | None -> Set.Poly.singleton atom)
      in
      (* a bound on the same side that a tighter one subsumes, compared as a threshold;
         a numeral is read modulo 2^w for the width w of its comparison, which is the width
         of the other side and may exceed the target's (x o b, an extension of x) *)
      let atoms =
        Common.PhaseTime.with_phase "bound" @@ fun () ->
        match tvars with
        | tvar :: _ ->
            let numeral size t =
              match t with
              | Term.FunApp (T_bv.BVNum (_, n), [], _) ->
                  Some (Z.erem n (Z.pow (Z.of_int 2) (T_bv.bits_of size)))
              | _ -> None
            in
            (* (other side, upper bound?, threshold) *)
            let bound atom =
              match atom with
              | Atom.App (Predicate.Psym psym, [ t1; t2 ], _)
                when Set.mem (Atom.fvs_of atom) tvar -> (
                  let dir strict side size =
                    match side with
                    | `Le -> Some (true, strict, size)
                    | `Ge -> Some (false, strict, size)
                  in
                  let side =
                    match psym with
                    | T_bv.BVLt (size, Some false) -> dir true `Le size
                    | T_bv.BVLeq (size, Some false) -> dir false `Le size
                    | T_bv.BVGt (size, Some false) -> dir true `Ge size
                    | T_bv.BVGeq (size, Some false) -> dir false `Ge size
                    | _ -> None
                  in
                  (* u <u c is B = c-1, u <=u c is B = c, c <u u is A = c+1, c <=u u is A = c *)
                  let thr upper strict c =
                    if upper then if strict then Z.sub c Z.one else c
                    else if strict then Z.add c Z.one
                    else c
                  in
                  match side with
                  | None -> None
                  | Some (upper, strict, size) -> (
                      match (numeral size t1, numeral size t2) with
                      | None, Some c -> Some (t1, upper, thr upper strict c)
                      | Some c, None ->
                          let upper = not upper in
                          Some (t2, upper, thr upper strict c)
                      | _ -> None))
              | _ -> None
            in
            let keeps =
              Set.fold atoms ~init:[] ~f:(fun acc atom ->
                  match bound atom with
                  | None -> acc
                  | Some (u, upper, b) ->
                      let key = (u, upper) in
                      let tighter b b' =
                        if upper then Z.Compare.(b < b') else Z.Compare.(b > b')
                      in
                      if
                        List.exists acc ~f:(fun (k, b') ->
                            Stdlib.(k = key) && tighter b' b)
                      then acc
                      else
                        (key, b)
                        :: List.filter acc ~f:(fun (k, _) -> not Stdlib.(k = key)))
            in
            Set.filter atoms ~f:(fun atom ->
                match bound atom with
                | None -> true
                | Some (u, upper, b) ->
                    List.for_all keeps ~f:(fun (k, b') ->
                        (not Stdlib.(k = (u, upper))) || Z.Compare.(b = b')))
        | [] -> atoms
      in
      (* a bitwise operation over one concatenation, the other side free of the target *)
      let atoms =
        Common.PhaseTime.with_phase "distrib1" @@ fun () ->
        match tvars with
        | tvar :: _ ->
            Set.concat_map atoms ~f:(fun atom ->
                match atom with
                | Atom.App (pred, args, info) ->
                    let args' =
                      List.map args
                        ~f:(normalize_term ~only:[ fold_distrib1 tvar ])
                    in
                    (* [normalize_term] returns its argument itself when no fold
                       applies, and the atoms here have just been through
                       [normalize_mbp]; normalizing an unchanged atom again was most
                       of this step's time on large terms and returned the atom
                       itself on every atom observed (normalization is not proved
                       idempotent, but leaving an atom as it is rewrites nothing) *)
                    if List.for_all2_exn args args' ~f:phys_equal then
                      Set.Poly.singleton atom
                    else normalize_mbp model (Atom.mk_app ~info pred args')
                | atom -> Set.Poly.singleton atom)
        | [] -> atoms
      in
      (* the slice reading of a left shift, on the slice layer and for comparisons only *)
      let atoms =
        Common.PhaseTime.with_phase "shl-slice" @@ fun () ->
        match tvars with
        | tvar :: _ ->
            Set.concat_map atoms ~f:(function
              | Atom.App
                  ( (Predicate.Psym T_bv.(BVLeq _ | BVLt _ | BVGeq _ | BVGt _) as
                     pred),
                    args,
                    info ) as atom
                when not (arith_layer tvar atom) ->
                  let args' =
                    List.map args ~f:(normalize_term ~only:[ fold_shl_slice ])
                  in
                  (* as for the distribution step above, an atom the slice reading
                     left unchanged is kept as it is; here only with
                     [reuse_unchanged], since the renormalization's identity on
                     these atoms is observed, not proved *)
                  if reuse_unchanged && List.for_all2_exn args args' ~f:phys_equal
                  then Set.Poly.singleton atom
                  else normalize_mbp model (Atom.mk_app ~info pred args')
              | atom -> Set.Poly.singleton atom)
        | _ -> atoms
      in
      (* what the last step returns as its normalization left it is known to be
         normal for the later steps of the same projection *)
      (match known with
      | Some known when final ->
          let normalized = PhysAtoms.create (Set.length atoms0) in
          Set.iter atoms0 ~f:(fun a -> PhysAtoms.replace normalized a ());
          Set.iter atoms ~f:(fun a ->
              if PhysAtoms.mem normalized a then PhysAtoms.replace known a ())
      | _ -> ());
      atoms
    in
    (* the x-operand of an equality or a disequality isolated from a sum *)
    let atoms =
      match tvars with
      | tvar :: _ ->
          Set.concat_map atoms ~f:(fun atom ->
              match isolate_eq tvar atom with
              | Some atom' -> normalize_mbp model atom'
              | None -> Set.Poly.singleton atom)
      | [] -> atoms
    in
    match tvars with
    | [] -> atoms
    | tvar :: rest ->
        if not (Set.exists atoms ~f:(fun a -> Set.mem (Atom.fvs_of a) tvar))
        then
          model_based_projection_aux ~reuse_unchanged ?known ~print ~filled model
            rest
            atoms
        else
          (* The first rule that applies is used, so the order matters: an
             equality is handled exactly and goes before comparisons; the mask
             rules go after the affine equality rules (they destroy affine form)
             and before extraction (which leaves a concat, not a mask); the
             signed division/remainder rules discharge the sign before the
             unsigned ones; division goes before the interval rule, whose affine
             extraction fails while a division remains; the fallback is last.
             Each rule carries the name of its phase: a phase is charged the
             rule's search for an atom it applies to, and its application when
             it applies (counted as the phase's [fired] event).  The phases only
             observe: the rules run as without them.  The name sits beside its
             rule so that adding a rule cannot leave a separate list of names
             one short. *)
          let rules =
            [
              ( "bv-eq-odd",
                fun () ->
                Set.find_map atoms ~f:(eq_odd_atom tvar)
                |> Option.map ~f:(fun (size, coeff, r, atom) ->
                    ( model,
                      rest,
                      eq_odd ~print model tvar ~size ~coeff ~rest:r atom atoms
                    )));
              ( "bv-eq-even",
                fun () ->
                eq_even_atom tvar atoms
                |> Option.map ~f:(fun (_, size, coeff, r, atom) ->
                    let model', y_h, atoms' =
                      eq_even ~print model tvar ~size ~coeff ~rest:r atom atoms
                    in
                    (model', y_h :: rest, atoms')));
              ( "bv-eq-mask",
                fun () ->
                let lits =
                  if Lazy.force eq_mask_joint_enabled then
                    Set.to_list atoms |> List.filter_map ~f:(eq_mask_atom tvar)
                  else
                    Option.to_list @@ Set.find_map atoms ~f:(eq_mask_atom tvar)
                in
                match lits with
                | [] -> None
                | [ (size, m, c, t, atom) ] ->
                    let model', z, atoms' =
                      eq_mask ~print model tvar ~size m c t atom atoms
                    in
                    Some (model', z :: rest, atoms')
                | (size, _, _, _, _) :: _ ->
                    let model', z, atoms' =
                      eq_mask_joint ~print model tvar ~size lits atoms
                    in
                    Some (model', z :: rest, atoms'));
              ( "bv-neq-mask",
                fun () ->
                Set.find_map atoms ~f:(neq_mask_atom tvar atoms)
                |> Option.map ~f:(fun (size, m, c, t, atom) ->
                    ( model,
                      tvar :: rest,
                      neq_mask ~print model tvar ~size m c t atom atoms )));
              ( "bv-cmp-mask",
                fun () ->
                Set.find_map atoms ~f:(cmp_mask_atom tvar atoms)
                |> Option.map ~f:(fun (psym, size, m, c, t, atom) ->
                    ( model,
                      tvar :: rest,
                      cmp_mask ~print model tvar psym ~size m c t atom atoms )));
              ( "bv-bitwise-both",
                fun () ->
                bitwise_both_atom tvar atoms
                |> Option.map ~f:(fun (xatoms, parts) ->
                    ( model,
                      rest,
                      bitwise_both ~print model tvar xatoms parts atoms )));
              ( "bv-sign-split",
                fun () ->
                Set.find_map atoms ~f:(sign_split_atom tvar)
                |> Option.bind ~f:(fun (size, is_div, s, t, atom) ->
                       sign_split ~print model tvar ~size ~is_div s t atom atoms
                       |> Option.map ~f:(fun atoms' -> (model, tvar :: rest, atoms'))));
              ( "bv-udiv-const",
                fun () ->
                Set.find_map atoms ~f:(udiv_const_atom tvar atoms)
                |> Option.bind ~f:(fun (psym, size, f, delta, d, atom) ->
                       udiv_const ~print model tvar psym ~size f delta d atom atoms
                       |> Option.map ~f:(fun atoms' -> (model, tvar :: rest, atoms'))));
              ( "bv-urem-const",
                fun () ->
                Set.find_map atoms ~f:(urem_const_atom tvar)
                |> Option.bind ~f:(fun (size, f, delta, atom) ->
                       urem_const ~print model tvar ~size f delta atom atoms
                       |> Option.map ~f:(fun atoms' -> (model, tvar :: rest, atoms'))));
              ( "bv-extract",
                fun () ->
                extract_atom tvar atoms
                |> Option.map ~f:(fun (size, cuts) ->
                    let model', ys, atoms' =
                      extract ~print model tvar ~size cuts atoms
                    in
                    (model', ys @ rest, atoms')));
              ( "bv-extend",
                fun () ->
                Set.find_map atoms ~f:(extend_atom tvar)
                |> Option.bind ~f:(fun (psym, se, size, k, u, t, atom) ->
                       extend ~print model tvar psym ~signed_ext:se ~size k u t
                         atom atoms
                       |> Option.map ~f:(fun atoms' -> (model, tvar :: rest, atoms'))));
              ( "bv-expand-extend",
                fun () ->
                (* the expansion of an extension, once every rule above declined *)
                let atoms' =
                  Set.concat_map atoms ~f:(fun atom ->
                      let slice_layer = not (arith_layer tvar atom) in
                      match atom with
                      | Atom.App (pred, args, info) ->
                          normalize_mbp model
                            (Atom.mk_app ~info pred
                               (List.map args
                                   ~f:(normalize_term
                                         ~only:[ expand_extend ~slice_layer tvar ])))
                      | atom -> Set.Poly.singleton atom)
                in
                if Set.equal atoms atoms' then None
                else (
                  print
                  @@ lazy
                       (sprintf "[mbp bv] expand-extend x=%s"
                          (Ident.name_of_tvar tvar));
                  Some (model, tvar :: rest, atoms')));
              ( "bv-eq-concat",
                fun () ->
                Set.find_map atoms ~f:(eq_concat_atom tvar)
                |> Option.map ~f:(fun (size1, size2, uh, ul, t, atom) ->
                    ( model,
                      tvar :: rest,
                      eq_concat ~print model tvar ~size1 ~size2 uh ul t atom
                        atoms )));
              ( "bv-neq-concat",
                fun () ->
                Set.find_map atoms ~f:(neq_concat_atom tvar)
                |> Option.map ~f:(fun (size1, size2, uh, ul, t, atom) ->
                    ( model,
                      tvar :: rest,
                      neq_concat ~print model tvar ~size1 ~size2 uh ul t atom
                        atoms )));
              ( "bv-cmp-concat",
                fun () ->
                Set.find_map atoms ~f:(cmp_concat_atom tvar)
                |> Option.map ~f:(fun (psym, size1, size2, uh, ul, t, atom) ->
                    ( model,
                      tvar :: rest,
                      cmp_concat ~print model tvar psym ~size1 ~size2 uh ul t
                        atom atoms )));
              ( "bv-offset",
                fun () ->
                offset_atom tvar atoms
                |> Option.map ~f:(fun (size, q) ->
                    let model', y, atoms' =
                      offset ~print model tvar ~size q atoms
                    in
                    (model', y :: rest, atoms')));
              ( "bv-mask-carry",
                fun () ->
                mask_carry_atom tvar atoms
                |> Option.bind ~f:(fun (size, w, atom, q, m, left) ->
                       mask_carry ~print model tvar ~size ~w q m atom left atoms
                       |> Option.map ~f:(fun atoms' -> (model, tvar :: rest, atoms'))));
              ( "bv-signed-cmp",
                fun () ->
                Set.find_map atoms ~f:(signed_cmp_atom tvar)
                |> Option.map ~f:(fun (atom, atom') ->
                    ( model,
                      tvar :: rest,
                      signed_cmp ~print model tvar atom atom' atoms )));
              ( "bv-add-interval",
                fun () ->
                Set.find_map atoms ~f:(add_interval_atom tvar atoms)
                |> Option.map ~f:(fun (size, g, lo, hi, atom) ->
                    ( model,
                      tvar :: rest,
                      add_interval ~print model tvar ~size g lo hi atom atoms
                    )));
              ( "bv-cmp-interval",
                fun () ->
                cmp_interval_atoms tvar atoms
                |> Option.map ~f:(fun (size, ivs) ->
                       (model, rest, cmp_interval ~print model tvar ~size ivs atoms)));
              ( "bv-neq-card",
                fun () ->
                neq_card_atoms tvar atoms
                |> Option.map ~f:(fun points ->
                       (model, rest, neq_card ~print model tvar points atoms)));
            ]
          in
          let model', tvars', atoms' =
            match
              List.find_map (rules)
                ~f:(fun (name, rule) ->
                  Common.PhaseTime.with_phase name (fun () ->
                      let r = rule () in
                      if Option.is_some r then
                        Common.PhaseTime.event_here ~in_copy:false "fired";
                      r))
            with
            | Some r -> r
            | None ->
                ( model,
                  rest,
                  Common.PhaseTime.with_phase "bv-fallback" (fun () ->
                      fallback ~print ~filled model tvar atoms) )
          in
          model_based_projection_aux ~reuse_unchanged ?known ~print ~filled model'
            tvars' atoms'

  (* A digest of a conjunction's printed atoms, sorted, for the trace only: two calls on the
     same conjunction and the same variable print the same [in=] key, so the distinct
     projections a fixed input receives across calls can be counted. *)
  let digest_of_atoms atoms =
    Set.to_list atoms |> List.map ~f:Atom.str_of
    |> List.sort ~compare:String.compare
    |> String.concat ~sep:" /\\ "
    |> Stdlib.Digest.string |> Stdlib.Digest.to_hex |> fun h -> String.prefix h 12

  (* A digest of [model] restricted to [vars], for the trace only *)
  let digest_of_model model vars =
    Set.to_list vars
    |> List.map ~f:(fun v ->
           sprintf "%s=%s" (Ident.name_of_tvar v)
             (Option.value_map (Map.Poly.find model v) ~default:"?" ~f:Term.str_of))
    |> List.sort ~compare:String.compare
    |> String.concat ~sep:","
    |> Stdlib.Digest.string |> Stdlib.Digest.to_hex |> fun h -> String.prefix h 12

  (* The size of a conjunction as a DAG and as a tree, for the per-call record only.  A node
     is a variable, a numeral, an application of a function symbol, or an atom; numerals
     and variables count one node each, and two occurrences are one DAG node when they
     print the same symbol at the same sort over the same DAG children.  The atoms of the
     set are distinct, so the conjunction itself adds no node. *)
  let dag_and_tree_size atoms =
    let ids = Hashtbl.create (module String) in
    let id_of key =
      match Hashtbl.find ids key with
      | Some id -> id
      | None ->
          let id = Hashtbl.length ids in
          Hashtbl.set ids ~key ~data:id;
          id
    in
    let tree = ref 0 in
    let key_of head children =
      head ^ "(" ^ String.concat ~sep:"," (List.map children ~f:string_of_int) ^ ")"
    in
    let rec term t =
      incr tree;
      match t with
      | Term.Var (v, s, _) ->
          id_of (key_of ("v:" ^ Ident.name_of_tvar v ^ ":" ^ Term.str_of_sort s) [])
      | Term.FunApp (sym, args, _) ->
          let children = List.map args ~f:term in
          id_of
            (key_of
               ("f:" ^ Term.str_of_funsym sym ^ ":" ^ Term.str_of_sort (Term.sort_of t))
               children)
      | Term.LetTerm (v, s, def, body, _) ->
          let children = [ term def; term body ] in
          id_of
            (key_of ("l:" ^ Ident.name_of_tvar v ^ ":" ^ Term.str_of_sort s) children)
    in
    Set.iter atoms ~f:(fun atom ->
        incr tree;
        match atom with
        | Atom.App (Predicate.Psym psym, args, _) ->
            let children = List.map args ~f:term in
            ignore
              (id_of
                 (key_of
                    ("p:" ^ Predicate.str_of_psym psym ^ ":"
                    ^ String.concat ~sep:","
                        (List.map args ~f:(Term.sort_of >> Term.str_of_sort)))
                    children)
                : int)
        | atom -> ignore (id_of ("a:" ^ Atom.str_of atom) : int));
    (Hashtbl.length ids, !tree)

  (* The per-call record: off unless the environment variable COAR_MBP_BV_STATS names a
     file, to which every call appends one line of space-separated key=value fields --
     the process, the variable and its width, digests of the input and the output (as on
     the trace), their atom counts and DAG and tree sizes, [g] (bits copied from the model
     by the fallback), [fb] (number of fallback substitutions) and [us] (wall-clock
     microseconds of the projection proper, before any of these sizes is computed),
     [rules] (the rules that fired, in order, as the trace names them) and [slice_op],
     [slice_top], [slice_none] (the census of the slices of a concat, summed over the
     steps).  Each
     line is one append-mode write, short enough that calls from parallel domains or
     processes do not interleave within a line. *)
  let stats_file = lazy (Sys.getenv "COAR_MBP_BV_STATS")

  let write_stats ~x ~w ~(filled : tally) ~usec ~rules atoms atoms' path =
    let dag_in, tree_in = dag_and_tree_size atoms in
    let slice_op, slice_top, slice_none = filled.slices in
    let dag_out, tree_out = dag_and_tree_size atoms' in
    let line =
      sprintf
        "pid=%d x=%s w=%s in=%s out=%s atoms_in=%d atoms_out=%d dag_in=%d dag_out=%d \
         tree_in=%d tree_out=%d g=%d fb=%d us=%d rules=%s slice_op=%d slice_top=%d \
         slice_none=%d\n"
        (Core_unix.getpid () |> Pid.to_int)
        x w (digest_of_atoms atoms) (digest_of_atoms atoms') (Set.length atoms)
        (Set.length atoms') dag_in dag_out tree_in tree_out filled.bits
        filled.fallbacks usec
        (if List.is_empty rules then "-" else String.concat ~sep:"," rules)
        slice_op slice_top slice_none
    in
    Out_channel.with_file path ~append:true ~f:(fun oc ->
        Out_channel.output_string oc line)

  (* The per-call dump: off unless the environment variable COAR_MBP_BV_DUMP names an
     existing directory, into which every call whose (variable, input) pair this process
     has not dumped yet writes one SMT-LIB 2 script, [<pid>_<n>.smt2].  The script
     declares the free variables, asserts the model's value of each, checks satisfiability
     and asks Z3's debugging command [(mbp <formula> (<x>))] -- the projection Spacer
     calls -- for the same input and model, so the two projections of one call can be
     compared offline.  The output of this projection is the comment line [; coar-out:]
     and the [define-fun coar_out]; the header comment repeats the per-call record's
     fields.  A call whose atoms use a symbol outside the bit-vector, Boolean and
     equality fragment printed here, or a variable name containing '|', is not dumped. *)
  let dump_dir = lazy (Sys.getenv "COAR_MBP_BV_DUMP")
  let dumped = Hashtbl.create (module String)
  let dump_count = ref 0

  (* calls may run in parallel domains: the table and the counter are read and written
     under this lock only *)
  let dump_lock = Stdlib.Mutex.create ()

  exception Unprintable

  let smt_symbol name =
    if String.mem name '|' then raise Unprintable
    else if
      (not (String.is_empty name))
      && (not (Char.is_digit name.[0]))
      && String.for_all name ~f:(fun c ->
             Char.is_alphanum c || String.mem "~!@$%^&*_-+=<>.?/" c)
    then name
    else "|" ^ name ^ "|"

  let smt_sort = function
    | T_bv.SBV size -> sprintf "(_ BitVec %d)" (T_bv.bits_of size)
    | T_bool.SBool -> "Bool"
    | _ -> raise Unprintable

  let rec smt_term = function
    | Term.Var (v, _, _) -> smt_symbol (Ident.name_of_tvar v)
    | Term.FunApp (T_bv.BVNum (size, n), [], _) ->
        let w = T_bv.bits_of size in
        let n = Z.erem n (Z.shift_left Z.one w) in
        sprintf "#b%s"
          (String.init w ~f:(fun i ->
               if Z.testbit n (w - 1 - i) then '1' else '0'))
    | Term.FunApp (T_bool.IfThenElse, [ c; a; b ], _) ->
        sprintf "(ite %s %s %s)" (smt_bool_term c) (smt_term a) (smt_term b)
    | Term.FunApp (T_bool.Formula _, [], _) as t -> smt_bool_term t
    | Term.FunApp (sym, args, _) ->
        let op =
          match sym with
          | T_bv.BVNot _ -> "bvnot"
          | T_bv.BVAnd _ -> "bvand"
          | T_bv.BVOr _ -> "bvor"
          | T_bv.BVXor _ -> "bvxor"
          | T_bv.BVNand _ -> "bvnand"
          | T_bv.BVNor _ -> "bvnor"
          | T_bv.BVXnor _ -> "bvxnor"
          | T_bv.BVNeg _ -> "bvneg"
          | T_bv.BVAdd _ -> "bvadd"
          | T_bv.BVSub _ -> "bvsub"
          | T_bv.BVMul _ -> "bvmul"
          | T_bv.BVDiv (_, s) -> if T_bv.is_signed s then "bvsdiv" else "bvudiv"
          | T_bv.BVRem (_, s) -> if T_bv.is_signed s then "bvsrem" else "bvurem"
          | T_bv.BVSMod _ -> "bvsmod"
          | T_bv.BVSHL _ -> "bvshl"
          | T_bv.BVLSHR _ -> "bvlshr"
          | T_bv.BVASHR _ -> "bvashr"
          | T_bv.BVEXTRACT (_, h, l) -> sprintf "(_ extract %d %d)" h l
          | T_bv.BVSEXT (_, e) -> sprintf "(_ sign_extend %d)" e
          | T_bv.BVZEXT (_, e) -> sprintf "(_ zero_extend %d)" e
          | T_bv.BVCONCAT _ -> "concat"
          | _ -> raise Unprintable
        in
        sprintf "(%s %s)" op (String.concat ~sep:" " (List.map args ~f:smt_term))
    | _ -> raise Unprintable

  and smt_bool_term = function
    | Term.FunApp (T_bool.Formula (Formula.Atom (atom, _)), [], _) -> smt_atom atom
    | Term.Var _ as t -> smt_term t
    | _ -> raise Unprintable

  and smt_atom = function
    | Atom.True _ -> "true"
    | Atom.False _ -> "false"
    | Atom.App (Predicate.Psym sym, args, _) ->
        let app op =
          sprintf "(%s %s)" op (String.concat ~sep:" " (List.map args ~f:smt_term))
        in
        let cmp s ~signed ~unsigned =
          app (if T_bv.is_signed s then signed else unsigned)
        in
        (match sym with
        | T_bool.Eq -> app "="
        | T_bool.Neq -> sprintf "(not %s)" (app "=")
        | T_bv.BVLeq (_, s) -> cmp s ~signed:"bvsle" ~unsigned:"bvule"
        | T_bv.BVGeq (_, s) -> cmp s ~signed:"bvsge" ~unsigned:"bvuge"
        | T_bv.BVLt (_, s) -> cmp s ~signed:"bvslt" ~unsigned:"bvult"
        | T_bv.BVGt (_, s) -> cmp s ~signed:"bvsgt" ~unsigned:"bvugt"
        | _ -> raise Unprintable)
    | _ -> raise Unprintable

  let smt_conj atoms =
    match Set.to_list atoms |> List.map ~f:smt_atom with
    | [] -> "true"
    | [ a ] -> a
    | l -> "(and " ^ String.concat ~sep:" " l ^ ")"

  let write_dump ~x ~tvar ~w ~(filled : tally) ~usec ~rules model atoms atoms' dir =
    let key = x ^ " " ^ digest_of_atoms atoms in
    let fresh =
      Stdlib.Mutex.protect dump_lock (fun () ->
          if Hashtbl.mem dumped key then None
          else (
            Hashtbl.set dumped ~key ~data:();
            incr dump_count;
            Some !dump_count))
    in
    Option.iter fresh ~f:(fun n ->
      try
        let vars =
          Set.to_list
            (Set.concat_map (Set.union atoms atoms') ~f:(fun a ->
                 Atom.term_sort_env_of a))
          @ Option.to_list
              (Map.Poly.find model tvar
              |> Option.map ~f:(fun t -> (tvar, Term.sort_of t)))
          |> List.dedup_and_sort ~compare:(fun (a, _) (b, _) ->
                 Ident.tvar_compare a b)
        in
        let decls =
          List.map vars ~f:(fun (v, s) ->
              sprintf "(declare-const %s %s)" (smt_symbol (Ident.name_of_tvar v))
                (smt_sort s))
        in
        let values =
          List.filter_map vars ~f:(fun (v, _) ->
              Map.Poly.find model v
              |> Option.map ~f:(fun t ->
                     sprintf "(assert (= %s %s))"
                       (smt_symbol (Ident.name_of_tvar v)) (smt_term t)))
        in
        let input = smt_conj atoms and output = smt_conj atoms' in
        let path =
          sprintf "%s/%d_%d.smt2" dir (Core_unix.getpid () |> Pid.to_int) n
        in
        let text =
          String.concat ~sep:"\n"
            ([
               sprintf "; x=%s w=%s in=%s out=%s fb=%d g=%d us=%d rules=%s" x w
                 (digest_of_atoms atoms) (digest_of_atoms atoms') filled.fallbacks
                 filled.bits usec
                 (if List.is_empty rules then "-" else String.concat ~sep:"," rules);
               "; coar-out: " ^ output;
             ]
            @ decls
            @ [
                sprintf "(define-fun coar_in () Bool %s)" input;
                sprintf "(define-fun coar_out () Bool %s)" output;
              ]
            @ values
            @ [
                "(assert coar_in)";
                "(check-sat)";
                sprintf "(mbp %s (%s))" input (smt_symbol x);
                "";
              ])
        in
        Out_channel.write_all path ~data:text
      with Unprintable -> ())

  (* The trace frames each call with [call-begin]/[call-end]; [g] on [call-end] is the
     number of bits the fallback copied from the model (the width of every variable it
     substituted, [x] or one introduced for part of [x]) and [fb] the number of those
     substitutions. [reuse_unchanged]: see [prepass_renorm]; [known]: see
     [normalize_atoms_known]. *)
  let model_based_projection_with ~reuse_unchanged ?known ~print model tvar atoms =
    let x = Ident.name_of_tvar tvar in
    let w =
      Option.value_map (width_in_model model tvar) ~default:"?" ~f:string_of_int
    in
    print
    @@ lazy
         (sprintf "[mbp bv] call-begin x=%s w=%s in=%s model=%s" x w
            (digest_of_atoms atoms)
            (digest_of_model model (Set.concat_map atoms ~f:Atom.fvs_of)));
    let filled =
      {
        bits = 0;
        fallbacks = 0;
        census = Option.is_some (Lazy.force stats_file);
        slices = (0, 0, 0);
      }
    in
    (* with the record or the dump on, every rule's trace line is forced to read the
       rule's name (the word after the prefix), whether or not [print] itself prints it *)
    let fired = Queue.create () in
    let print_rule =
      match (Lazy.force stats_file, Lazy.force dump_dir) with
      | None, None -> print
      | _ ->
          fun line ->
            let line = Lazy.force line in
            (match String.chop_prefix line ~prefix:"[mbp bv] " with
            | Some rest ->
                Queue.enqueue fired
                  (List.hd_exn (String.split rest ~on:' '))
            | None -> ());
            print (lazy line)
    in
    let started = Time_ns.now () in
    let atoms' =
      model_based_projection_aux ~reuse_unchanged ?known ~print:print_rule ~filled model
        [ tvar ] atoms
    in
    let usec =
      Time_ns.diff (Time_ns.now ()) started
      |> Time_ns.Span.to_int63_ns |> Int63.to_int_exn |> fun ns -> ns / 1000
    in
    print
    @@ lazy
         (sprintf "[mbp bv] call-end x=%s in=%s out=%s g=%d fb=%d" x
            (digest_of_atoms atoms) (digest_of_atoms atoms') filled.bits
            filled.fallbacks);
    Option.iter (Lazy.force stats_file)
      ~f:(write_stats ~x ~w ~filled ~usec ~rules:(Queue.to_list fired) atoms atoms');
    Option.iter (Lazy.force dump_dir)
      ~f:
        (write_dump ~x ~tvar ~w ~filled ~usec ~rules:(Queue.to_list fired) model
           atoms atoms');
    atoms'

  let model_based_projection ~print model tvar atoms =
    model_based_projection_with ~reuse_unchanged:false ~print model tvar atoms
end


module ADT = struct
  let mk_eq t1 t2 = Atom.mk_app (Predicate.Psym T_bool.Eq) [ t1; t2 ]
  let mk_neq t1 t2 = Atom.mk_app (Predicate.Psym T_bool.Neq) [ t1; t2 ]
  let mem_tvar tvars v = List.exists tvars ~f:(Ident.tvar_equal v)
  let has_tvar tvars atom = Set.exists (Atom.fvs_of atom) ~f:(mem_tvar tvars)

  let contains_false atoms =
    Set.exists atoms
      ~f:(* Check if there are formlas that is false *)
         (* Note that this module only set false when they are contradictor *)
        (function
      | Atom.False _ -> true
      | _ -> false)

  let iter_atom_subterms ~f atom =
    let rec iter_subterms ~f t =
      f t;
      match t with
      | Term.FunApp (_, args, _) -> List.iter args ~f:(iter_subterms ~f)
      | Term.LetTerm (_, _, t1, t2, _) ->
          iter_subterms ~f t1;
          iter_subterms ~f t2
      | Term.Var _ -> ()
    in
    match atom with
    | Atom.App (_, args, _) -> List.iter args ~f:(iter_subterms ~f)
    | Atom.True _ | Atom.False _ -> ()

  let rec term_equal t1 t2 =
    match (t1, t2) with
    | Term.Var (x, _, _), Term.Var (y, _, _) -> Ident.tvar_equal x y
    | Term.FunApp (f1, a1, _), Term.FunApp (f2, a2, _) -> (
        Stdlib.(f1 = f2)
        &&
        match List.for_all2 a1 a2 ~f:term_equal with
        | Ok b -> b
        | Unequal_lengths -> false)
    | Term.LetTerm (x1, s1, a1, b1, _), Term.LetTerm (x2, s2, a2, b2, _) ->
        Ident.tvar_equal x1 x2
        && Stdlib.(s1 = s2)
        && term_equal a1 a2 && term_equal b1 b2
    | _ -> false

  (* [x = C(... x ...)] has no solution in a well-founded datatype: a value cannot be a proper
     subterm of itself.  The argument needs *every* step from the root down to the occurrence
     of [x] to be a constructor.  A selector must not count: SMT-LIB leaves a selector applied
     to the wrong constructor unconstrained, so [x = tl(x)] is satisfiable -- take [x = nil] in
     a model reading [tl(nil)] as [nil] -- and folding it to [false] reports no solution for a
     formula that has one.  (Codatatypes would break the constructor case too, since an
     infinite value satisfies it; they are refused before this point.) *)
  let rec occurs_under_cons x = function
    | Term.FunApp (T_dt.DTCons _, args, _) ->
        List.exists args ~f:(fun a ->
            (match a with
              | Term.Var (y, _, _) -> Ident.tvar_equal y x
              | _ -> false)
            || occurs_under_cons x a)
    | _ -> false

  let model_term_of model t =
    Term.of_value (get_dtenv ()) @@ Evaluator.eval_term @@ Term.subst model t

  let head_cons_of model t =
    match model_term_of model t with
    | Term.FunApp (T_dt.DTCons (cname, _, dt), args, _) -> Some (cname, dt, args)
    | _ -> None

  let models_is_cons model cname u =
    match head_cons_of model u with
    | Some (c, _, _) -> String.(c = cname)
    | None -> false

  let sel_terms_of atoms =
    Set.fold atoms ~init:[] ~f:(fun acc atom ->
        let local = ref acc in
        iter_atom_subterms atom ~f:(fun s ->
            if T_dt.is_sel s then local := s :: !local);
        !local)

  let find_var_to_expand tvars atoms =
    match
      List.find_map (sel_terms_of atoms) ~f:(function
        | Term.FunApp (T_dt.DTSel (_, dt, _), [ Term.Var (x, _, _) ], _)
          when mem_tvar tvars x ->
            Some (x, dt)
        | _ -> None)
    with
    | Some res -> Some res
    | None ->
        Set.find_map atoms ~f:(function
          | Atom.App
              (Predicate.Psym (T_dt.IsCons (_, dt)), [ Term.Var (x, _, _) ], _)
          | Atom.App
              ( Predicate.Psym (T_dt.NotIsCons (_, dt)),
                [ Term.Var (x, _, _) ],
                _ )
            when mem_tvar tvars x ->
              Some (x, dt)
          | _ -> None)

  let sels_and_iscons dt cname u =
    match Datatype.look_up_cons dt cname with
    | Some cons ->
        let sels = Datatype.sels_of_cons cons in
        let sel_terms =
          List.map sels ~f:(fun sel ->
              T_dt.mk_sel dt (Datatype.name_of_sel sel) u)
        in
        (T_dt.mk_is_cons dt cname u, sel_terms)
    | None -> failwith @@ sprintf "[ADT.sels_and_iscons] unknown cons: %s" cname

  let assert_no_codt atoms =
    Set.iter atoms ~f:(fun atom ->
        iter_atom_subterms atom ~f:(function
          | Term.FunApp (T_dt.DTCons (_, _, dt), _, _)
          | Term.FunApp (T_dt.DTSel (_, dt, _), _, _) ->
              if Datatype.is_codt dt then
                failwith "[ADT] codatatype is not supported"
          | _ -> ()))

  let normalize_init_step ~print atoms =
    Set.concat_map atoms ~f:(fun atom ->
        match atom with
        | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _) -> (
            match (t1, t2) with
            | _ when term_equal t1 t2 -> Set.Poly.empty
            | ( Term.FunApp (T_dt.DTCons (c1, _, _), a1, _),
                Term.FunApp (T_dt.DTCons (c2, _, _), a2, _) ) ->
                if String.(c1 = c2) then
                  Set.Poly.of_list (List.map2_exn a1 a2 ~f:mk_eq)
                else (
                  print
                  @@ lazy
                       (sprintf "[mbp adt] exclusivity: %s = %s -> bot" c1 c2);
                  Set.Poly.singleton (Atom.mk_false ()))
            | ( (Term.Var _ | Term.FunApp (T_dt.DTSel _, _, _)),
                Term.FunApp (T_dt.DTCons _, _, _) ) ->
                Set.Poly.singleton (mk_eq t2 t1)
            | Term.Var (x, _, _), (Term.FunApp _ as r)
              when occurs_under_cons x r ->
                print
                @@ lazy
                     (sprintf "[mbp adt] acyclicity: %s -> bot"
                        (Ident.name_of_tvar x));
                Set.Poly.singleton (Atom.mk_false ())
            | (Term.FunApp _ as l), Term.Var (x, _, _)
              when occurs_under_cons x l ->
                print
                @@ lazy
                     (sprintf "[mbp adt] acyclicity: %s -> bot"
                        (Ident.name_of_tvar x));
                Set.Poly.singleton (Atom.mk_false ())
            | _ -> Set.Poly.singleton atom)
        | Atom.App
            ( Predicate.Psym (T_dt.IsCons (name, _)),
              [ Term.FunApp (T_dt.DTCons (name1, _, _), _, _) ],
              _ ) ->
            if String.(name = name1) then Set.Poly.empty
            else Set.Poly.singleton (Atom.mk_false ())
        | Atom.App
            ( Predicate.Psym (T_dt.NotIsCons (name, _)),
              [ Term.FunApp (T_dt.DTCons (name1, _, _), _, _) ],
              _ ) ->
            if String.(name <> name1) then Set.Poly.empty
            else Set.Poly.singleton (Atom.mk_false ())
        | _ -> Set.Poly.singleton atom)

  let rec normalize_init ~print atoms =
    let atoms' = normalize_init_step ~print atoms in
    if contains_false atoms' then Set.Poly.singleton (Atom.mk_false ())
    else if Set.equal atoms' atoms then atoms
    else normalize_init ~print atoms'

  let add_is_cons ~print model atoms =
    (* TODO: It might be better to perform normalization before running mbp, we needs review. *)
    List.fold (sel_terms_of atoms) ~init:atoms ~f:(fun atoms sel ->
        match sel with
        | Term.FunApp (T_dt.DTSel (selname, dt, _), [ arg ], _) -> (
            match Datatype.look_up_cons_of_sel dt selname with
            | Some cons ->
                let cname = Datatype.name_of_cons cons in
                (* Cases where the selector argument in a model does not correspond to the target constructor.*)
                (* Undefined the value of selector. Maybe we should adjust how we select models.*)
                if not (models_is_cons model cname arg) then (
                  print
                  @@ lazy
                       (sprintf
                          "[mbp adt] discrepancies between model and sel: \
                           %s(%s)"
                          cname (Term.str_of arg));
                  atoms)
                else
                  let already =
                    Set.exists atoms ~f:(function
                      | Atom.App (Predicate.Psym (T_dt.IsCons (c, _)), [ u ], _)
                        ->
                          String.(c = cname) && term_equal u arg
                      | _ -> false)
                  in
                  if already then atoms
                  else (
                    print
                    @@ lazy
                         (sprintf "[mbp adt] add is_cons: %s(%s)" cname
                            (Term.str_of arg));
                    Set.add atoms (T_dt.mk_is_cons dt cname arg))
            | None -> atoms)
        | _ -> atoms)

  let rec reduce_sel_cons t =
    match t with
    | Term.FunApp (T_dt.DTSel (selname, dt, _), [ arg ], info) -> (
        let arg' = reduce_sel_cons arg in
        match arg' with
        | Term.FunApp (T_dt.DTCons _, _, _) -> (
            match T_dt.eval_select selname dt arg' with
            | Some ti -> ti
            | None -> T_dt.mk_sel dt selname arg' ~info)
        | _ -> T_dt.mk_sel dt selname arg' ~info)
    | Term.FunApp (fsym, args, info) ->
        Term.mk_fsym_app fsym (List.map args ~f:reduce_sel_cons) ~info
    | Term.LetTerm (v, s, t1, t2, info) ->
        Term.mk_let_term v s (reduce_sel_cons t1) (reduce_sel_cons t2) ~info
    | Term.Var _ -> t

  let del_sel_cons ~print:_ _model _tvars atoms =
    Set.Poly.map atoms ~f:(function
      | Atom.App (pred, args, info) ->
          Atom.mk_app pred (List.map args ~f:reduce_sel_cons) ~info
      | atom -> atom)

  let rec del_sel ~print model tvars atoms =
    match find_var_to_expand tvars atoms with
    | None -> (model, tvars, atoms)
    | Some (x, dt) -> (
        let xvar = Term.mk_var x (T_dt.SDT dt) in
        match head_cons_of model xvar with
        | None -> failwith "[ADT.del_sel] model gives no constructor"
        | Some (cname, _, _) -> (
            match Datatype.look_up_cons dt cname with
            | None -> failwith @@ sprintf "[ADT.del_sel] unknown cons: %s" cname
            | Some cons ->
                let sels = Datatype.sels_of_cons cons in
                let fresh =
                  List.map sels ~f:(fun _ -> Ident.mk_fresh_tvar ())
                in
                (* x := c(y1..yk) *)
                let args =
                  List.map2_exn fresh sels ~f:(fun v sel ->
                      Term.mk_var v (Datatype.sort_of_sel dt sel))
                in
                let consterm = T_dt.mk_cons dt cname args in
                let sub = Map.Poly.singleton x consterm in
                let atoms' = Set.Poly.map atoms ~f:(Atom.subst sub) in
                (* Extend the model: y_i |-> M(sel_{c,i}(x)) *)
                let model' =
                  List.fold2_exn fresh sels ~init:model ~f:(fun m v sel ->
                      let sval =
                        model_term_of model
                        @@ T_dt.mk_sel dt (Datatype.name_of_sel sel) xvar
                      in
                      Map.Poly.set m ~key:v ~data:sval)
                in
                let tvars' =
                  fresh
                  @ List.filter tvars ~f:(fun v -> not (Ident.tvar_equal v x))
                in
                print
                @@ lazy
                     (sprintf "[mbp adt] del_sel: %s := %s"
                        (Ident.name_of_tvar x) (Term.str_of consterm));
                let atoms'' = del_sel_cons ~print model' tvars' atoms' in
                del_sel ~print model' tvars' atoms''))

  let eq_atom tvars = function
    | Atom.App (Predicate.Psym T_bool.Eq, [ Term.Var (x, _, _); t ], _)
      when mem_tvar tvars x && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some (x, t)
    | Atom.App (Predicate.Psym T_bool.Eq, [ t; Term.Var (x, _, _) ], _)
      when mem_tvar tvars x && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some (x, t)
    | _ -> None

  let rec substitution_with_eq ~print model tvars atoms =
    match Set.find_map atoms ~f:(eq_atom tvars) with
    | None -> atoms
    | Some (x, t) ->
        print
        @@ lazy
             (sprintf "[mbp adt] subst: %s := %s" (Ident.name_of_tvar x)
                (Term.str_of t));
        let sub = Map.Poly.singleton x t in
        substitution_with_eq ~print model tvars
        @@ Set.concat_map atoms ~f:(Atom.subst sub >> normalize_mbp model)

  let unify ~print:_ tvars atoms =
    Set.concat_map atoms ~f:(fun atom ->
        match atom with
        | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _) -> (
            match (t1, t2) with
            | Term.FunApp (T_dt.DTCons (cname, _, dt), cargs, _), u
            | u, Term.FunApp (T_dt.DTCons (cname, _, dt), cargs, _) ->
                if T_dt.is_cons u then Set.Poly.singleton atom
                else if not (has_tvar tvars atom) then Set.Poly.singleton atom
                else
                  let is_c, sel_terms = sels_and_iscons dt cname u in
                  let eqs = List.map2_exn cargs sel_terms ~f:mk_eq in
                  Set.Poly.of_list (is_c :: eqs)
            | _ -> Set.Poly.singleton atom)
        | _ -> Set.Poly.singleton atom)

  let step_neq ~print:_ model tvars atoms =
    Set.concat_map atoms ~f:(fun atom ->
        match atom with
        | Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _) -> (
            match (t1, t2) with
            | Term.FunApp (T_dt.DTCons (cname, _, dt), cargs, _), u
            | u, Term.FunApp (T_dt.DTCons (cname, _, dt), cargs, _) -> (
                if not (has_tvar tvars atom) then Set.Poly.singleton atom
                else if not (models_is_cons model cname u) then
                  Set.Poly.singleton (T_dt.mk_is_not_cons dt cname u)
                else
                  let is_c, sel_terms = sels_and_iscons dt cname u in
                  let mval_eq model a b =
                    term_equal (model_term_of model a) (model_term_of model b)
                  in
                  let diff =
                    List.find (List.zip_exn cargs sel_terms) ~f:(fun (ti, si) ->
                        not (mval_eq model ti si))
                  in
                  match diff with
                  | Some (ti, si) -> Set.Poly.of_list [ is_c; mk_neq ti si ]
                  | None -> Set.Poly.singleton (Atom.mk_false ()))
            | _ -> Set.Poly.singleton atom)
        | _ -> Set.Poly.singleton atom)

  let rec neq_loop ~print model tvars atoms =
    let has_cons_neq_with_tvar tvars atoms =
      Set.exists atoms ~f:(function
        | Atom.App (Predicate.Psym T_bool.Neq, [ t1; t2 ], _) as atom ->
            (T_dt.is_cons t1 || T_dt.is_cons t2) && has_tvar tvars atom
        | _ -> false)
    in
    let model, tvars, atoms = del_sel ~print model tvars atoms in
    if has_cons_neq_with_tvar tvars atoms then
      neq_loop ~print model tvars (step_neq ~print model tvars atoms)
    else (model, tvars, atoms)

  let elim_diseq ~print model x dt atoms =
    FinDom.elim_diseq ~print model x (T_dt.SDT dt) atoms

  let is_adt_tvar model y =
    match Map.Poly.find model y with
    | Some (Term.FunApp (T_dt.DTCons _, _, _)) -> true
    | _ -> false

  let elim_other ~print model y atoms =
    let atoms1, atoms2 =
      Set.partition_tf atoms ~f:(fun a -> Set.mem (Atom.fvs_of a) y)
    in
    let fallback () =
      let sub = Map.Poly.singleton y (Map.Poly.find_exn model y) in
      Set.union atoms2
      @@ Set.concat_map atoms1 ~f:(Atom.subst sub >> normalize_mbp model)
    in
    match Map.Poly.find model y with
    (* [fallback] begins with [find_exn model y], so routing the "not in the model" case to it
       produced a bare [Not_found_s] from the one branch written to handle that case.  There is
       nothing sensible to substitute; say which variable is missing. *)
    | None ->
        failwith
        @@ sprintf
             "[mbp adt] the model does not bind %s, so it cannot be eliminated \
              by substituting its value"
             (Ident.name_of_tvar y)
    | Some v -> (
        try
          match Term.sort_of v with
          | T_bool.SBool ->
              Set.union atoms2
                (Boolean.model_based_projection ~print model y atoms1)
          | T_int.SInt ->
              Set.union atoms2
                (LIA.model_based_projection ~print model y atoms1)
          | T_real.SReal ->
              Set.union atoms2
                (LRA.model_based_projection ~print model y atoms1)
          | _ -> fallback ()
          (* TODO: Separate implementation is required for cases such as mixing ADT and arrays.
          It might be better to change the mbp search in proof search itself. *)
        with NotNormalized | Failure _ -> fallback ())

  let rec model_based_projection_aux ~print model tvars atoms =
    (* the individual rules each print, but the loop that applies them did not, so a rewrite
       that fails to make progress was invisible: nothing distinguished "still working" from
       "going round" *)
    print
    @@ lazy
         (sprintf "[mbp adt] loop: tvars=[%s] atoms={%s}"
            (String.concat_map_list ~sep:"; " tvars ~f:Ident.name_of_tvar)
            (String.concat_map_set ~sep:"; " ~f:Atom.str_of atoms));
    let atoms = normalize_init ~print atoms in
    if contains_false atoms then Set.Poly.singleton (Atom.mk_false ())
    else
      let atoms = substitution_with_eq ~print model tvars atoms in
      if contains_false atoms then Set.Poly.singleton (Atom.mk_false ())
      else
        let tvars =
          List.filter tvars ~f:(fun x ->
              Set.exists atoms ~f:(fun a -> Set.mem (Atom.fvs_of a) x))
        in
        let has_eq_with_tvar tvars atoms =
          Set.exists atoms ~f:(function
            | Atom.App (Predicate.Psym T_bool.Eq, _, _) as atom ->
                has_tvar tvars atom
            | _ -> false)
        in
        if List.is_empty tvars then atoms
        else if List.exists tvars ~f:(fun y -> not (is_adt_tvar model y)) then
          let y = List.find_exn tvars ~f:(fun y -> not (is_adt_tvar model y)) in
          model_based_projection_aux ~print model
            (List.filter tvars ~f:(fun v -> not (Ident.tvar_equal v y)))
            (elim_other ~print model y atoms)
        else if has_eq_with_tvar tvars atoms then
          let has_cons_eq =
            Set.exists atoms ~f:(function
              | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _) as a ->
                  (T_dt.is_cons t1 || T_dt.is_cons t2) && has_tvar tvars a
              | _ -> false)
          in
          if Option.is_none (find_var_to_expand tvars atoms) && not has_cons_eq
          then raise NotNormalized
          else
            let model, tvars, atoms = del_sel ~print model tvars atoms in
            let atoms = unify ~print tvars atoms in
            model_based_projection_aux ~print model tvars atoms
        else
          let model, tvars, atoms = neq_loop ~print model tvars atoms in
          let atoms = normalize_init ~print atoms in
          if contains_false atoms then Set.Poly.singleton (Atom.mk_false ())
          else
            let tvars =
              List.filter tvars ~f:(fun x ->
                  Set.exists atoms ~f:(fun a -> Set.mem (Atom.fvs_of a) x))
            in
            if List.is_empty tvars then atoms
            else
              let x = List.hd_exn tvars in
              let tvars' =
                List.filter tvars ~f:(fun v -> not (Ident.tvar_equal v x))
              in
              match Map.Poly.find model x with
              | Some (Term.FunApp (T_dt.DTCons (_, _, dt), _, _)) ->
                  model_based_projection_aux ~print model tvars'
                  @@ elim_diseq ~print model x dt atoms
              | _ ->
                  model_based_projection_aux ~print model tvars'
                  @@ elim_other ~print model x atoms

  let model_based_projection ~print model tvar atoms =
    assert_no_codt atoms;
    (* TODO: codatatype is not supported *)
    let atoms = add_is_cons ~print model atoms in
    let res = model_based_projection_aux ~print model [ tvar ] atoms in
    if contains_false res then Set.Poly.singleton (Atom.mk_false ())
    else Set.concat_map res ~f:(normalize_mbp model)
end

module SAtom = struct
  type t = Atom.t * Term.t Set.Poly.t

  let get_atom (atom, _) = atom
  let get_set (_, s) = s
  let of_atom ?(s = Set.Poly.empty) atom = (atom, s)

  (* The atom an array literal with an index set stands for.  [(t1 = t2, S)]
     says the arrays agree at every index outside [S], and [(t1 <> t2, S)] that
     they differ at some index outside [S]; both are written without the set by
     overwriting [t1] at each index of [S] with [t2]'s value there,
     [store (... store (t1, i, t2[i]) ...) = t2].  This holds whatever [t1] is:
     reading the set only when [t1] happened to be a store printed
     [(c <> b, {j})] as [c <> b], weaker than the literal, and the projection of
     [store (c, j, x[0]) <> b /\ x[0] = b[j]] came out [c <> b], which a [c]
     differing from [b] only at [j] satisfies while no [x] does; in the equality
     direction it was stronger than the literal and false in the model. *)
  let to_atom (atom, s) =
    if Set.is_empty s then atom
    else
      match atom with
      | Atom.App
          (Predicate.Psym ((T_bool.Eq | T_bool.Neq) as op), [ t1; t2 ], info)
        -> (
          match Term.sort_of t1 with
          | T_array.SArray (idx_s, elem_s) ->
              let t1' =
                Set.fold s ~init:t1 ~f:(fun acc i ->
                    T_array.mk_store idx_s elem_s acc i
                      (T_array.mk_select idx_s elem_s t2 i))
              in
              Atom.mk_app ~info (Predicate.Psym op) [ t1'; t2 ]
          | _ -> atom)
      | _ -> atom
end

module ARR = struct
  let eq_atom tvar = function
    | Atom.App (Predicate.Psym T_bool.Eq, [ Term.Var (x, _, _); t ], _)
      when Ident.tvar_equal x tvar && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some t
    | Atom.App (Predicate.Psym T_bool.Eq, [ t; Term.Var (x, _, _) ], _)
      when Ident.tvar_equal x tvar && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some t
    | _ -> None

  let neq_atom tvar = function
    | Atom.App (Predicate.Psym T_bool.Neq, [ Term.Var (x, _, _); t ], _)
      when Ident.tvar_equal x tvar && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some t
    | Atom.App (Predicate.Psym T_bool.Neq, [ t; Term.Var (x, _, _) ], _)
      when Ident.tvar_equal x tvar && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some t
    | _ -> None

  let triv_eq satoms =
    let term_equal t1 t2 =
      match (t1, t2) with
      | Term.Var (v1, _, _), Term.Var (v2, _, _) -> Ident.tvar_equal v1 v2
      | _ -> false
      (*TODO Other terms*)
    in

    let is_triv_eq_atom atom =
      match atom with
      | Atom.App (Predicate.Psym T_bool.Eq, [ t1; t2 ], _) ->
          if term_equal t1 t2 then true else false
      | _ -> false
    in
    Set.filter satoms ~f:(fun (atom, _) -> not (is_triv_eq_atom atom))

  let is_store = function
    | Term.FunApp (T_array.AStore _, _, _) -> true
    | _ -> false

  let symm satoms =
    let is_symm_target atom =
      match atom with
      | Atom.App (_, [ t1; t2 ], _) -> (not (is_store t1)) && is_store t2
      | _ -> false
    in

    Set.Poly.map satoms ~f:(fun (atom, set) ->
        if is_symm_target atom then
          match atom with
          | Atom.App (pred, [ t1; t2 ], info) ->
              SAtom.of_atom ~s:set (Atom.mk_app ~info pred [ t2; t1 ])
          | _ -> SAtom.of_atom ~s:set atom
        else SAtom.of_atom ~s:set atom)

  let eval_satom model satom =
    match SAtom.to_atom satom with
    | Atom.App (_, _, _) as atom -> Evaluator.eval_atom @@ Atom.subst model atom
    | Atom.True _ -> true
    | Atom.False _ -> false

  let mem_by_model model i set =
    let i_v = Evaluator.eval_term @@ Term.subst model i in
    Set.find set ~f:(fun t ->
        Value.eq i_v @@ Evaluator.eval_term @@ Term.subst model t)

  let mbp_disjunction model satom1 satom2 =
    if eval_satom model satom1 then Some satom1
    else if eval_satom model satom2 then Some satom2
    else None

  let rec aux_elim_wr_rd model term =
    match term with
    | Term.FunApp
        ( T_array.ASelect (idx_s, elemm_s),
          [ Term.FunApp (T_array.AStore (_, _), [ t; i; v ], _); j ],
          _ ) ->
        if
          Value.eq
            (Evaluator.eval_term @@ Term.subst model i)
            (Evaluator.eval_term @@ Term.subst model j)
        then
          let extra, new_v = aux_elim_wr_rd model v in
          ( Set.add extra
              (Atom.mk_app (Predicate.Psym T_bool.Eq) [ i; j ], Set.Poly.empty),
            new_v )
        else
          let extra_t, new_t = aux_elim_wr_rd model t in
          let extra_j, new_j = aux_elim_wr_rd model j in
          let extra_t_j = Set.union extra_t extra_j in
          ( Set.add extra_t_j
              (Atom.mk_app (Predicate.Psym T_bool.Neq) [ i; j ], Set.Poly.empty),
            T_array.mk_select idx_s elemm_s new_t new_j )
    | Term.FunApp (fun_sym, args, info) ->
        let extra_atoms, new_args =
          List.fold_map args ~init:Set.Poly.empty ~f:(fun acc arg ->
              let extra, new_arg = aux_elim_wr_rd model arg in
              (Set.union acc extra, new_arg))
        in
        (extra_atoms, Term.mk_fsym_app fun_sym new_args ~info)
    | Term.LetTerm (tvar, sort, t1, t2, info) ->
        let extra1, new_t1 = aux_elim_wr_rd model t1 in
        let extra2, new_t2 = aux_elim_wr_rd model t2 in
        (Set.union extra1 extra2, Term.mk_let_term tvar sort new_t1 new_t2 ~info)
    | _ -> (Set.Poly.empty, term)

  let elim_wr_rd model satoms =
    Set.concat_map satoms ~f:(fun (atom, set) ->
        match atom with
        | Atom.App (pred, args, info) ->
            let extra_atoms, new_args =
              List.fold_map args ~init:Set.Poly.empty ~f:(fun acc arg ->
                  let extra, new_arg = aux_elim_wr_rd model arg in
                  (Set.union acc extra, new_arg))
            in
            Set.add extra_atoms (Atom.mk_app pred new_args ~info, set)
        | _ -> Set.Poly.singleton (atom, set))

  let elim_wr_eq_satom model (atom, set) =
    match atom with
    | Atom.App (_, args, info) -> (
        match args with
        | [ wrt; t2 ] -> (
            match wrt with
            | Term.FunApp (T_array.AStore (idx_s, val_s), [ t1; j; v ], _) -> (
                match mem_by_model model j set with
                | Some t ->
                    let eq1 =
                      let atm1 =
                        Atom.mk_app ~info (Predicate.Psym T_bool.Eq) [ t1; t2 ]
                      in
                      SAtom.of_atom ~s:set atm1
                    in
                    let eq2 =
                      let atm2 =
                        Atom.mk_app ~info (Predicate.Psym T_bool.Eq) [ j; t ]
                      in
                      SAtom.of_atom atm2
                    in
                    Set.Poly.of_list [ eq1; eq2 ]
                | None ->
                    let eq1 =
                      let atm1 =
                        Atom.mk_app ~info (Predicate.Psym T_bool.Eq) [ t1; t2 ]
                      in
                      let set1 = Set.add set j in
                      SAtom.of_atom ~s:set1 atm1
                    in
                    let eq2 =
                      let rdt = T_array.mk_select idx_s val_s t2 j in
                      let atm2 =
                        Atom.mk_app ~info (Predicate.Psym T_bool.Eq) [ v; rdt ]
                      in
                      SAtom.of_atom atm2
                    in
                    let neq_set =
                      Set.Poly.map set ~f:(fun t ->
                          ( Atom.mk_app ~info (Predicate.Psym T_bool.Neq)
                              [ j; t ],
                            Set.Poly.empty ))
                    in
                    Set.union neq_set (Set.Poly.of_list [ eq1; eq2 ]))
            | _ -> failwith "elim_wr_eq: not a write term")
        | _ -> failwith "elim_wr_eq: not a binary predicate")
    | _ -> failwith "elim_wr_eq: not apply"

  let elim_wr_eq model satoms =
    Set.concat_map satoms ~f:(fun satom ->
        let atom = SAtom.get_atom satom in
        match atom with
        | Atom.App (Predicate.Psym T_bool.Eq, [ t1; _ ], _) when is_store t1 ->
            elim_wr_eq_satom model satom
        | _ -> Set.Poly.singleton satom)

  let elim_wr_neq_satom model (atom, set) =
    match atom with
    | Atom.App (_, args, info) -> (
        match args with
        | [ wrt; t2 ] -> (
            match wrt with
            | Term.FunApp (T_array.AStore (idx_s, elem_s), [ t1; j; v ], _) -> (
                match mem_by_model model j set with
                | Some t ->
                    let neq =
                      let atm1 =
                        Atom.mk_app ~info (Predicate.Psym T_bool.Neq) [ t1; t2 ]
                      in
                      SAtom.of_atom ~s:set atm1
                    in
                    let eq =
                      let atm2 =
                        Atom.mk_app ~info (Predicate.Psym T_bool.Eq) [ j; t ]
                      in
                      SAtom.of_atom atm2
                    in
                    Set.Poly.of_list [ neq; eq ]
                | None -> (
                    let neq1 =
                      let atm1 =
                        Atom.mk_app ~info (Predicate.Psym T_bool.Neq) [ t1; t2 ]
                      in
                      let set1 = Set.add set j in
                      SAtom.of_atom ~s:set1 atm1
                    in
                    let neq2 =
                      let rdt = T_array.mk_select idx_s elem_s t2 j in
                      let atm2 =
                        Atom.mk_app ~info (Predicate.Psym T_bool.Neq) [ v; rdt ]
                      in
                      SAtom.of_atom atm2
                    in
                    let neq_set =
                      Set.Poly.map set ~f:(fun t ->
                          ( Atom.mk_app ~info (Predicate.Psym T_bool.Neq)
                              [ j; t ],
                            Set.Poly.empty ))
                    in
                    match mbp_disjunction model neq1 neq2 with
                    | Some atm -> Set.add neq_set atm
                    | None ->
                        Set.Poly.singleton (Atom.mk_false (), Set.Poly.empty)))
            | _ -> failwith "elim_wr_neq: not a write term")
        | _ -> failwith "elim_wr_neq: not a binary predicate")
    | _ -> failwith "elim_wr_neq: not apply"

  let elim_wr_neq model satoms =
    Set.concat_map satoms ~f:(fun satom ->
        let atom = SAtom.get_atom satom in
        match atom with
        | Atom.App (Predicate.Psym T_bool.Neq, [ t1; _ ], _) when is_store t1 ->
            elim_wr_neq_satom model satom
        | _ -> Set.Poly.singleton satom)

  (* Rewrites until no store is left, or until a round changes nothing.  A store is looked
     for under every function symbol: a read through a store nested under arithmetic,
     [store (x, 0, 1)[y] + 1 = z], is one [elim_wr_rd] removes, and a search that stopped at
     the top of the atom, a [select] or a constant array left it in place, so the
     projection returned the input with the eliminated array still in it.  The progress
     test bounds the loop where a store sits in a position no rule here rewrites (under an
     uninterpreted function, say); the caller then finds the variable still present and
     substitutes its model value. *)
  let rec aux_elim_write model satoms =
    let rec exist_write_term = function
      | Term.FunApp (T_array.AStore (_, _), _, _) -> true
      | Term.FunApp (_, args, _) -> List.exists args ~f:exist_write_term
      | Term.LetTerm (_, _, t1, t2, _) ->
          exist_write_term t1 || exist_write_term t2
      | Term.Var _ -> false
    in

    let exist_write =
      Set.exists satoms ~f:(fun (atm, _) ->
          match atm with
          | Atom.App (_, args, _) -> List.exists args ~f:exist_write_term
          | _ -> false)
    in

    if exist_write then
      let satoms' =
        satoms |> symm |> triv_eq |> elim_wr_rd model |> elim_wr_eq model
        |> elim_wr_neq model
      in
      if Set.equal satoms' satoms then satoms else aux_elim_write model satoms'
    else satoms

  let elim_write model satoms = aux_elim_write model satoms |> triv_eq

  let model_term_of model t =
    Term.of_value (get_dtenv ()) @@ Evaluator.eval_term @@ Term.subst model t

  let name_read model name def =
    match name with
    | Term.Var (y, _, _) ->
        Map.Poly.set model ~key:y ~data:(model_term_of model def)
    | _ -> model

  let rec aux_factor_out model tvar term =
    match term with
    | Term.FunApp (T_array.ASelect (idx_s, elemm_s), [ t1; t2 ], _) -> (
        let model, extra2, new_t2 = aux_factor_out model tvar t2 in
        match t1 with
        | Term.Var (x, sort, info) when Ident.tvar_equal tvar x ->
            let s = Term.mk_fresh_var elemm_s in
            let new_read =
              T_array.mk_select idx_s elemm_s
                (Term.mk_var tvar sort ~info)
                new_t2
            in
            ( name_read model s new_read,
              Set.add extra2
                ( Atom.mk_app (Predicate.Psym T_bool.Eq) [ s; new_read ],
                  Set.Poly.empty ),
              s )
        | _ ->
            let model, extra1, new_t1 = aux_factor_out model tvar t1 in
            ( model,
              Set.union extra1 extra2,
              T_array.mk_select idx_s elemm_s new_t1 new_t2 ))
    | Term.FunApp (fun_sym, args, info) ->
        let model, extra_satoms, new_args =
          List.fold args ~init:(model, Set.Poly.empty, [])
            ~f:(fun (model, acc_atoms, acc_args) arg ->
              let model, atom, new_arg = aux_factor_out model tvar arg in
              (model, Set.union acc_atoms atom, new_arg :: acc_args))
          |> fun (model, res_atoms, res_args) ->
          (model, res_atoms, List.rev res_args)
        in
        (model, extra_satoms, Term.mk_fsym_app ~info fun_sym new_args)
    | Term.LetTerm (v, sort, t1, t2, info) ->
        (* the binder is [v], not the variable being eliminated: binding it under that
           name made both recursive calls look for reads of the let variable instead.  A
           body under a binder that shadows [tvar] reads no [tvar] *)
        let model, extra1, new_t1 = aux_factor_out model tvar t1 in
        let model, extra2, new_t2 =
          if Ident.tvar_equal v tvar then (model, Set.Poly.empty, t2)
          else aux_factor_out model tvar t2
        in
        ( model,
          Set.union extra1 extra2,
          Term.mk_let_term ~info v sort new_t1 new_t2 )
    | _ -> (model, Set.Poly.empty, term)

  let factor_out model tvar satoms =
    (*CaseSplitEq*)
    (* We don't have to implement since in this point, we think only atomic formulas*)
    (*FactorRd*)
    Set.fold satoms ~init:(model, Set.Poly.empty)
      ~f:(fun (model, acc) (atom, set) ->
        match atom with
        | Atom.App (pred, args, info) ->
            (* the index set is part of the literal, and an index written by a
               store whose index read the variable ([store (c, x[0], v) = b])
               carries that read into it; left unnamed, it reached the result
               and the projection still mentioned the variable *)
            let factor model terms =
              List.fold terms ~init:(model, Set.Poly.empty, [])
                ~f:(fun (model, acc_atoms, acc_args) arg ->
                  let model, atom, new_arg = aux_factor_out model tvar arg in
                  (model, Set.union acc_atoms atom, new_arg :: acc_args))
              |> fun (model, res_atoms, res_args) ->
              (model, res_atoms, List.rev res_args)
            in
            let model, extra_satoms, new_args = factor model args in
            let model, extra_set_satoms, new_set =
              factor model (Set.to_list set)
            in
            ( model,
              Set.union acc
              @@ Set.add
                   (Set.union extra_satoms extra_set_satoms)
                   (Atom.mk_app pred new_args ~info, Set.Poly.of_list new_set) )
        | _ -> (model, Set.add acc (atom, set)))

  let elim_eq model tvar satoms =
    match
      Set.find_map satoms ~f:(fun (atom, set) ->
          match eq_atom tvar atom with Some t -> Some (t, set) | None -> None)
    with
    | Some (t, set) -> (
        match Term.sort_of t with
        | T_array.SArray (idx_s, elem_s) ->
            let arr = Term.mk_var tvar (T_array.SArray (idx_s, elem_s)) in
            let model, updated_t =
              Set.fold set ~init:(model, t) ~f:(fun (model, acc) i ->
                  let fresh_var = Term.mk_fresh_var elem_s in
                  ( name_read model fresh_var
                    @@ T_array.mk_select idx_s elem_s arr i,
                    T_array.mk_store idx_s elem_s acc i fresh_var ))
            in
            let sub = Map.Poly.singleton tvar updated_t in
            Some
              ( model,
                Set.Poly.map satoms ~f:(fun (atom, set) ->
                    (Atom.subst sub atom, set)) )
        | _ -> failwith "elim_eq: tvar not array")
    | None -> None

  let elim_neq _model tvar satoms =
    Set.filter satoms ~f:(fun (atom, _) ->
        match neq_atom tvar atom with Some _ -> false | None -> true)

  let rec value_eq_is_exact = function
    | T_int.SInt | T_real.SReal | T_bool.SBool | T_bv.SBV (Some _) -> true
    | T_tuple.STuple sorts -> List.for_all sorts ~f:value_eq_is_exact
    | T_array.SArray (idx_s, elem_s) ->
        (* a model's finite map cannot cover an index domain this large, so the
           normalized value is extensional *)
        let k = 1 lsl 20 in
        FinDom.card_upto [] idx_s k >= k && value_eq_is_exact elem_s
    | _ -> false

  let ackermann model tvar satoms =
    let reads, other_satoms =
      Set.fold satoms ~init:([], Set.Poly.empty)
        ~f:(fun (pairs, others) (atom, set) ->
          match atom with
          | Atom.App
              ( Predicate.Psym T_bool.Eq,
                [
                  s;
                  Term.FunApp
                    (T_array.ASelect (idx_s, _), [ Term.Var (a, _, _); t ], _);
                ],
                _ )
          | Atom.App
              ( Predicate.Psym T_bool.Eq,
                [
                  Term.FunApp
                    (T_array.ASelect (idx_s, _), [ Term.Var (a, _, _); t ], _);
                  s;
                ],
                _ ) ->
              if Ident.tvar_equal a tvar then ((idx_s, t, s) :: pairs, others)
              else (pairs, Set.add others (atom, set))
          | _ -> (pairs, Set.add others (atom, set)))
    in
    match reads with
    | [] -> other_satoms
    | (idx_s, _, _) :: _ ->
        if not @@ value_eq_is_exact idx_s then
          failwith
          @@ sprintf "[mbp arr] cannot compare indices of sort %s"
               (Term.str_of_sort idx_s);
        let groups =
          List.fold reads ~init:[] ~f:(fun classes (_, t, s) ->
              let v = Evaluator.eval_term (Term.subst model t) in
              let rec add = function
                | [] -> [ (v, [ (t, s) ]) ]
                | (v', ts) :: rest ->
                    if FinDom.val_eq v v' then (v', (t, s) :: ts) :: rest
                    else (v', ts) :: add rest
              in
              add classes)
          |> List.map ~f:(fun (v, ts) -> (v, List.rev ts))
        in
        let equivalence_class_atoms =
          List.concat_map groups ~f:(fun (_, group) ->
              match group with
              | (t_rep, s_rep) :: others ->
                  List.concat_map others ~f:(fun (t_nrep, s_nrep) ->
                      [
                        Atom.mk_app (Predicate.Psym T_bool.Eq) [ t_rep; t_nrep ];
                        Atom.mk_app (Predicate.Psym T_bool.Eq) [ s_rep; s_nrep ];
                      ])
              | [] -> [])
        in
        let representatives =
          List.filter_map groups ~f:(fun (v, group) ->
              Option.map (List.hd group) ~f:(fun (t, _) -> (v, t)))
        in
        let inter_atoms =
          let chain lt =
            let sorted =
              List.sort representatives ~compare:(fun (v1, _) (v2, _) ->
                  if Value.eq v1 v2 then 0
                  else if Value.geq v1 v2 then 1
                  else -1)
            in
            let rec go = function
              | (_, t1) :: ((_, t2) :: _ as rest) ->
                  Atom.mk_app (Predicate.Psym lt) [ t1; t2 ] :: go rest
              | _ -> []
            in
            go sorted
          in
          match idx_s with
          | T_int.SInt -> chain T_int.Lt
          | T_real.SReal -> chain T_real.RLt
          | _ ->
              let rec pairs = function
                | (_, t1) :: rest ->
                    List.map rest ~f:(fun (_, t2) ->
                        Atom.mk_app (Predicate.Psym T_bool.Neq) [ t1; t2 ])
                    @ pairs rest
                | [] -> []
              in
              pairs representatives
        in
        Set.union other_satoms @@ Set.Poly.of_list
        @@ List.map (equivalence_class_atoms @ inter_atoms) ~f:(fun atom ->
            (atom, Set.Poly.empty))

  let target_var_elim model tvar satoms =
    match elim_eq model tvar satoms with
    | Some (model, satoms) -> (model, satoms)
    | None -> (model, satoms |> elim_neq model tvar |> ackermann model tvar)

  let diseq_atom tvar = function
    | Atom.App (Predicate.Psym T_bool.Neq, [ Term.Var (x, _, _); t ], _)
      when Ident.tvar_equal x tvar && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some t
    | Atom.App (Predicate.Psym T_bool.Neq, [ t; Term.Var (x, _, _) ], _)
      when Ident.tvar_equal x tvar && (not @@ Set.mem (Term.fvs_of t) x) ->
        Some t
    | _ -> None

  let elim_named ~print model y atoms =
    let atoms1, atoms2 =
      Set.partition_tf atoms ~f:(fun a -> Set.mem (Atom.fvs_of a) y)
    in
    if Set.is_empty atoms1 then atoms
    else
      let fallback () =
        let sub = Map.Poly.singleton y (Map.Poly.find_exn model y) in
        Set.union atoms2
        @@ Set.concat_map atoms1 ~f:(Atom.subst sub >> normalize_mbp model)
      in
      print
      @@ lazy
           (sprintf "[mbp arr] eliminating the named read %s"
              (Ident.name_of_tvar y));
      match Map.Poly.find model y with
      | None ->
          failwith
          @@ sprintf "[mbp arr] the model does not bind the named read %s"
               (Ident.name_of_tvar y)
      | Some v -> (
          try
            match Term.sort_of v with
            | T_bool.SBool ->
                Set.union atoms2
                  (Boolean.model_based_projection ~print model y atoms1)
            | T_int.SInt ->
                Set.union atoms2
                  (LIA.model_based_projection ~print model y atoms1)
            | T_real.SReal ->
                Set.union atoms2
                  (LRA.model_based_projection ~print model y atoms1)
            | T_bv.SBV _ ->
                Set.union atoms2
                  (BV.model_based_projection ~print model y atoms1)
            | T_dt.SDT _ ->
                Set.union atoms2
                  (ADT.model_based_projection ~print model y atoms1)
            | _ -> fallback ()
          with NotNormalized | Failure _ -> fallback ())

  let elim_all_named ~print model0 model atoms =
    Map.Poly.keys model
    |> List.filter ~f:(Map.Poly.mem model0 >> not)
    |> List.fold ~init:atoms ~f:(fun atoms y -> elim_named ~print model y atoms)

  let model_based_projection ~print model tvar atoms =
    (*
    let () =
      Stdlib.print_endline "--------------------------------------------------";
      Stdlib.print_endline ("::: [Array MBP] Target TVar (x): " ^ Ident.name_of_tvar tvar);
      let model_str = String.concat_map_list ~sep:", " (Map.Poly.to_alist model)
          ~f:(fun (Ident.Tvar v, value) -> Printf.sprintf "%s |-> %s" v (Term.str_of value)) in
      Stdlib.print_endline ("::: [Array MBP] Full Model: [" ^ model_str ^ "]");
      let atoms_str = String.concat ~sep:", " (List.map (Set.to_list atoms) ~f:Atom.str_of) in
      Stdlib.print_endline ("::: [Array MBP] Atoms: {" ^ atoms_str ^ "}");
      Stdlib.print_endline "--------------------------------------------------";
      Stdlib.flush Stdlib.stdout
    in
    *)
    match Set.find_map atoms ~f:(eq_atom tvar) with
    | Some t ->
        let sub = Map.Poly.singleton tvar t in
        Set.concat_map atoms ~f:(Atom.subst sub >> normalize_mbp model)
    | None ->
        (*TODO: Implement for constant arrays*)
        (*In the current implementation, if a constant is present, *)
        (*we give up on model-based projection and directly substitute.*)
        (*Warning: Inparticular, the situation changes if there is a constant around NEQ*)
        let rec contains_aconst t =
          match t with
          | Term.Var (_, _, _) -> false
          | Term.FunApp (sym, args, _) -> (
              match sym with
              | T_array.AConst (_, _) -> true
              | _ -> List.exists ~f:contains_aconst args)
          | Term.LetTerm (_, _, t1, t2, _) ->
              contains_aconst t1 || contains_aconst t2
        in

        (* The rules below drop a disequality [x <> t] on the eliminated array
           once its reads are named, which is exact only when some index lies
           outside every read and stored index, so that [x] can differ from [t]
           there, and the element sort has a second value to differ by.  A
           small index sort need not have such an index:
           [x[true] = y /\ x[false] = y /\ x <> t] projects to
           [t[true] <> y \/ t[false] <> y], and dropping the disequality left
           nothing.  Each [select] and [store] of the atoms constrains at most
           one index, so an index sort with more elements than there are of
           them has the room; otherwise the array is projected by substituting
           its model value, which is exact for the model and implies the
           existential. *)
        let may_lack_room =
          let constrained =
            Set.sum
              (module Int)
              atoms
              ~f:(fun atom ->
                Set.length
                @@ Formula.filtered_terms_of (Formula.mk_atom atom)
                     ~f:(fun t -> T_array.is_select t || T_array.is_store t))
          in
          Set.exists atoms ~f:(fun atom ->
              Set.exists (Atom.term_sort_env_of atom) ~f:(fun (y, s) ->
                  Ident.tvar_equal y tvar
                  &&
                  match s with
                  | T_array.SArray (idx_s, elem_s) ->
                      let k = constrained + 1 in
                      FinDom.card_upto [] idx_s k < k
                      || FinDom.card_upto [] elem_s 2 < 2
                  | _ -> false))
        in
        let by_value () =
          match Map.Poly.find model tvar with
          | Some value ->
              let sub = Map.Poly.singleton tvar value in
              Set.concat_map atoms ~f:(Atom.subst sub >> normalize_mbp model)
          | None ->
              failwith
              @@ sprintf
                   "[mbp arr] the model does not bind %s: model-based \
                    projection requires a model of its input"
                   (Ident.name_of_tvar tvar)
        in
        if
          may_lack_room
          || Set.exists atoms ~f:(fun atom ->
                 match atom with
                 | Atom.App (_, [ t1; t2 ], _) ->
                     contains_aconst t1 || contains_aconst t2
                 | _ -> false)
        then by_value ()
        else
          (*Equality with Sets*)
          let satoms = Set.Poly.map atoms ~f:(fun atom -> SAtom.of_atom atom) in
          (*
        let() =
          Stdlib.print_endline "--------------------------------------------------";
          let atoms = Set.Poly.map(satoms) ~f: (fun (atom, _) -> atom) in
          let atoms_str = String.concat ~sep:", " (List.map (Set.to_list atoms) ~f:Atom.str_of) in
          Stdlib.print_endline ("::: [Start Atoms] Atoms: {" ^ atoms_str ^ "}");
          Stdlib.flush Stdlib.stdout
        in
        *)

          (*Elim Write*)
          let elim_write_atoms = elim_write model satoms in
          (*
        let() =
          let atoms = Set.Poly.map(elim_write_atoms) ~f: (fun (atom, _) -> atom) in
          let atoms_str = String.concat ~sep:", " (List.map (Set.to_list atoms) ~f:Atom.str_of) in
          Stdlib.print_endline ("::: [Elim Write] Atoms: {" ^ atoms_str ^ "}");
          Stdlib.flush Stdlib.stdout
        in
        *)

          (*Factor out qualities and read terms*)
          let model', factor_out_atoms =
            factor_out model tvar elim_write_atoms
          in

          (*LiftEqDiseqRd*)
          (*We don't have to implement since we think formulas as a set of atomic formulas*)

          (*Target Variables Elimination*)
          let model', target_var_elim_atoms =
            target_var_elim model' tvar factor_out_atoms
          in
          (*
        let() =
          let atoms = Set.Poly.map(target_var_elim_atoms) ~f: (fun (atom, _) -> atom) in
          let atoms_str = String.concat ~sep:", " (List.map (Set.to_list atoms) ~f:Atom.str_of) in
          Stdlib.print_endline ("::: [Target Variables Elimination] Atoms: {" ^ atoms_str ^ "}");
          Stdlib.flush Stdlib.stdout
        in
        *)

          (*Output*)
          let out_atoms =
            Set.concat_map target_var_elim_atoms ~f:(fun satom ->
                normalize_mbp model' @@ SAtom.to_atom satom)
          in
          (*
        let() =
          let atoms_str = String.concat ~sep:", " (List.map (Set.to_list out_atoms) ~f:Atom.str_of) in
          Stdlib.print_endline ("::: [Output] Atoms: {" ^ atoms_str ^ "}");
          Stdlib.print_endline "--------------------------------------------------";
          Stdlib.flush Stdlib.stdout
        in
        *)
          let res = elim_all_named ~print model model' out_atoms in
          (* The rules above remove [tvar] only from the positions they read: an equation
             or disequation on it, a read of it, a store over it under a read or at the top
             of an (in)equation.  Anywhere else (an argument of an uninterpreted function,
             an array of arrays) it survives them, and a result that mentions the variable
             it was to eliminate is no projection; its model value is one. *)
          if Set.exists res ~f:(fun a -> Set.mem (Atom.fvs_of a) tvar) then
            by_value ()
          else res
end
