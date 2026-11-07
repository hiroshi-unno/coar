open Core
open LogicOld

(* The rewrites a validity question may be given before it is asked, as one
   value a caller states, and the ones that are pure formula rewrites (no
   solver is called) applied here.  The rewrite that asks a solver (the factor
   equalities implied by a question's linear facts) is applied by the
   validity service, which has a solver.

   The rewrites of the first group are equivalences in every model that add
   no free variable, so the rewritten question is valid exactly when the
   original is, and a proof or a countermodel of one is one of the other; the
   two after them preserve validity only, and the last is a weakening read
   only as a proof (each group's contract is stated where it starts).  Each
   caller keeps its own switches and decides where in its route the rewrites
   run; this module fixes their order among themselves. *)

(* where integer binders are split at the thresholds of the [ite]s in their
   bodies ([IntBinderSplit]): [Off]; [Rewrite_question tally], the question
   itself rewritten (counted in [tally]); [In_solver_calls], the solver
   interface's own split ([Z3interface.with_split_int_binders]) in force
   around the caller's asks, applied there to each formula it is given *)
type int_binders = Off | Rewrite_question of IntBinderSplit.tally | In_solver_calls

type t = {
  onepoint : bool;
      (* the one-point rule, the binder splits and the singleton-range rule
         ([Evaluator.elim_onepoint_singleton_and_split_binders]) on a question
         that has a binder *)
  split_seq_reads : bool;
      (* reads of a concatenation split by the index
         ([Evaluator.split_seq_reads_for_validity]) *)
  prefix_over_concat : bool;
      (* [extract (a ++ b) 0 k] as a case split on [k <= len a]
         ([Evaluator.rewrite_seq_prefix_over_concat]) *)
  int_binders : int_binders;
  implied_factor_equalities : bool;
      (* the equations between factors of products that the question's linear
         facts imply, stated as disjuncts (asks a solver; applied by the
         validity service) *)
}

let none =
  {
    onepoint = false;
    split_seq_reads = false;
    prefix_over_concat = false;
    int_binders = Off;
    implied_factor_equalities = false;
  }

(* [phased name f] runs [f] as the phase [name] of the phase-time account when
   [phases] is set, and plainly otherwise *)
let phased ~phases name f =
  if phases then Common.PhaseTime.with_phase name f else f ()

(* [onepoint ?phases rw phi]: the one-point rewrite of [rw] on [phi] when it
   is on and [phi] has a quantifier (timed as [onepoint]); [phi] otherwise *)
let onepoint ?(phases = true) rw phi =
  if rw.onepoint && not (Formula.is_quantifier_free phi) then
    phased ~phases "onepoint" (fun () ->
        Evaluator.elim_onepoint_singleton_and_split_binders phi)
  else phi

(* [formula_rewrites ?phases rw phi]: the pure rewrites of [rw] other than the
   one-point rule, in this order: the read split ([split_seq_reads], timed as
   [split] whether or not it is on), the prefix split ([prefix_over_concat],
   timed as [prefix-concat]), the integer-binder split when it is
   [Rewrite_question] (timed as [int-binder-split]).  [In_solver_calls] is
   not applied here: the caller puts the solver interface's split in force. *)
let formula_rewrites ?(phases = true) rw phi =
  let phi =
    phased ~phases "split" (fun () ->
        if rw.split_seq_reads then Evaluator.split_seq_reads_for_validity phi
        else phi)
  in
  let phi =
    if rw.prefix_over_concat then
      phased ~phases "prefix-concat" (fun () ->
          Evaluator.rewrite_seq_prefix_over_concat phi)
    else phi
  in
  match rw.int_binders with
  | Rewrite_question tally ->
      phased ~phases "int-binder-split" (fun () ->
          IntBinderSplit.rewrite_at tally phi)
  | Off | In_solver_calls -> phi

(* The two rewrites below preserve VALIDITY, not equivalence in every model:
   [q] is valid exactly when [phi] is, while [q] and [phi] may differ in a
   single model (a free variable is fixed, a function symbol is added).  So a
   caller may read a proof of [q] as a proof of [phi], and a countermodel of
   [q] is not handed back as one of [phi] by anything here; the callers below
   read only a proof. *)

(* [name_bv_to_int phi]: every [bv_to_int_n t] (the integer value of an
   [n]-bit word, unsigned or signed) replaced by [u_n t] for a function
   symbol [u_n] of its own, and the definition of [u_n] made a premise:
   [Ax -> phi'] with [Ax] the conjunction, over the pairs (width, signedness)
   that occur, of [forall x. int_to_bv_n (u_n x) = x /\ lo <= u_n x < hi]
   ([lo, hi] = [0, 2^n] unsigned, [-2^(n-1), 2^(n-1)] signed).  [None] when
   [phi] has no such application.

   Contract: [Ax -> phi'] is valid iff [phi] is.  Proof.  [int_to_bv_n] is
   the remainder by [2^n] read as a word, so it is injective on any interval
   of [2^n] consecutive integers, and [bv_to_int_n x] is the unique integer
   of [[lo, hi)] that it sends to [x]; so a model satisfies [Ax] exactly when
   it interprets [u_n] as [bv_to_int_n] (both total, so no partiality enters).
   If [phi] is valid, a model of [Ax] gives [phi'] the value [phi] has in it,
   which is true; if [Ax -> phi'] is valid, any model extended with [u_n :=
   bv_to_int_n] satisfies [Ax], hence [phi'], which there is [phi].  Every
   application is replaced, under binders too: [u_n] is a function symbol, so
   no variable can be captured.  The definitions of the recursive functions
   in the environment keep [bv_to_int_n]; [Ax] says the two agree.

   Why: Z3 5.1.0 rewrites [bv2nat (bvor w c)] into a sum over extracts of
   [w] before [int2bv n (bv2nat .)] can collapse, and the [int2bv] of that sum
   stalls it (a bit read back from a word sequence updated by [bvor]: no
   answer at 60 s); with the conversion behind an uninterpreted symbol whose
   only link to the words is [Ax], the same question was proved in 6-8 s.
   The composition arises inside the solver, through a read of the updated
   sequence, so no rewrite of the question's own terms can collapse it. *)
let name_bv_to_int phi =
  let used = ref Map.Poly.empty in
  let symbol bits signed =
    let size = Some bits and sg = T_bv.is_signed signed in
    let name =
      sprintf "#%sbv_to_int_inverse%d" (if sg then "s" else "u") bits
    in
    let u = Ident.Tvar name in
    used := Map.Poly.set !used ~key:(bits, sg) ~data:(u, size);
    FVar (u, [ T_bv.SBV size ], T_int.SInt)
  in
  let phi' =
    Formula.map_term phi ~f:(function
      | Term.FunApp (T_irb.BVToInt (_, signed), [ t ], info) as app -> (
          (* the width is read off the argument's sort: the size annotation
             of the conversion itself may be absent (the default width) on a
             64-bit argument, and a symbol declared at the wrong width is a
             sort error in the solver.  An argument of unknown width is left
             as it is (the rewrite stays exact: fewer applications named). *)
          match Term.sort_of t with
          | T_bv.SBV (Some bits) ->
              Term.mk_fsym_app ~info (symbol bits signed) [ t ]
          | _ -> app)
      | t -> t)
  in
  if Map.Poly.is_empty !used then None
  else
    let axiom ((bits, sg), (u, size)) =
      let x = Ident.mk_fresh_tvar () in
      let sort = T_bv.SBV size in
      let xv = Term.mk_var x sort in
      let ux = Term.mk_fsym_app (FVar (u, [ sort ], T_int.SInt)) [ xv ] in
      let lo, hi =
        if sg then (Z.neg (Z.shift_left Z.one (bits - 1)), Z.shift_left Z.one (bits - 1))
        else (Z.zero, Z.shift_left Z.one bits)
      in
      Formula.forall [ (x, sort) ]
        (Formula.and_of
           [
             Formula.eq (T_irb.mk_int_to_bv ~size ux) xv;
             Formula.geq ux (T_int.mk_int lo);
             Formula.lt ux (T_int.mk_int hi);
           ])
    in
    Some
      (Formula.mk_imply
         (Formula.and_of (List.map (Map.Poly.to_alist !used) ~f:axiom))
         phi')

(* [pin_free_int_singletons phi]: the singleton-range rule (an integer that
   the constant bounds among the literals of its binder confine to one value
   is replaced by that value, [Evaluator.elim_onepoint_singleton_and_split_binders])
   applied to the free integer variables of a validity question as well,
   reading each as the universal it is: the rewrite is run on
   [forall xs. phi] for the free integer variables [xs], and the universals
   then left at the top of the result, along its conjunctions, are removed.
   [None] when no free integer variable disappears.

   Contract: the result is valid iff [phi] is.  Proof: [phi] is valid iff
   [forall xs. phi] is (a free variable of a validity question is read
   universally); the rewrite is an equivalence in every model; and for the
   removal, [A /\ B] is valid iff [A] and [B] are, and [forall y. B] iff [B]
   is -- each conjunct's validity is asked on its own, so two conjuncts may
   reuse a name.  The one-point rule and the binder splits of the same
   rewrite apply to [xs] too; each is an equivalence.

   Why: a free variable confined by its constant bounds is the case a bound
   one already gets; no question is known that it decides (the base case it
   was built for bounds its index from above in one disjunct only, so the
   index is not confined to one value). *)
let pin_free_int_singletons phi =
  let free =
    Set.to_list
    @@ Set.filter (Formula.term_sort_env_of phi) ~f:(fun (_, s) ->
        Stdlib.( = ) s T_int.SInt)
  in
  if List.is_empty free then None
  else
    let r =
      Evaluator.elim_onepoint_singleton_and_split_binders
        (Formula.mk_forall free phi)
    in
    let rec strip = function
      | Formula.BinaryOp (Formula.And, p, q, info) ->
          Formula.mk_binop ~info Formula.And (strip p) (strip q)
      | Formula.Bind (Formula.Forall, _, body, _) -> strip body
      | p -> p
    in
    let r = strip r in
    let left = Formula.tvs_of r in
    if List.exists free ~f:(fun (x, _) -> not (Set.mem left x)) then Some r
    else None

(* The rewrite below is a WEAKENING, read only as a proof: its result is
   implied by its argument, so an [unsat] of the result is an [unsat] of the
   argument, and nothing else may be read from it. *)

(* the most instances one universal is replaced by *)
let max_positions = 4

(* [int_universals_at_positions phi], for a formula [phi] whose
   UNSATISFIABILITY is asked (the negation of a validity question): each
   subformula of [nnf phi] reached through conjunctions and disjunctions
   only (no binder, no negation above it) of the form [forall xs. psi] with an integer variable [x] of [xs] that [psi] uses as a
   position (reads a sequence at an index mentioning [x]) and for which the
   rules below give positions is replaced by its instances
   [forall (xs - x). psi[k / x]] at those positions, the universal itself
   dropped (the first such [x] of [xs]).  [None] when no conjunct has a
   position.

   Positions, in this order, at most [max_positions] per universal:
   - a ground read: [phi] reads a sequence [s] whose variables are free in
     [phi] at an index [n] that folds to an integer numeral, and [psi] reads
     the same [s] (printed alike, not mentioning [x]) at [x], [x + d],
     [d + x], [x - d] or [div x c] for numerals [d] and [c > 0], or at an
     [ite] with such an index in a branch: the [k] that makes that index
     [n] ([n], [n - d], [n + d], [c n]; [div (c n) c = n] under every
     rounding mode);
   - a predecessor: [t - 1] for each integer argument [t] of an application
     of a function of the function environment in [phi] whose variables are
     all free in [phi] (a counted recursive function's step at counter [t]
     reads the position [t - 1]).

   Contract: the result is implied by [phi] in every model (an instance of a
   universal is implied by it, and conjunction and disjunction are monotone,
   so replacing a subformula reached through them alone by one it implies
   gives a formula the whole implies), so if the result is
   unsatisfiable, so is [phi].  A model of the result need not satisfy the
   dropped universal, so a caller reads only an [unsat] of it, as a proof of
   the question whose negation [phi] is.  Any position is sound; the rules
   only choose which instances are worth offering.  An instance's terms
   mention only variables free in [phi], so substituting one captures
   nothing ([Formula.subst] is capture-avoiding besides).

   Why: Z3 5.1.0 did not answer a membership question read after an
   insertion into an empty set with the set's zero-word premises kept
   (30 s), and answered it in 0.6-0.9 s with their instances at word 0 (the
   ground read) in their place.  The predecessor is the position a count's
   step reads (its bit at the counter minus one), at which a lemma about the
   count needs its bit-agreement premise. *)
let int_universals_at_positions phi =
  let phi = Formula.nnf_of phi in
  let free = Formula.tvs_of phi in
  let numeral i =
    if not (Set.is_empty (Term.tvs_of i)) then None
    else
      match
        try Some (Evaluator.simplify_term i)
        with exn_ when not (Common.Timer.is_async exn_) -> None
      with
      | Some (Term.FunApp (T_int.Int n, [], _)) -> Some n
      | _ -> None
  in
  let ground = Hashtbl.Poly.create () in
  Formula.iter_term phi ~f:(function
    | Term.FunApp (T_seq.SqNth _, [ s; i ], _)
      when Set.is_subset (Term.tvs_of s) ~of_:free -> (
        match numeral i with
        | Some n ->
            Hashtbl.update ground (Term.str_of s) ~f:(function
              | None -> [ n ]
              | Some ns -> if List.mem ns n ~equal:Z.equal then ns else n :: ns)
        | None -> ())
    | _ -> ());
  let fenv = get_fenv () in
  let predecessors = ref [] in
  Formula.iter_term phi ~f:(function
    | Term.FunApp (FVar (f, _, _), args, _)
      when Map.Poly.mem fenv f
           && List.for_all args ~f:(fun a ->
                  Set.is_subset (Term.tvs_of a) ~of_:free) ->
        List.iter args ~f:(fun a ->
            if Stdlib.( = ) (Term.sort_of a) T_int.SInt then
              let p = T_int.mk_sub a (T_int.one ()) in
              if
                not
                  (List.exists !predecessors ~f:(fun q ->
                       String.equal (Term.str_of q) (Term.str_of p)))
              then predecessors := p :: !predecessors)
    | _ -> ());
  let predecessors = List.rev !predecessors in
  if Hashtbl.is_empty ground && List.is_empty predecessors then None
  else
    let num = function Term.FunApp (T_int.Int d, [], _) -> Some d | _ -> None in
    let positions x psi =
      let is_x = function
        | Term.Var (y, _, _) -> Ident.tvar_equal x y
        | _ -> false
      in
      let rec solve e n =
        match e with
        | _ when is_x e -> [ n ]
        | Term.FunApp (T_int.Add, [ a; b ], _) when is_x a ->
            Option.to_list (Option.map (num b) ~f:(fun d -> Z.sub n d))
        | Term.FunApp (T_int.Add, [ a; b ], _) when is_x b ->
            Option.to_list (Option.map (num a) ~f:(fun d -> Z.sub n d))
        | Term.FunApp (T_int.Sub, [ a; b ], _) when is_x a ->
            Option.to_list (Option.map (num b) ~f:(fun d -> Z.add n d))
        | Term.FunApp (T_int.Div _, [ a; b ], _) when is_x a -> (
            match num b with
            | Some c when Z.gt c Z.zero -> [ Z.mul c n ]
            | _ -> [])
        | Term.FunApp (T_bool.IfThenElse, [ _; a; b ], _) ->
            (* either branch may be the one the read takes *)
            solve a n @ solve b n
        | _ -> []
      in
      let acc = ref [] in
      let add k =
        let key = Term.str_of k in
        if
          (not
             (List.exists !acc ~f:(fun q -> String.equal (Term.str_of q) key)))
          && List.length !acc < max_positions
        then acc := k :: !acc
      in
      let read_at_x = ref false in
      Formula.iter_term psi ~f:(function
        | Term.FunApp (T_seq.SqNth _, [ s; e ], _)
          when not (Set.mem (Term.tvs_of s) x) -> (
            if Set.mem (Term.tvs_of e) x then read_at_x := true;
            match Hashtbl.find ground (Term.str_of s) with
            | None -> ()
            | Some ns ->
                List.iter (List.rev ns) ~f:(fun n ->
                    List.iter (solve e n) ~f:(fun k -> add (T_int.mk_int k))))
        | _ -> ());
      if !read_at_x then List.iter predecessors ~f:add;
      List.rev !acc
    in
    let changed = ref false in
    let rewrite c =
      match c with
      | Formula.Bind (Formula.Forall, bounds, psi, _) -> (
          match
            List.find_map bounds ~f:(fun (x, s) ->
                if Stdlib.( = ) s T_int.SInt then
                  match positions x psi with [] -> None | ks -> Some (x, ks)
                else None)
          with
          | None -> c
          | Some (x, ks) ->
              changed := true;
              let rest =
                List.filter bounds ~f:(fun (y, _) -> not (Ident.tvar_equal x y))
              in
              Formula.and_of
                (List.map ks ~f:(fun k ->
                     let inst = Formula.subst (Map.Poly.singleton x k) psi in
                     if List.is_empty rest then inst
                     else Formula.mk_forall rest inst)))
      | c -> c
    in
    let rec go = function
      | Formula.BinaryOp (((Formula.And | Formula.Or) as op), p, q, info) ->
          Formula.mk_binop ~info op (go p) (go q)
      | c -> rewrite c
    in
    let r = go phi in
    if !changed then Some r else None
