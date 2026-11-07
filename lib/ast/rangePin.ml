(* Pin the width of a bounded integer existential and expand it into its
   instances.

   WHAT.  [pin ~width phi] looks, in the positive positions of [phi] (under
   [not], [and], [or] and [=>], polarity tracked; nothing inside a binder,
   [<=>], [xor], [let] or a recursive definition), for a block [exists x. B]
   binding one integer [x] whose body's top-level conjunction holds a lower
   bound [x >= lo] and an upper bound [x < hi] -- comparisons of [x] with
   coefficient one or minus one, read by [IntBinderSplit.atom_threshold], so
   [lo] and [hi] are free of [x].  Each such block is replaced by
   [B[x := lo] \/ .. \/ B[x := lo + width - 1]] and the equation
   [hi = lo + width] is collected.  The result is [Some (pins, phi')] when at
   least one block was replaced, [None] otherwise.  Requires [width >= 1].

   CLAIM.  In every model in which every pin holds, [phi'] is equivalent to
   [phi]: the range [lo <= x < hi] then has exactly the elements
   [lo .. lo + width - 1], and [B] implies the range, so [exists x. B] is the
   disjunction of [B] at those elements.  Positive positions only are
   rewritten, so the equivalence propagates to the whole formula.  Hence a
   model of [pins /\ not phi'] is a model of [not phi] -- a countermodel to the
   validity of [phi].  Nothing is claimed in the other direction: that
   [pins => phi'] is valid says nothing about [phi], so only a countermodel of
   the pinned question may be read.  Substitution is capture-avoiding, so a
   binder inside [B] does not capture a variable of [lo].

   WHY.  A validity question with such an existential has, in its negation, a
   universal [forall x. lo <= x < hi => not B]; over a body that reads bits of
   sequence elements through [int_to_bv], [div] and [mod], Z3 (5.1.0) left the
   negation undecided at 30 s while the width [hi - lo] was free, and answered
   [sat] in 0.1 s once [hi = lo + k] was asserted (any [k] from 1 to 64),
   whereas an inequality [hi - lo <= 4] was still undecided.  A validation
   question left undecided learns nothing, so a CEGIS loop that meets one with
   every candidate proposes the same candidate again. *)
open Core
open Common.Ext
open LogicOld

let rec conjuncts phi =
  match phi with
  | Formula.BinaryOp (Formula.And, p, q, _) -> conjuncts p @ conjuncts q
  | _ -> [ phi ]

(* [Some (lo, hi)] when a conjunct of [body] is [x >= lo] and another is
   [x < hi], the first of each kind *)
let bounds_of x body =
  let cs = conjuncts body in
  let find upper =
    List.find_map cs ~f:(fun c ->
        match IntBinderSplit.atom_threshold x c with
        | Some (t, is_upper) when Bool.(is_upper = upper) -> Some t
        | _ -> None)
  in
  match (find false, find true) with
  | Some lo, Some hi -> Some (lo, hi)
  | _ -> None

let pin ~width phi =
  if width < 1 then None
  else
    let pins = ref [] in
    let rec tr pos phi =
      match phi with
      | Formula.UnaryOp (Formula.Not, p, info) ->
          Formula.mk_neg ~info (tr (not pos) p)
      | Formula.BinaryOp (((Formula.And | Formula.Or) as op), p, q, info) ->
          Formula.mk_binop ~info op (tr pos p) (tr pos q)
      | Formula.BinaryOp (Formula.Imply, p, q, info) ->
          Formula.mk_imply ~info (tr (not pos) p) (tr pos q)
      | Formula.Bind (Formula.Exists, [ (x, s) ], body, _)
        when pos && Term.is_int_sort s -> (
          match bounds_of x body with
          | None -> phi
          | Some (lo, hi) ->
              pins :=
                Formula.eq hi (T_int.mk_add lo (T_int.mk_int (Z.of_int width)))
                :: !pins;
              Formula.or_of
              @@ List.init width ~f:(fun i ->
                  Formula.subst
                    (Map.Poly.singleton x
                       (T_int.mk_add lo (T_int.mk_int (Z.of_int i))))
                    body))
      | _ -> phi
    in
    let phi' = tr true phi in
    match !pins with [] -> None | ps -> Some (List.rev ps, phi')

(* [Some q] where [q] is [pins => phi'] for [pin ~width phi]; a countermodel
   of [q] is one of [phi] (see the claim above) *)
let pinned_question ~width phi =
  Option.map (pin ~width phi) ~f:(fun (pins, phi') ->
      Formula.mk_imply (Formula.and_of pins) phi')

(* GROUND RANGES.  [expand_ground ~max_width phi] replaces, everywhere in
   [phi] (bottom-up, inside binders too), a block [exists x. B] binding one
   integer [x] whose body's top-level conjunction holds [x >= lo] and
   [x < hi], and a block [forall x. B] whose body's top-level disjunction
   holds [x < lo] and [x >= hi], with [lo] and [hi] simplifying to integer
   numerals and [hi - lo <= max_width], by the disjunction (the conjunction)
   of [B] at [lo .. hi - 1] ([false] / [true] for an empty range).  Each
   replacement is an equivalence in every model, since the integers are the
   same in all of them, so the result means what [phi] means and an answer
   about it is one about [phi].  Why: a truth-table cell asking whether an
   example's two sequences disagree on a bit of the range [1, 2) was left
   undecided by Z3 at budgets of 2 s and more as a quantified question, and
   decided in 0.3 s as its one instance. *)
let rec disjuncts phi =
  match phi with
  | Formula.BinaryOp (Formula.Or, p, q, _) -> disjuncts p @ disjuncts q
  | _ -> [ phi ]

let numeral t =
  let t = Evaluator.simplify_term t in
  if T_int.is_int t then Some (T_int.let_int t) else None

(* [Some (lo, hi)] when parts of [ps] bound [x] as below: [lower] reads the
   part giving [lo], [upper] the part giving [hi] *)
let ground_range ~max_width x ps ~lo_is_upper =
  let find want =
    List.find_map ps ~f:(fun c ->
        match IntBinderSplit.atom_threshold x c with
        | Some (t, is_upper) when Bool.(is_upper = want) -> numeral t
        | _ -> None)
  in
  match (find lo_is_upper, find (not lo_is_upper)) with
  | Some lo, Some hi when Z.(leq (hi - lo) (of_int max_width)) -> Some (lo, hi)
  | _ -> None

let expand_ground ~max_width phi =
  let instances x body lo hi =
    let n = max 0 (Z.to_int (Z.sub hi lo)) in
    List.init n ~f:(fun i ->
        Formula.subst
          (Map.Poly.singleton x (T_int.mk_int (Z.add lo (Z.of_int i))))
          body)
  in
  let rec tr phi =
    match phi with
    | Formula.UnaryOp (Formula.Not, p, info) -> Formula.mk_neg ~info (tr p)
    | Formula.BinaryOp (op, p, q, info) ->
        Formula.mk_binop ~info op (tr p) (tr q)
    | Formula.Bind (b, senv, body, info) -> (
        let body = tr body in
        match (b, senv) with
        | Formula.Exists, [ (x, s) ] when Term.is_int_sort s -> (
            (* [x >= lo] reads as not-upper, [x < hi] as upper *)
            match
              ground_range ~max_width x (conjuncts body) ~lo_is_upper:false
            with
            | Some (lo, hi) -> Formula.or_of (instances x body lo hi)
            | None -> Formula.mk_bind ~info b senv body)
        | Formula.Forall, [ (x, s) ] when Term.is_int_sort s -> (
            (* the disjunct [x < lo] reads as upper, [x >= hi] as not-upper *)
            match
              ground_range ~max_width x (disjuncts body) ~lo_is_upper:true
            with
            | Some (lo, hi) -> Formula.and_of (instances x body lo hi)
            | None -> Formula.mk_bind ~info b senv body)
        | _ -> Formula.mk_bind ~info b senv body)
    | _ -> phi
  in
  tr phi

(* The width [expand_ground] is applied at in truth-table cells and
   validation questions; [None] (the default): not applied.  A process-wide
   cell rather than a parameter because the truth table's cell evaluation is
   reached from the labeler and the synthesizer through no configuration of
   its own, which is why its sibling switches (the ground evaluation of
   recursive qualifiers) are process-wide cells too.  Set once, by the PCSat
   solver's construction before any solving domain exists, and only ever
   from [None] to [Some]; a nested solve whose configuration leaves it unset
   keeps the enclosing run's width.  Being an equivalence, a stale width can
   change only which questions are decided, never an answer. *)
let ground_expansion_width : int option Atomic.t = Atomic.make None
let set_ground_expansion_width w = Atomic.set ground_expansion_width w

(* [expand_ground] at the configured width, the identity when none is *)
let expand_ground_configured phi =
  match Atomic.get ground_expansion_width with
  | Some max_width when not (Formula.is_quantifier_free phi) ->
      expand_ground ~max_width phi
  | _ -> phi
