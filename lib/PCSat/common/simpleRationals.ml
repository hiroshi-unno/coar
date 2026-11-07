(* A teacher that prefers simple rationals in the real part of a
   counterexample.

   An arithmetic solver answers a satisfiable linear query with a vertex of
   the region the query describes, or a point an infinitesimal inside it, so
   the real values of a counterexample are ratios of the query's own
   coefficients.  When the query is a clause with a candidate substituted,
   those coefficients are the candidate's, which the synthesizer chose to fit
   the earlier examples, so they are ratios of the earlier examples' values:
   the counterexample of one round is built from the numbers of the round
   before.  On a piecewise-linear template over one real variable the rounds
   then refine a breakpoint by points that close in on it, each with about
   120 more digits than the last (11 to 1507 digits in 13 rounds on one QFL
   input), until a template question over those numbers no longer returns
   within its budget and the run stalls; a run whose solver happened to pick
   other vertices of the same regions kept every value under 160 digits and
   answered in 12 rounds.  Which run happens is decided by the solver's
   internal state, which the timing of the host's garbage collection moves.

   This replaces each real value whose denominator exceeds [max_den] by the
   simplest rational near it that keeps the query true -- the first among
   [floor v], [ceil v] and the continued-fraction convergents of [v], taken by
   increasing denominator, that the evaluator finds still makes [phi] true
   with the other values as they stand -- and then asks the query again with
   the real variables pinned to the values so chosen.  The convergents of [v]
   are the best approximations of [v] by rationals of no larger denominator,
   so when [v] lies inside the region (or on its boundary, with the region
   open on one side), a convergent of small denominator lies in it too.

   Contract: [reask] returns either [model] unchanged or a model the [ask]
   callback returned for [phi] conjoined with equalities fixing some of its
   real variables, so whatever it returns is a model of [phi] whenever [ask]
   answers models of the formula it is given -- a counterexample all the
   same.  The evaluator only proposes the values; the solver's answer to the
   pinned query is what is returned, so an evaluator that judged a candidate
   wrongly costs one question and changes nothing.  It only chooses WHICH
   counterexample is used, so it cannot change a verdict.  A model with no
   real value of denominator above [max_den], or no simpler value that the
   evaluator accepts, asks nothing.  No state is kept between calls. *)

open Core
open Common.Ext
open Ast
open Ast.LogicOld

type model = ((Ident.tvar * Sort.t) * Term.t option) list

(* the real value of a model entry, when the model gives it a numeral *)
let real_value = function
  | (_, T_real.SReal), Some t -> (
      match Term.value_of (Evaluator.simplify_term t) with
      | Value.Real q -> Some q
      | Value.Int z -> Some (Q.of_bigint z)
      | _ -> None
      | exception exn when not (Common.Timer.is_async exn) -> None)
  | _ -> None

(* [floor q], [ceil q] and the continued-fraction convergents of [q] whose
   denominators are below [q]'s, by increasing denominator (ties: nearer to
   [q] first).  Every element differs from [q].  At most 64 convergents are
   taken; their denominators grow at least as fast as the Fibonacci numbers,
   so the 64th already exceeds 2^43. *)
let simpler_candidates (q : Q.t) : Q.t list =
  let n = Q.num q and d = Q.den q in
  let fl = Z.fdiv n d in
  let base = [ Q.of_bigint fl; Q.of_bigint (Z.succ fl) ] in
  let rec convergents k (h1, k1) (h2, k2) (n, d) acc =
    (* h1/k1 the last convergent, h2/k2 the one before; n/d the remainder *)
    if k >= 64 || Z.equal d Z.zero then acc
    else
      let a = Z.fdiv n d in
      let h = Z.add (Z.mul a h1) h2 and kk = Z.add (Z.mul a k1) k2 in
      let c = Q.make h kk in
      if Z.geq kk (Q.den q) then acc
      else
        convergents (k + 1) (h, kk) (h1, k1) (d, Z.sub n (Z.mul a d)) (c :: acc)
  in
  let all = base @ convergents 0 (Z.one, Z.zero) (Z.zero, Z.one) (n, d) [] in
  List.dedup_and_sort all ~compare:(fun a b ->
      match Z.compare (Q.den a) (Q.den b) with
      | 0 -> Q.compare (Q.abs (Q.sub a q)) (Q.abs (Q.sub b q))
      | c -> c)
  |> List.filter ~f:(fun c -> not (Q.equal c q))

(* does [phi] evaluate to true under the values [sub] gives its variables?
   [false] when the evaluator does not reduce it to [true] *)
let holds sub phi =
  try Formula.is_true @@ Evaluator.simplify @@ Formula.subst sub phi
  with exn when not (Common.Timer.is_async exn) -> false

let reask ~(max_den : int) ~(ask : Formula.t -> model option) (phi : Formula.t)
    (model : model) : model =
  let max_den = Z.of_int (Int.max 1 max_den) in
  let complex =
    List.filter_map model ~f:(fun (((x, _), _) as e) ->
        match real_value e with
        | Some q when Z.gt (Q.den q) max_den -> Some (x, q)
        | _ -> None)
  in
  if List.is_empty complex then model
  else
    let sub0 =
      Map.Poly.of_alist_reduce ~f:(fun t _ -> t)
      @@ List.filter_map model ~f:(fun ((x, _), t) ->
          Option.map t ~f:(fun t -> (x, t)))
    in
    (* greedy, one variable at a time, the others at their current values *)
    let _sub, pinned =
      List.fold complex ~init:(sub0, []) ~f:(fun (sub, pinned) (x, q) ->
          match
            List.find (simpler_candidates q) ~f:(fun c ->
                holds (Map.Poly.set sub ~key:x ~data:(T_real.mk_real c)) phi)
          with
          | Some c ->
              ( Map.Poly.set sub ~key:x ~data:(T_real.mk_real c),
                (x, c) :: pinned )
          | None -> (sub, pinned))
    in
    if List.is_empty pinned then model
    else
      let pins =
        List.map pinned ~f:(fun (x, c) ->
            Formula.eq (Term.mk_var x T_real.SReal) (T_real.mk_real c))
      in
      match ask (Formula.and_of (phi :: pins)) with
      | Some model' ->
          Common.PhaseTime.event_here "pinned";
          model'
      | None ->
          Common.PhaseTime.event_here "kept";
          model
