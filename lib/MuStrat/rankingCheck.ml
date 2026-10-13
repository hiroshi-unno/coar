(* Whether a ranking a strategy check substitutes is transitive.

   A ranking key of the disjunctively well-founded reduction denotes a relation
   [W(a, b)] between a remembered copy [a] of a state and the current state
   [b]: its parameters are the copy followed by the state, with the same sorts
   in the same order.  Every ranking the refinement builds is a finite union of
   pieces, each a bounded decreasing measure and so well-founded, which makes
   [W] disjunctively well-founded.  A transitive disjunctively well-founded
   relation is well-founded: an infinite descending chain would put every pair
   of its elements in [W], and Ramsey's theorem, colouring those pairs by the
   piece that holds them, yields an infinite chain inside one piece
   (Podelski and Rybalchenko, "Transition invariants", LICS 2004).  A won
   check whose rankings are well-founded is a sound answer, while a merely
   disjunctively well-founded ranking can be satisfied by choices that read
   the copy, so this is the test that separates the two. *)

open Core
open Common.Ext
open Common.Combinator
open Ast

(* [Ok ()] when Z3 proves [W(a, b) /\ W(b, c) => W(a, c)] valid for the relation
   the lambda term [t] denotes, within [timeout_ms]; [Error reason] whenever it
   is not proved: invalid, unknown, a timeout, a formula the solver may not
   return on, or a term that is not a lambda over a copy followed by a state of
   the same sorts.  So [Ok] is a proof and [Error] claims nothing beyond its
   reason.  [transitive] is its boolean form.  Pure apart
   from the solver call; [t] is closed except for its lambda parameters. *)
let check ?(timeout_ms = 1000) t =
  try
    let args, body = Logic.Term.let_lam t in
    let n = List.length args in
    if n % 2 <> 0 then Error (sprintf "%d parameters, not a copy and a state" n)
    else
      let xs, ys = List.split_n args (n / 2) in
      if
        not
          (List.equal Stdlib.( = ) (List.map xs ~f:snd) (List.map ys ~f:snd))
      then Error "the copy's sorts differ from the state's"
      else
        let zs = Logic.mk_fresh_sort_env_list (List.map ys ~f:snd) in
        (* simultaneous substitution of the parameters; [zs] is fresh, so no
           replacement is captured *)
        let app a b =
          Logic.ExtTerm.subst
            (Map.Poly.of_alist_exn
               (List.zip_exn (List.map args ~f:fst)
                  (List.map (a @ b) ~f:(fst >> Logic.ExtTerm.mk_var))))
            body
        in
        let phi =
          Logic.BoolTerm.imply_of
            (Logic.BoolTerm.and_of [ app xs ys; app ys zs ])
            (app xs zs)
        in
        (* A synthesised ranking can hold a template's selector term (a
           [case] over the candidate linear pieces with a constant index),
           which the solver interface does not encode; simplification resolves
           it to the selected piece, as it does before the strategy is
           printed or compared. *)
        let phi =
          Evaluator.simplify
          @@ Logic.ExtTerm.to_old_fml Map.Poly.empty
               (Map.Poly.of_alist_exn (args @ zs))
               phi
        in
        if Z3Smt.Z3interface.may_not_return phi then
          Error "the transitivity query may not return"
        else
          match
            Z3Smt.Z3interface.check_valid ~timeout:(Some timeout_ms) ~id:None
              (LogicOld.get_fenv ()) phi
          with
          | `Valid -> Ok ()
          | `Invalid _ -> Error "not transitive (Z3 found a counter-model)"
          | `Unknown r -> Error ("Z3 answered unknown: " ^ r)
          | `Timeout -> Error "Z3 timed out"
          | `Sat _ | `Unsat -> Error "Z3 answered a satisfiability verdict"
  with exn when not (Common.Timer.is_async exn) ->
    Error ("raised " ^ Exn.to_string exn)

let transitive ?timeout_ms t = Result.is_ok (check ?timeout_ms t)

(* Whether the relation [region] between the integer states [xs] and [ys]
   (the upper and the lower visit of a chain pair, same length) has a linear
   ranking: [Some true] when Z3 finds integer coefficients [c] and a constant
   [c0] with [region(x, y) => c.x - c.y >= 1 /\ c.x + c0 >= 0] for all [x],
   [y]; [Some false] when Z3 proves there are none; [None] when it does not
   decide within [timeout_ms], when a state is not of integer sort, or when a
   conjunct of the region is not a linear comparison.  The question is asked
   through Farkas' lemma, so it is a linear, quantifier-free query.

   A region is asked of a ranking relation [R] as [R ⊇ region], and [R] must
   be well-founded, so a region that is not well-founded makes the whole
   re-synthesis unsatisfiable and its budget is spent for nothing.  Model-based
   projection of a chain segment can drop the bound that made the play's chain
   finite -- "the state decreases by one" with no floor -- which is exactly
   such a region.  [Some false] therefore marks a region worth dropping: a
   linear ranking is the complete test for well-foundedness of a conjunction
   of linear constraints over the rationals (Podelski and Rybalchenko, "A
   complete method for the synthesis of linear ranking functions", VMCAI
   2004), and over the integers it is sufficient only, so dropping on
   [Some false] can drop a region with a non-linear or lexicographic ranking.
   That costs at most a region, never soundness, since regions only add
   demands to the ranking search and the strategy check certifies every
   answer. *)
let region_has_linear_ranking ?(timeout_ms = 1000) xs ys region =
  let open LogicOld in
  try
    let zs = xs @ ys in
    if
      List.length xs <> List.length ys
      || List.exists zs ~f:(fun (_, s) -> not (Term.is_int_sort s))
    then None
    else
      (* The region as rows [a . z <= b] over the integers.  Each conjunct is
         a linear comparison; its coefficients are read by evaluation (the
         value at 0 and at each unit vector) and the affine reading is
         confirmed at one more point, so a non-linear conjunct gives up. *)
      let eval_at assign t =
        let env =
          Map.Poly.of_alist_exn
            (List.map zs ~f:(fun (v, _) ->
                 (v, Value.Int (Z.of_int (Option.value ~default:0 (List.Assoc.find assign v ~equal:Stdlib.( = )))))))
        in
        Value.int_of (Evaluator.eval_term ~env t)
      in
      let affine t =
        let k0 = eval_at [] t in
        let ks = List.map zs ~f:(fun (v, _) -> Z.(eval_at [ (v, 1) ] t - k0)) in
        let at2 =
          eval_at (List.map zs ~f:(fun (v, _) -> (v, 2))) t
        in
        if Z.equal at2 Z.(k0 + (of_int 2 * List.fold ks ~init:zero ~f:( + ))) then
          Some (ks, k0)
        else None
      in
      let rows_of phi =
        if Formula.is_true phi then Some []
        else if not (Formula.is_atom phi) then None
        else
          match fst (Formula.let_atom phi) with
          | Atom.App (Predicate.Psym sym, [ t1; t2 ], _) -> (
              match affine (T_int.mk_sub t1 t2) with
              | None -> None
              | Some (ks, k0) ->
                  let neg = List.map ks ~f:Z.neg in
                  (* d = ks . z + k0 *)
                  let le = (ks, Z.neg k0) and ge = (neg, k0) in
                  if Stdlib.( = ) sym T_int.Leq then Some [ le ]
                  else if Stdlib.( = ) sym T_int.Lt then Some [ (ks, Z.(neg k0 - one)) ]
                  else if Stdlib.( = ) sym T_int.Geq then Some [ ge ]
                  else if Stdlib.( = ) sym T_int.Gt then Some [ (neg, Z.(k0 - one)) ]
                  else if Stdlib.( = ) sym T_bool.Eq then Some [ le; ge ]
                  else None)
          | _ -> None
      in
      match Option.all (List.map (Formula.conjuncts_list_of region) ~f:rows_of) with
      | None -> None
      | Some rowss ->
          let rows = List.concat rowss in
          let n = List.length xs in
          let int_var () = Term.mk_var (Ident.mk_fresh_tvar ~prefix:(Some "RC_") ()) T_int.SInt in
          let cs = List.init n ~f:(fun _ -> int_var ()) in
          let l1 = List.map rows ~f:(fun _ -> int_var ()) in
          let l2 = List.map rows ~f:(fun _ -> int_var ()) in
          let dot ls col =
            T_int.mk_sum (T_int.zero ())
              (List.map2_exn ls rows ~f:(fun l (ks, _) ->
                   T_int.mk_mul (T_int.mk_int (List.nth_exn ks col)) l))
          in
          let beta ls =
            T_int.mk_sum (T_int.zero ())
              (List.map2_exn ls rows ~f:(fun l (_, b) -> T_int.mk_mul (T_int.mk_int b) l))
          in
          (* Farkas: [region => -c.x + c.y <= -1] and [region => -c.x <= c0]
             hold for a feasible region iff there are multipliers
             [l1, l2 >= 0] with [l1 . A = (-c, c)], [l1 . b <= -1] and
             [l2 . A = (-c, 0)] ([c0] then exists).  Scaling by a positive
             integer keeps every constraint, so integer unknowns are
             equisatisfiable with rational ones and the query is linear. *)
          let nonneg = List.map (l1 @ l2) ~f:(fun l -> Formula.geq l (T_int.zero ())) in
          let cols =
            List.concat
            @@ List.init n ~f:(fun j ->
                   let c = List.nth_exn cs j in
                   [
                     Formula.eq (dot l1 j) (T_int.mk_neg c);
                     Formula.eq (dot l1 (n + j)) c;
                     Formula.eq (dot l2 j) (T_int.mk_neg c);
                     Formula.eq (dot l2 (n + j)) (T_int.zero ());
                   ])
          in
          let phi =
            Formula.and_of
              ((Formula.leq (beta l1) (T_int.mk_int Z.minus_one) :: nonneg) @ cols)
          in
          match
            Z3Smt.Z3interface.check_sat ~timeout:(Some timeout_ms) ~id:None
              (get_fenv ()) [ phi ]
          with
          | `Sat _ -> Some true
          | `Unsat -> Some false
          | _ -> None
  with exn when not (Common.Timer.is_async exn) -> None
