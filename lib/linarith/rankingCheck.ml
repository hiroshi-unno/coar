(* Linear ranking constructions over regions of pairs of states, shared by
   MuStrat's strategy checks and PCSat's synthesiser for well-founded
   unknowns ([WfLp]), and the transitivity test a strategy check applies.

   Whether a ranking a strategy check substitutes is transitive.

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
   from the solver call; [t] is closed except for its lambda parameters.
   With [~direct:true] the query reaches Z3 without the simplifier: the
   template's selector is resolved by [Logic.select_constant_cases] (exact by
   the definition of [case]), the formula is converted and asked as it is,
   with no other rewrite on the proof's path. *)
let check ?(timeout_ms = 1000) ?(direct = false) t =
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
          if direct then
            Logic.ExtTerm.to_old_fml Map.Poly.empty
              (Map.Poly.of_alist_exn (args @ zs))
              (Logic.select_constant_cases phi)
          else
            Evaluator.simplify
            @@ Logic.ExtTerm.to_old_fml Map.Poly.empty
                 (Map.Poly.of_alist_exn (args @ zs))
                 phi
        in
        if Z3Smt.Z3interface.may_not_return phi then
          Error "the transitivity query may not return"
        else if direct then
          match
            Z3Smt.Z3interface.check_sat_with_preds ~timeout:(Some timeout_ms)
              ~id:None (LogicOld.get_fenv ()) [ LogicOld.Formula.mk_neg phi ]
          with
          | `Unsat -> Ok ()
          | `Sat -> Error "not transitive (Z3 found a counter-model)"
          | `Unknown -> Error "Z3 answered unknown or timed out"
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

(* The rows a region is read as are [Rows]'s, and the Farkas statements over
   them [Farkas]'s; included (the statements by name) so that every caller
   keeps these names. *)
include Rows

module Num = Farkas.Num

let farkas_rows = Farkas.farkas_rows

(* Whether the relation [region] between the integer or real states [xs] and
   [ys] (the upper and the lower visit of a chain pair, same length) has a
   linear ranking: [Some true] when Z3 finds coefficients [c] and a constant
   [c0] with [region(x, y) => c.x - c.y >= 1 /\ c.x + c0 >= 0] for all [x],
   [y] read over the rationals; [Some false] when Z3 proves there are none;
   [None] when it does not decide within [timeout_ms], when a state is of
   neither sort, or when a conjunct of the region is not a linear
   comparison.  The question is asked
   through Farkas' lemma, so it is a linear, quantifier-free query.

   A region is asked of a ranking relation [R] as [R ⊇ region], and [R] must
   be well-founded, so a region that is not well-founded makes the whole
   re-synthesis unsatisfiable and its budget is spent for nothing.  Model-based
   projection of a chain segment can drop the bound that made the play's chain
   finite -- "the state decreases by one" with no floor -- which is exactly
   such a region.  [Some false] therefore marks a region worth dropping: a
   linear ranking is a sufficient certificate of well-foundedness, over both
   rational and integer states. The complete synthesis of linear ranking
   functions (Podelski and Rybalchenko, "A complete method for the synthesis
   of linear ranking functions", VMCAI 2004) does not decide general
   well-foundedness. Dropping on [Some false] can therefore drop a
   well-founded region with a multiphase or non-linear ranking, even over
   the rationals.
   That costs at most a region, never soundness, since regions only add
   demands to the ranking search and the strategy check certifies every
   answer. *)
let region_has_linear_ranking ?(timeout_ms = 1000) xs ys region =
  let open LogicOld in
  try
    match region_rows xs ys region with
    | None -> None
    | Some rows ->
          let n = List.length xs in
          let int_var () = Term.mk_var (Ident.mk_fresh_tvar ~prefix:(Some "RC_") ()) T_int.SInt in
          let cs = List.init n ~f:(fun _ -> int_var ()) in
          let l1 = Farkas.combination ~prefix:"RC_" rows in
          let l2 = Farkas.combination ~prefix:"RC_" rows in
          (* Farkas: [region => -c.x + c.y <= -1] and [region => -c.x <= c0]
             hold for a feasible region iff there are multipliers
             [l1, l2 >= 0] with [l1 . A = (-c, c)], [l1 . b <= -1] and
             [l2 . A = (-c, 0)] ([c0] then exists).  Scaling by a positive
             integer keeps every constraint, so integer unknowns are
             equisatisfiable with rational ones and the query is linear. *)
          let nonneg = l1.nonneg @ l2.nonneg in
          let cols =
            List.concat
            @@ List.init n ~f:(fun j ->
                   let c = List.nth_exn cs j in
                   [
                     Formula.eq (l1.column j) (T_int.mk_neg c);
                     Formula.eq (l1.column (n + j)) c;
                     Formula.eq (l2.column j) (T_int.mk_neg c);
                     Formula.eq (l2.column (n + j)) (T_int.zero ());
                   ])
          in
          let phi =
            Formula.and_of
              ((Formula.leq l1.bound (T_int.mk_int Z.minus_one) :: nonneg) @ cols)
          in
          match
            (* only satisfiability is read *)
            Z3Smt.Z3interface.with_model_unread (fun () ->
                Z3Smt.Z3interface.check_sat ~timeout:(Some timeout_ms) ~id:None
                  (get_fenv ()) [ phi ])
          with
          | `Sat _ -> Some true
          | `Unsat -> Some false
          | _ -> None
  with exn when not (Common.Timer.is_async exn) -> None

(* [region_nested_ranking ~depth xs ys region]: whether the relation [region]
   between the states [xs] (the earlier visit) and [ys] (the later one) has a
   nested ranking function of depth [depth] in the sense of Ben-Amram and
   Genaim, "On Multiphase-Linear Ranking Functions" (CAV 2017): affine
   functions [f_1 .. f_d] of one state with, for every pair [(x, y)] of the
   region read over the rationals,
     [f_d(x) >= 0]  and  [f_i(x) - f_i(y) - 1 + f_(i-1)(x) >= 0]  (i = 1..d),
   where [f_0 = 0].  At depth 1 this is the linear ranking
   [region_has_linear_ranking] asks for.

   Answers [`Ranking fs], each component its integer coefficients over the
   positions of [xs] and an integer constant; [`Infeasible] when Z3 proves no
   such functions of this depth exist (over the rationals, so the region may
   still have an integer-only or deeper ranking); [`Undecided] when the region
   cannot be read as linear rows (see [region_rows]), when [depth < 1], or
   when Z3 does not decide within [timeout_ms].

   Each implication [region => linear inequality] is asked through the affine
   form of Farkas' lemma, which is exact for a non-empty region (a region
   holds at the play's pair, so it is non-empty): one vector of non-negative
   multipliers per implication, linear in the unknown coefficients, so the
   query is one linear program.  Scaling every unknown by a positive integer
   keeps every constraint ([k (c - 1) <= k c - 1]), so integer unknowns are
   equisatisfiable with rational ones.

   What a [`Ranking] is worth: whatever the components are, the relation
   [template_order] builds from them is well-founded, so a wrong model costs
   at most a candidate that fails to cover the region.  The functions are
   only claimed to rank the region if Z3's model is right. *)
let region_nested_ranking ?(timeout_ms = 1000) ~depth xs ys region =
  let open LogicOld in
  try
    if depth < 1 then `Undecided
    else
      match region_rows xs ys region with
      | None -> `Undecided
      | Some rows ->
          let n = List.length xs in
          let fresh () = Ident.mk_fresh_tvar ~prefix:(Some "RN_") () in
          (* components 1..d: coefficient variables and a constant variable *)
          let comps =
            List.init depth ~f:(fun _ ->
                ( List.init n ~f:(fun _ -> (fresh (), T_int.SInt)),
                  (fresh (), T_int.SInt) ))
          in
          let var (v, s) = Term.mk_var v s in
          let zero = T_int.zero () in
          let coef i j =
            (* [c_i] at column [j], with [c_0 = 0] *)
            if i = 0 then zero else var (List.nth_exn (fst (List.nth_exn comps (i - 1))) j)
          in
          let const i =
            if i = 0 then zero else var (snd (List.nth_exn comps (i - 1)))
          in
          (* [region => a . z <= beta] through multipliers [ls >= 0] with
             [ls . A = a] and [ls . b <= beta]; [a] given per column *)
          let farkas a beta =
            let c = Farkas.combination ~prefix:"RN_" rows in
            (Formula.leq c.bound beta :: c.nonneg)
            @ List.init (2 * n) ~f:(fun col -> Formula.eq (c.column col) (a col))
          in
          (* [f_d(x) >= 0], i.e. [-c_d . x <= c_(d,0)] *)
          let bounded =
            farkas
              (fun col -> if col < n then T_int.mk_neg (coef depth col) else zero)
              (const depth)
          in
          (* [(-c_i - c_(i-1)) . x + c_i . y <= c_(i-1,0) - 1] *)
          let steps =
            List.concat
            @@ List.init depth ~f:(fun k ->
                   let i = k + 1 in
                   farkas
                     (fun col ->
                       if col < n then
                         T_int.mk_neg (T_int.mk_add (coef i col) (coef (i - 1) col))
                       else coef i (col - n))
                     (T_int.mk_sub (const (i - 1)) (T_int.one ())))
          in
          let phi = Formula.and_of (bounded @ steps) in
          match
            Z3Smt.Z3interface.check_sat ~timeout:(Some timeout_ms) ~id:None
              (get_fenv ()) [ phi ]
          with
          | `Sat model ->
              (* read by name and sort: an entry a pooled context holds at
                 another sort says nothing about this coefficient *)
              let value (v, s) =
                match model_find model (v, s) with
                | Some t -> (
                    match
                      Evaluator.eval_term (snd (remove_dontcare_elem ((v, s), t)))
                    with
                    | Value.Int z -> z
                    | _ -> raise Exit)
                | None -> Z.zero
              in
              `Ranking
                (List.map comps ~f:(fun (cs, c0) ->
                     (List.map cs ~f:value, value c0)))
          | `Unsat -> `Infeasible
          | _ -> `Undecided
  with exn when not (Common.Timer.is_async exn) -> `Undecided

(* [template_order xs ys fs]: the relation, between the states [xs] (the
   earlier, the copy) and [ys] (the later), of the single-piece lexicographic
   ranking over the components [fs] (each its integer coefficients over the
   state positions and an integer constant):
     OR_k [ f_k(x) >= 0 /\ f_k(x) >= f_k(y) + 1
            /\ AND_(l<k) ((f_l(x) <= -1 /\ f_l(y) <= -1) \/ f_l(x) >= f_l(y)) ]
   This is exactly the ranking template's decrease relation with one piece,
   the components as its lexicographic components and a trivially true
   discriminator, built with the same comparisons ([>= +1] for strictness),
   so it is well-founded for any [fs]: [c(t) := max(t, -1)] maps each
   disjunct to a bounded lexicographic decrease of [c . f].  It is also
   transitive (the same map makes it a strict lexicographic order on the
   images), over integer and real states alike.
   Pre: [xs] and [ys] have the length of every component's coefficients, and
   are integer or real terms.  States are read as reals when any of them is
   real (an integer state is cast), as integers otherwise.  Raises on a list
   length mismatch. *)
let template_order xs ys fs =
  let open LogicOld in
  let num_sort =
    if List.for_all (xs @ ys) ~f:(fun t -> Term.is_int_sort (Term.sort_of t))
    then T_int.SInt
    else T_real.SReal
  in
  let affine ts (cs, c0) =
    if Stdlib.( = ) num_sort T_int.SInt then
      T_int.mk_sum (T_int.mk_int c0)
        (List.map2_exn cs ts ~f:(fun c t -> T_int.mk_mul (T_int.mk_int c) t))
    else
      T_real.mk_rsum
        (T_real.mk_real (Q.of_bigint c0))
        (List.map2_exn cs ts ~f:(fun c t ->
             T_real.mk_rmul
               (T_real.mk_real (Q.of_bigint c))
               (T_irb.cast (Term.sort_of t, num_sort) t)))
  in
  let r_x = List.map fs ~f:(affine xs) and r_y = List.map fs ~f:(affine ys) in
  let zero = T_irb.zero_of num_sort in
  Formula.or_of
  @@ List.init (List.length fs) ~f:(fun k ->
         Formula.and_of
         @@ (Formula.mk_atom @@ T_irb.geq_of num_sort (List.nth_exn r_x k) zero)
            :: T_irb.gt_of num_sort (List.nth_exn r_x k) (List.nth_exn r_y k)
            :: List.init k ~f:(fun l ->
                   Formula.or_of
                     [
                       Formula.and_of
                         [
                           T_irb.gt_of num_sort zero (List.nth_exn r_x l);
                           T_irb.gt_of num_sort zero (List.nth_exn r_y l);
                         ];
                       Formula.mk_atom
                       @@ T_irb.geq_of num_sort (List.nth_exn r_x l)
                            (List.nth_exn r_y l);
                     ]))

(* [exceeds_bound b (cs, c0)]: whether the affine function's coefficients'
   absolute values sum to more than [b], or its constant's absolute value is
   above [b] -- the two measures the constraint solver's ranking template
   bounds (a sum over the coefficients, and the constant), so a function
   for which this holds is outside the template's bounds while they are
   [b]. *)
let exceeds_bound b (cs, c0) =
  Z.gt (List.fold cs ~init:Z.zero ~f:(fun acc c -> Z.add acc (Z.abs c))) b
  || Z.gt (Z.abs c0) b

(* [largest_literal phis]: the largest absolute value of an integer literal
   in the formulas [phis], at least 1.  A formula whose symbols cannot be
   collected (a [let rec] inside it) contributes nothing, so the result is a
   lower bound on the largest literal and never raises except
   asynchronously. *)
let largest_literal phis =
  let open LogicOld in
  List.fold phis ~init:Z.one ~f:(fun acc phi ->
      match Formula.funsyms_of phi with
      | syms ->
          Set.fold syms ~init:acc ~f:(fun acc -> function
            | T_int.Int z -> Z.max acc (Z.abs z)
            | _ -> acc)
      | exception exn when not (Common.Timer.is_async exn) -> acc)

(* [const_ladder ~first ~literal]: the rungs [lex_ranking ~const_first] asks
   for a component's constant: [first]; then [literal] (the problem's largest
   literal, see [largest_literal]) when it is given and above [first].  The
   rungs increase, so a later one is asked only where a tighter one found
   nothing; the unbounded question after them is [lex_ranking]'s. *)
let const_ladder ~first ?literal () =
  match literal with
  | Some m when Z.gt m first -> [ first; m ]
  | _ -> [ first ]

(* [str_of_components fs]: the components of a nested ranking for a trace,
   each as an affine function of the state positions [x1 .. xn]. *)
let str_of_components fs =
  "("
  ^ String.concat_map_list ~sep:", " fs ~f:(fun (cs, c0) ->
        let terms =
          List.filter_mapi cs ~f:(fun j c ->
              if Z.equal c Z.zero then None
              else if Z.equal c Z.one then Some (sprintf "x%d" (j + 1))
              else Some (sprintf "%s*x%d" (Z.to_string c) (j + 1)))
        in
        let terms =
          if Z.equal c0 Z.zero && not (List.is_empty terms) then terms
          else terms @ [ Z.to_string c0 ]
        in
        String.concat ~sep:" + " terms)
  ^ ")"

(* [int_model ~timeout_ms phis]: a model of the conjunction [phis] read as a
   function from an integer variable to its value ([0] for a variable the
   model leaves out, which Z3 does only for a variable whose value does not
   matter); [None] when Z3 answers anything but [sat] within [timeout_ms] or
   a value is not an integer.  Only the model's INTEGER-sorted entries are
   read: the function is asked about integer variables, and an entry of
   another sort -- left in a pooled solver context by an earlier query that
   used the same name -- says nothing about one. *)
let int_of_model model =
  let open LogicOld in
  try
    let tbl =
      List.filter_map model ~f:(fun (((x, s), _) as e) ->
          if not (Term.is_int_sort s) then None
          else
            match Evaluator.eval_term (snd (remove_dontcare_elem e)) with
            | Value.Int z -> Some (x, z)
            | _ -> raise Exit)
    in
    Some
      (fun v ->
        Option.value ~default:Z.zero
          (List.find_map tbl ~f:(fun (x, z) ->
               if Ident.tvar_equal x v then Some z else None)))
  with Exit -> None

(* [int_model] reads its answer with [int_of_model], [rat_model] with
   [rat_of_model]; [lex_ranking ~base_session] reads a session's answer with
   them too. *)
let int_model ?(id = None) ~timeout_ms phis =
  let open LogicOld in
  match
    Z3Smt.Z3interface.check_sat ~timeout:(Some timeout_ms) ~id
      (get_fenv ()) [ Formula.and_of phis ]
  with
  | `Sat model -> int_of_model model
  | _ -> None

(* [rat_model ~timeout_ms phis]: [int_model] for a question whose unknowns
   are reals: a model read as a function from a variable to its rational
   value ([0] for one the model leaves out); [None] unless Z3 answers [sat]
   within [timeout_ms] and every value is a number.  Only the model's
   integer- and real-sorted entries are read, as in [int_of_model]. *)
let rat_of_model model =
  let open LogicOld in
  try
    let tbl =
      List.filter_map model ~f:(fun (((x, s), _) as e) ->
          if not (Term.is_int_sort s || Term.is_real_sort s) then None
          else
            match Evaluator.eval_term (snd (remove_dontcare_elem e)) with
            | Value.Int z -> Some (x, Q.of_bigint z)
            | Value.Real q -> Some (x, q)
            | _ -> raise Exit)
    in
    Some
      (fun v ->
        Option.value ~default:Q.zero
          (List.find_map tbl ~f:(fun (x, q) ->
               if Ident.tvar_equal x v then Some q else None)))
  with Exit -> None

let rat_model ?(id = None) ~timeout_ms phis =
  let open LogicOld in
  match
    Z3Smt.Z3interface.check_sat ~timeout:(Some timeout_ms) ~id
      (get_fenv ()) [ Formula.and_of phis ]
  with
  | `Sat model -> rat_of_model model
  | _ -> None

(* [scale_to_integers (cs, c0)]: the affine function multiplied by the least
   common multiple [L >= 1] of its entries' denominators, so integer-valued.
   Multiplying by [L] keeps the sign of the function at every point, keeps
   [f(x) - f(y) >= 0], and turns [f(x) - f(y) >= 1] into [>= L >= 1], so a
   component that ranks a region (or does not increase on it) still does,
   over integer and real states alike. *)
let scale_to_integers (cs, c0) =
  let l = List.fold (c0 :: cs) ~init:Z.one ~f:(fun l q -> Z.lcm l (Q.den q)) in
  let int_of q = Q.num Q.(q * of_bigint l) in
  (List.map cs ~f:int_of, int_of c0)

(* The questions [lex_ranking ~base_session] asked against a session's base.
   Printed to stderr at exit when COAR_LEX_SESSION_COUNT is set; it is what
   proves a run read the switch, and a test reads it to see the switch act. *)
let session_asks = ref 0

let () =
  match Sys.getenv "COAR_LEX_SESSION_COUNT" with
  | None | Some "" -> ()
  | Some _ ->
      Stdlib.at_exit (fun () ->
          Stdlib.prerr_endline
          @@ sprintf "lex-session: questions asked against a base %d" !session_asks)

(* With COAR_CONST_RUNG_COUNT set, the answers of questions asked with
   constant rungs ([lex_ranking ~const_first]) are counted by the rung that
   answered (the first two rungs, then any later one), with the questions no
   rung answered and the free question then answered, printed to stderr at
   exit: "const-rungs: rung1 A rung2 B later C free D none E".  A diagnostic
   only; the counts are not synchronised across domains. *)
let const_rung_counts = [| 0; 0; 0; 0; 0 |]

let () =
  match Sys.getenv "COAR_CONST_RUNG_COUNT" with
  | None | Some "" -> ()
  | Some _ ->
      Stdlib.at_exit (fun () ->
          let c = const_rung_counts in
          Stdlib.prerr_endline
          @@ sprintf "const-rungs: rung1 %d rung2 %d later %d free %d none %d"
               c.(0) c.(1) c.(2) c.(3) c.(4))

(* With COAR_DUMP_LEX_RANKING=<file> set, each [lex_ranking] question set is
   appended to <file> as one line, read back by the measurement tool that
   compares the integer and the rational forms of the same questions:
     [n depth bound direct | region ; region ...], a region being its rows
   [k1,k2,..:b] separated by spaces, [bound] [-] for none.  Without the
   variable nothing is written. *)
let dump_lex_question ~n ~depth ~coef_bound ~direct_points regions =
  match Sys.getenv "COAR_DUMP_LEX_RANKING" with
  | None | Some "" -> ()
  | Some file -> (
      try
        let row (ks, b) =
          String.concat ~sep:"," (List.map ks ~f:Z.to_string) ^ ":" ^ Z.to_string b
        in
        let region rows = String.concat ~sep:" " (List.map rows ~f:row) in
        let line =
          sprintf "%d %d %s %b | %s\n" n depth
            (match coef_bound with None -> "-" | Some b -> Z.to_string b)
            direct_points
            (String.concat ~sep:" ; " (List.map regions ~f:region))
        in
        Out_channel.with_file ~append:true file ~f:(fun oc ->
            Out_channel.output_string oc line)
      with exn when not (Common.Timer.is_async exn) -> ())

(* [lex_ranking ~depth ~n regions]: affine functions [f_1 .. f_k] of one state
   ([k <= depth]) such that every region of [regions] (each given as
   [region_rows] over a copy and a state of [n] positions) is ranked by one
   component in the lexicographic sense: for some [i], [f_i(x) >= 0] and
   [f_i(x) >= f_i(y) + 1] on the whole region, and [f_l(x) >= f_l(y)] on the
   whole region for every [l < i].  Each component is its integer
   coefficients over the positions and an integer constant.

   Built level by level, as the greedy construction of lexicographic linear
   ranking functions over a set of transition polyhedra does (the scheme of
   Alias, Darte, Feautrier and Gonnord, SAS 2010, and of Ben-Amram and Genaim's
   synthesis of such functions; both *unverified* as sources here): a level
   asks for one affine function that does not increase on any region still
   to be ranked, and that decreases by at least 1 from a value at least 0 on
   as many of them as it can; those leave, and the next level ranks the
   rest.  "As many as it can" is approximated greedily -- first all of them
   in one question, then the regions one at a time in their given order,
   each kept when it can be added to the ones kept so far -- so the set a
   level takes is maximal, not necessarily maximum.  Each question is one
   linear query through [farkas_rows]; integer unknowns are equisatisfiable
   with rational ones, since scaling every unknown by a positive integer
   keeps every constraint.  With [coef_bound = b] every coefficient (not the
   constant) is also held within [-b, b], which makes each question an
   integer program and prefers components over few positions: where the
   regions are slices of a loop whose single linear ranking needs a
   coefficient growing with the slices (x1 + k x3 for growing k), the
   bounded construction finds the lexicographic order (x3, x1) the growth
   tends to.

   A region's rows may have more than [2 n] columns: the columns past the
   two states are existential in the region (an example's parameters), and
   [farkas_rows] states each implication with coefficient 0 there.

   [None] when some level ranks no region, when [depth] levels do not
   suffice, when a region's rows have fewer than [2 n] columns, or when a
   question raises.  An undecided question is read as "no", which can only
   lose a candidate.  At most [depth * (m + 1)] questions are asked for [m]
   regions.

   [timeout_ms] does not bound every question.  Z3 5.1.0 can stay in its
   simplex on a large Farkas question -- each pivot slower than the last as
   the tableau's rationals grow -- with neither its timeout nor a resource
   limit stopping it: the unit-bound question over 40 point regions of six
   positions (about 2,900 integer unknowns) answers in about a second on
   most of the solver's random states and does not return on a few, and
   which state a pooled solver is in moves with the OCaml collector.  The
   direct form of a point region ([direct_points]) asks a few unknowns
   instead; a caller that must not hang on a large non-point set asks in a
   killed copy ([ForkedQuery]).

   Two options restrict the construction to or past its first question, the
   one that asks a single component to rank every region at once: with
   [first_ask_only] only that question is asked, and the answer is the one
   component or [None]; with [skip_first_ask] that question is taken as
   answered "no" and not asked, for a caller that has just asked it (with
   the same [coef_bound]), so the rest of the construction is asked exactly
   as it would be after a "no".

   [direct_points] is [farkas_rows]': a region that is one integer point
   (a ground chain pair) is asked by one inequality per implication, with
   the same answers.

   With [const_bound = b] every component's constant is also held within
   [-b, b].

   With [const_first = [b_1; ...; b_k]] (the rungs of a ladder, normally
   increasing) each question is asked first with the component's constant
   held within [-b_1, b_1]; only when that finds no component, within
   [-b_2, b_2]; and so on, and without any such bound only when every rung
   has found none.  The same questions are decided (a bounded answer is an
   answer to the unbounded question, and the unbounded question is asked
   last), so the levels rank the same regions up to undecided questions;
   what changes is which component is returned.  A region is often bounded
   on a position only because the plays it was read from were (a branch
   such as [x <= 34] on their path), and an unbounded question can then
   answer [33 - y] where [x - y] ranks the same region: the constant
   memorises that bound, and the component fails on the first play beyond
   it, a play the checks may need many steps to reach.  A small constant can
   only come from the coefficients, so the component ranks by relations
   between positions where some does.  A caller's ladder [[1; m]], with [m]
   the largest absolute integer literal of the problem the regions were
   read from, adds a middle rung: a constant within the problem's own
   literals is one a guard of the problem can state (a loop bound [8 - i]),
   while a constant beyond every literal can only come from the values the
   plays or examples happened to take.  Each rung costs one more question
   only where the rung before it found nothing.  With the rational form the
   bound holds of the constant before scaling, that is, relative to the
   decrease of 1 every strict condition asks.  [[]] is the construction
   without the argument.

   With [rational] every unknown of a question is a real, so each question is
   a linear program over the rationals (where Farkas' lemma needs no integer
   multiplier and is exact for a non-empty region), and a component found is
   scaled to integer coefficients ([scale_to_integers]), which keeps every
   condition it was asked for.  Without [coef_bound] and [const_bound] the
   rational and the integer form of each question are satisfiable together:
   every constraint is homogeneous in the unknowns (multipliers,
   coefficients, constant) except the decrease bound [<= -1], so multiplying
   a rational solution by the least common multiple [L >= 1] of its
   denominators gives an integer one ([<= -L <= -1]), and an integer solution
   is a rational one.  A fractional Farkas multiplier is then absorbed by
   scaling the coefficients with it, and the construction takes the same
   steps in either form (up to undecided questions); only the components, a
   model's, may differ.  With [coef_bound] or [const_bound] the rational
   question bounds the rational unknowns before scaling, a different
   restriction from the integer one, which it can answer where the integer
   one cannot.  [scale] (a test's mutant only) replaces [scale_to_integers] on
   the rational form's model.

   With [integral] (read only with [rational]) the coefficients and the
   constant are required to be integers while the Farkas multipliers stay
   rational: a mixed question whose components need no scaling, so a
   coefficient bound holds of the components returned.  It decides more than
   the integer form under the same bound, whose integer multipliers miss an
   implication such as [64 y <= 64 x - 61 => 2 x - 2 y >= 1] (multiplier
   1/32), and exactly the bounded question over integer coefficients.

   With [base_session] each level's questions are asked in one solver
   holding the level's base (the bounds and every remaining region's
   non-increase), converted and asserted once, each question adding its
   strict conditions in a scope: the same questions, asked incrementally, so
   only the models and what is decided within [timeout_ms] can differ.
   [session_drop_base] (a test's mutant only) leaves the base out of the
   session.

   What an answer is worth: whatever the components are, [template_order]
   on them is well-founded, so a wrong model costs at most a candidate that
   fails to contain a region; the caller checks containment independently. *)
let lex_ranking ?(id = None) ?(timeout_ms = 1000) ?(rational = false)
    ?(scale = scale_to_integers) ?(integral = false) ?coef_bound ?const_bound ?const_first ?(skip_first_ask = false) ?(first_ask_only = false)
    ?(direct_points = false) ?(base_session = false) ?(session_drop_base = false)
    ~depth ~n regions =
  let num = if rational then Num.real_num else Num.int_num in
  let farkas_rows = farkas_rows ~num ~direct_points in
  let open LogicOld in
  dump_lex_question ~n ~depth ~coef_bound ~direct_points regions;
  Common.PhaseTime.with_phase "lex-ranking" @@ fun () ->
  try
    if
      depth < 1
      || List.exists regions
           ~f:(List.exists ~f:(fun (ks, _) -> List.length ks < 2 * n))
    then None
    else
      let zero = Num.zero num in
      (* one solver for every level's session, reset by each level's base *)
      let session_obj = lazy (Z3Smt.Z3interface.base_session_create ~id ()) in
      let rec level k remaining acc =
        if List.is_empty remaining then Some (List.rev acc)
        else if k > depth then None
        else
          let fresh () = Ident.mk_fresh_tvar ~prefix:(Some "RX_") () in
          let cs = List.init n ~f:(fun _ -> fresh ()) and c0 = fresh () in
          let c j = Term.mk_var (List.nth_exn cs j) num.sort in
          (* [-c . x + c . y], the coefficients of [f(y) - f(x)] *)
          let delta col = if col < n then num.neg (c col) else c (col - n) in
          let nonincreasing (_, rows) = farkas_rows ~n rows delta zero in
          let strict (_, rows) =
            farkas_rows ~n rows delta (num.of_z Z.minus_one)
            @ farkas_rows ~n rows
                (fun col -> if col < n then num.neg (c col) else zero)
                (Term.mk_var c0 num.sort)
          in
          let bounds =
            match coef_bound with
            | None -> []
            | Some b ->
                List.concat_map cs ~f:(fun v ->
                    let t = Term.mk_var v num.sort in
                    [ Formula.leq t (num.of_z b); Formula.geq t (num.of_z (Z.neg b)) ])
          in
          let bounds =
            match const_bound with
            | None -> bounds
            | Some b ->
                let t = Term.mk_var c0 num.sort in
                bounds
                @ [ Formula.leq t (num.of_z b); Formula.geq t (num.of_z (Z.neg b)) ]
          in
          let bounds =
            if integral && rational then
              bounds
              @ List.map (c0 :: cs) ~f:(fun v ->
                  Formula.mk_atom (T_irb.mk_is_int (Term.mk_var v num.sort)))
            else bounds
          in
          let base =
            Common.PhaseTime.with_phase "lp-build" (fun () ->
                bounds @ List.concat_map remaining ~f:nonincreasing)
          in
          (* [base_session]: the level's base (the bounds and every remaining
             region's non-increase) is converted to Z3 and asserted once, in
             a solver of its own, and each question asserts only its strict
             conditions in a scope ([Z3interface.base_session_check]).  Each
             question is the conjunction it is without the switch, so an
             answer is one Z3 gives to the same question; only the solver it
             is asked in (incremental, holding the base) and so the model and
             what is decided within [timeout_ms] can differ.  A base the
             session refuses (a non-empty function environment) is asked as
             before. *)
          let session =
            if base_session then
              let s = Lazy.force session_obj in
              let fenv = get_fenv () in
              if
                Common.PhaseTime.with_phase "lp-session" (fun () ->
                    Z3Smt.Z3interface.base_session_set ~id s fenv
                      (if session_drop_base then [] else base))
              then Some (s, fenv)
              else None
            else None
          in
          let const_rungs =
            List.map (Option.value const_first ~default:[]) ~f:(fun b ->
                let t = Term.mk_var c0 num.sort in
                [ Formula.leq t (num.of_z b); Formula.geq t (num.of_z (Z.neg b)) ])
          in
          let ask_once ~extra ranked =
            let read model =
              if rational then
                Option.map (rat_of_model model) ~f:(fun m ->
                    scale (List.map cs ~f:m, m c0))
              else
                Option.map (int_of_model model) ~f:(fun m ->
                    (List.map cs ~f:m, m c0))
            in
            match session with
            | Some (s, fenv) -> (
                let ext =
                  Common.PhaseTime.with_phase "lp-build" (fun () ->
                      Formula.and_of (extra @ List.concat_map ranked ~f:strict))
                in
                session_asks := !session_asks + 1;
                Common.PhaseTime.with_phase "lp-ask" (fun () ->
                    match
                      Z3Smt.Z3interface.base_session_check ~id s
                        ~timeout:(Some timeout_ms) fenv ext
                    with
                    | `Sat model -> read model
                    | _ -> None))
            | None ->
                let phis =
                  Common.PhaseTime.with_phase "lp-build" (fun () ->
                      base @ extra @ List.concat_map ranked ~f:strict)
                in
                Common.PhaseTime.with_phase "lp-ask" (fun () ->
                    if rational then
                      Option.map (rat_model ~id ~timeout_ms phis) ~f:(fun m ->
                          scale (List.map cs ~f:m, m c0))
                    else
                      Option.map (int_model ~id ~timeout_ms phis) ~f:(fun m ->
                          (List.map cs ~f:m, m c0)))
          in
          let ask ranked =
            if List.is_empty const_rungs then ask_once ~extra:[] ranked
            else
              let bump i =
                const_rung_counts.(i) <- const_rung_counts.(i) + 1
              in
              match
                List.find_mapi const_rungs ~f:(fun i extra ->
                    Option.map (ask_once ~extra ranked) ~f:(fun m -> (i, m)))
              with
              | Some (i, m) ->
                  bump (Int.min i 2);
                  Some m
              | None -> (
                  match ask_once ~extra:[] ranked with
                  | Some m ->
                      bump 3;
                      Some m
                  | None ->
                      bump 4;
                      None)
          in
          let component f = f in
          let first =
            if k = 1 && skip_first_ask then None else ask remaining
          in
          match first with
          | Some m -> Some (List.rev (component m :: acc))
          | None when k = 1 && first_ask_only -> None
          | None -> (
              let ranked, model =
                List.fold remaining ~init:([], None) ~f:(fun (s, m) r ->
                    match ask (r :: s) with
                    | Some m' -> (r :: s, Some m')
                    | None -> (s, m))
              in
              match model with
              | None -> None
              | Some m ->
                  level (k + 1)
                    (List.filter remaining ~f:(fun (i, _) ->
                         not (List.exists ranked ~f:(fun (j, _) -> i = j))))
                    (component m :: acc))
      in
      level 1 (List.mapi regions ~f:(fun i r -> (i, r))) []
  with exn when not (Common.Timer.is_async exn) -> None

(* [lex_ranking_small_first ~bounds ?bounded ~unbounded]: the first
   construction among [bounded b] for [b] in [bounds] (in order) that finds
   components, tagged [Some b]; when none does, [unbounded ()] tagged [None].

   [bounded] defaults to [lex_ranking ~coef_bound:b] over the same regions
   with integer coefficients and rational multipliers ([~rational ~integral],
   depth [depth]), and [unbounded] is the caller's
   construction without a bound.  So the components returned carry every
   coefficient within [-b, b] for the [b] tagged, and no smaller bound of
   [bounds] found any; with [None] every bound failed and the answer is the
   unbounded construction's.  Each construction is asked at most once, the
   unbounded one only when every bounded one has answered [None].  Whatever is
   returned, [template_order] on it is well-founded (see [lex_ranking]); the
   point of asking small bounds first is only which components are chosen,
   since the unbounded question has no objective and its model's magnitudes
   are the solver's choice. *)
let lex_ranking_small_first ?(id = None) ?(timeout_ms = 1000)
    ?(direct_points = false) ?bounded ~bounds ~unbounded ~depth ~n regions =
  let bounded =
    match bounded with
    | Some f -> f
    | None ->
        fun b ->
          lex_ranking ~id ~timeout_ms ~direct_points ~rational:true
            ~integral:true ~coef_bound:(Z.of_int b) ~depth ~n regions
  in
  match
    List.find_map bounds ~f:(fun b ->
        Option.map (bounded b) ~f:(fun fs -> (Some b, fs)))
  with
  | Some r -> Some r
  | None -> Option.map (unbounded ()) ~f:(fun fs -> (None, fs))

(* [fixed_value rows col]: [Some v] when [rows] contain [z_col <= v] and
   [-z_col <= -v] as rows of their own, i.e. the region fixes the position
   [col] to [v] syntactically; [None] otherwise (the region may still fix it
   through a combination of rows). *)
let fixed_value rows col =
  let unit_at sign (ks, _) =
    List.for_alli ks ~f:(fun j k ->
        if j = col then Z.equal k sign else Z.equal k Z.zero)
  in
  List.find_map rows ~f:(fun ((_, b) as row) ->
      if
        unit_at Z.one row
        && List.exists rows ~f:(fun ((_, b') as row') ->
               unit_at Z.minus_one row' && Z.equal b' (Z.neg b))
      then Some b
      else None)

(* [piecewise_ranking ~n ~is_int regions]: a ranking with two pieces split on
   one integer position [p] of the state at a threshold [t] -- the piece
   [z_p <= t] ranked by an affine [f_1], the piece [z_p >= t + 1] by an
   affine [f_2] -- such that for every region (as [region_rows] over a copy
   and a state of [n] positions) and every piece [j] the later state may be
   in, with [i] the piece of the earlier state:
     [f_i(x) >= 0  /\  f_i(x) >= f_j(y) + 1]  on the region within piece [j].
   Only a position every region fixes syntactically at the earlier state
   ([fixed_value]) and that [is_int] accepts is split on, so that the
   earlier piece of each region is known and the two pieces cover every
   integer value; the thresholds tried are the values the regions fix, at
   both states, in increasing order, all but the largest.  One linear query
   per position and threshold, through [farkas_rows] ([direct_points] as
   there).

   Answers [Some (p, t, f_1, f_2)] for the first that is feasible; [None]
   otherwise, when a region's rows do not have [2 n] columns, or when a
   question raises.

   What an answer is worth: [template_order_pieces] on the two pieces is an
   instance of the ranking template with two pieces, one lexicographic
   component each and the discriminators [t - z_p >= 0] and
   [z_p - t - 1 >= 0], so it is well-founded whatever the functions are;
   the caller checks containment independently. *)
let piecewise_ranking ?(timeout_ms = 1000) ?(direct_points = false) ~n ~is_int
    regions =
  let farkas_rows = farkas_rows ~direct_points in
  let open LogicOld in
  try
    if
      List.is_empty regions
      || List.exists regions
           ~f:(List.exists ~f:(fun (ks, _) -> List.length ks <> 2 * n))
    then None
    else
      let zero = T_int.zero () in
      let positions =
        List.filter (List.init n ~f:Fn.id) ~f:(fun p ->
            is_int p
            && List.for_all regions ~f:(fun rows ->
                   Option.is_some (fixed_value rows p)))
      in
      List.find_map positions ~f:(fun p ->
          let values =
            List.concat_map regions ~f:(fun rows ->
                List.filter_opt [ fixed_value rows p; fixed_value rows (n + p) ])
            |> List.dedup_and_sort ~compare:Z.compare
          in
          let thresholds = List.drop_last values |> Option.value ~default:[] in
          List.find_map thresholds ~f:(fun t ->
              let piece v = if Z.leq v t then 0 else 1 in
              let fresh () = Ident.mk_fresh_tvar ~prefix:(Some "RP_") () in
              let comps =
                List.init 2 ~f:(fun _ ->
                    (List.init n ~f:(fun _ -> fresh ()), fresh ()))
              in
              let c i j =
                Term.mk_var (List.nth_exn (fst (List.nth_exn comps i)) j) T_int.SInt
              in
              let k i = Term.mk_var (snd (List.nth_exn comps i)) T_int.SInt in
              (* the later state in piece [j], as a row over [z] *)
              let unit sign =
                List.init (2 * n) ~f:(fun col ->
                    if col = n + p then sign else Z.zero)
              in
              let in_piece j =
                if j = 0 then (unit Z.one, t) else (unit Z.minus_one, Z.(neg (t + one)))
              in
              let constraints =
                List.concat_map regions ~f:(fun rows ->
                    let i = piece (Option.value_exn (fixed_value rows p)) in
                    List.concat_map [ 0; 1 ] ~f:(fun j ->
                        match fixed_value rows (n + p) with
                        | Some v when piece v <> j -> []
                        | _ ->
                            let rows = rows @ [ in_piece j ] in
                            farkas_rows ~n rows
                              (fun col ->
                                if col < n then T_int.mk_neg (c i col) else zero)
                              (k i)
                            @ farkas_rows ~n rows
                                (fun col ->
                                  if col < n then T_int.mk_neg (c i col)
                                  else c j (col - n))
                                (T_int.mk_sub
                                   (T_int.mk_sub (k i) (k j))
                                   (T_int.one ()))))
              in
              match int_model ~timeout_ms constraints with
              | None -> None
              | Some m ->
                  let comp (cs, c0) = (List.map cs ~f:m, m c0) in
                  Some
                    ( p,
                      t,
                      comp (List.nth_exn comps 0),
                      comp (List.nth_exn comps 1) )))
  with exn when not (Common.Timer.is_async exn) -> None

(* [template_order_pieces xs ys pieces]: the ranking template's decrease
   relation over pieces [(disc, fs)], each a discriminator [disc] (a list of
   affine atoms [cs . z + c0 >= 0] over one state, read as their
   conjunction) and lexicographic components [fs] (all pieces with the same
   number), between the earlier state [xs] and the later [ys]:
     (OR_j D_j(y)) /\ OR_i [ D_i(x) /\ AND_j (D_j(y) => ldec(i, j)) ]
     ldec(i, j) = OR_k [ r_ik(x) >= 0 /\ r_ik(x) >= r_jk(y) + 1
                         /\ AND_(l<k) ((r_il(x) <= -1 /\ r_jl(y) <= -1)
                                       \/ r_il(x) >= r_jl(y)) ]
   which is the template's instance with these discriminators, components
   and selections.  It is well-founded for any discriminators and
   components: along a descending chain, map each state to the clamped
   components [max(r, -1)] of a piece it is in; each step then decreases
   that vector in a bounded lexicographic order.  It is also transitive,
   like one piece: [ldec(i, j)] is that order between piece [i]'s vector at
   [x] and piece [j]'s at [y], it is asked of every piece holding at [y],
   and the order is transitive, so a piece of [x] above every piece of [y],
   and a piece of [y] above every piece of [z], put the first above every
   piece of [z].  Same sort conventions and preconditions as
   [template_order]; raises on a length mismatch or pieces of different
   component counts. *)
let template_order_pieces xs ys pieces =
  let open LogicOld in
  let num_sort =
    if List.for_all (xs @ ys) ~f:(fun t -> Term.is_int_sort (Term.sort_of t))
    then T_int.SInt
    else T_real.SReal
  in
  let affine ts (cs, c0) =
    if Stdlib.( = ) num_sort T_int.SInt then
      T_int.mk_sum (T_int.mk_int c0)
        (List.map2_exn cs ts ~f:(fun c t -> T_int.mk_mul (T_int.mk_int c) t))
    else
      T_real.mk_rsum
        (T_real.mk_real (Q.of_bigint c0))
        (List.map2_exn cs ts ~f:(fun c t ->
             T_real.mk_rmul
               (T_real.mk_real (Q.of_bigint c))
               (T_irb.cast (Term.sort_of t, num_sort) t)))
  in
  let zero = T_irb.zero_of num_sort in
  let disc ts d =
    Formula.and_of
      (List.map d ~f:(fun a ->
           Formula.mk_atom @@ T_irb.geq_of num_sort (affine ts a) zero))
  in
  let nl =
    match pieces with
    | [] -> 0
    | (_, fs) :: rest ->
        let nl = List.length fs in
        if List.exists rest ~f:(fun (_, fs') -> List.length fs' <> nl) then
          failwith "template_order_pieces: pieces of different lengths"
        else nl
  in
  let ldec (_, fi) (_, fj) =
    let rx = List.map fi ~f:(affine xs) and ry = List.map fj ~f:(affine ys) in
    Formula.or_of
    @@ List.init nl ~f:(fun k ->
           Formula.and_of
           @@ (Formula.mk_atom @@ T_irb.geq_of num_sort (List.nth_exn rx k) zero)
              :: T_irb.gt_of num_sort (List.nth_exn rx k) (List.nth_exn ry k)
              :: List.init k ~f:(fun l ->
                     Formula.or_of
                       [
                         Formula.and_of
                           [
                             T_irb.gt_of num_sort zero (List.nth_exn rx l);
                             T_irb.gt_of num_sort zero (List.nth_exn ry l);
                           ];
                         Formula.mk_atom
                         @@ T_irb.geq_of num_sort (List.nth_exn rx l)
                              (List.nth_exn ry l);
                       ]))
  in
  Formula.and_of
    [
      Formula.or_of (List.map pieces ~f:(fun (d, _) -> disc ys d));
      Formula.or_of
        (List.map pieces ~f:(fun pi ->
             Formula.and_of
               (disc xs (fst pi)
               :: List.map pieces ~f:(fun pj ->
                      Formula.mk_imply (disc ys (fst pj)) (ldec pi pj)))));
    ]

(* [two_pieces ~n (p, t, f1, f2)]: the pieces of [piecewise_ranking]'s answer
   for [template_order_pieces]: [t - z_p >= 0] ranked by [f1],
   [z_p - t - 1 >= 0] by [f2], over states of [n] positions. *)
let two_pieces ~n (p, t, f1, f2) =
  let unit sign = List.init n ~f:(fun j -> if j = p then sign else Z.zero) in
  [ ([ (unit Z.minus_one, t) ], [ f1 ]); ([ (unit Z.one, Z.(neg (t + one))) ], [ f2 ]) ]

(* [str_of_two_pieces (p, t, f1, f2)]: a piecewise ranking for a trace. *)
let str_of_two_pieces (p, t, f1, f2) =
  sprintf "x%d <= %s ? %s : %s" (p + 1) (Z.to_string t)
    (str_of_components [ f1 ]) (str_of_components [ f2 ])

(* [sign_directions ~n ~is_int regions]: the discriminators a piecewise
   ranking may split on, read off the regions' own rows.  A row [k . z <= b]
   (over a copy and a state of [n] positions, perhaps with existential columns
   past [2 n], which must be 0 in it) whose non-zero entries all lie in one
   state, at positions [is_int] accepts, states [a . s >= c] for that state
   [s], with [a = -k] restricted to the state and [c = -b].  Over the integers
   that inequality and [a . s <= c - 1] partition the states, so the
   discriminator is kept as [(a, c)] normalised: [a] divided by the gcd [g] of
   its entries, [c] by [g] rounded up (the same integer half-space), and, when
   the first non-zero entry of [a] is negative, [(a, c)] replaced by
   [(-a, 1 - c)] (the complementary half-space, so the same partition).
   Directions [a] are returned in decreasing number of regions whose rows
   mention them (first occurrence breaks ties), each with every threshold [c]
   its rows give, the most frequent first (first occurrence breaks ties).
   Pure. *)
let sign_directions ~n ~is_int regions =
  let gcd_list zs = List.fold zs ~init:Z.zero ~f:Z.gcd in
  let normalise (a, c) =
    let g = gcd_list a in
    if Z.equal g Z.zero then None
    else
      let a = List.map a ~f:(fun k -> Z.div k g) in
      let c = Z.cdiv c g in
      match List.find a ~f:(fun k -> not (Z.equal k Z.zero)) with
      | Some k when Z.lt k Z.zero ->
          Some (List.map a ~f:Z.neg, Z.(one - c))
      | _ -> Some (a, c)
  in
  let of_row (ks, b) =
    if List.length ks < 2 * n then None
    else
      let xs = List.take ks n and ys = List.sub ks ~pos:n ~len:n in
      let extra = List.drop ks (2 * n) in
      let zero l = List.for_all l ~f:(Z.equal Z.zero) in
      let ints l =
        List.for_alli l ~f:(fun p k -> Z.equal k Z.zero || is_int p)
      in
      if not (zero extra) then None
      else if (not (zero xs)) && zero ys && ints xs then
        normalise (List.map xs ~f:Z.neg, Z.neg b)
      else if zero xs && (not (zero ys)) && ints ys then
        normalise (List.map ys ~f:Z.neg, Z.neg b)
      else None
  in
  (* per direction: the regions mentioning it, and its thresholds' counts,
     both in order of first occurrence *)
  let table =
    List.foldi regions ~init:[] ~f:(fun ri acc rows ->
        List.fold rows ~init:acc ~f:(fun acc row ->
            match of_row row with
            | None -> acc
            | Some (a, c) -> (
                match List.Assoc.find acc a ~equal:Stdlib.( = ) with
                | None -> acc @ [ (a, ([ ri ], [ (c, 1) ])) ]
                | Some (ris, cs) ->
                    let ris = if List.mem ris ri ~equal:( = ) then ris else ri :: ris in
                    let cs =
                      match List.Assoc.find cs c ~equal:Z.equal with
                      | None -> cs @ [ (c, 1) ]
                      | Some k ->
                          List.map cs ~f:(fun (c', k') ->
                              if Z.equal c c' then (c', k + 1) else (c', k'))
                    in
                    List.Assoc.add acc a (ris, cs) ~equal:Stdlib.( = ))))
  in
  (* [List.Assoc.add] moves an updated entry to the front; restore the order
     of first occurrence before the stable sorts *)
  let order =
    List.foldi regions ~init:[] ~f:(fun _ acc rows ->
        List.fold rows ~init:acc ~f:(fun acc row ->
            match of_row row with
            | Some (a, _) when not (List.mem acc a ~equal:Stdlib.( = )) -> acc @ [ a ]
            | _ -> acc))
  in
  List.map order ~f:(fun a ->
      let ris, cs = List.Assoc.find_exn table a ~equal:Stdlib.( = ) in
      let cs =
        List.stable_sort cs ~compare:(fun (_, k1) (_, k2) -> Int.compare k2 k1)
        |> List.map ~f:fst
      in
      (List.length ris, (a, cs)))
  |> List.stable_sort ~compare:(fun (k1, _) (k2, _) -> Int.compare k2 k1)
  |> List.map ~f:snd

(* [sign_cell_atoms dirs signs]: the discriminator of the cell [signs] (one
   [true] for [a . s >= c], [false] for [a . s <= c - 1], per direction of
   [dirs]) as [template_order_pieces]' atoms [cs . s + c0 >= 0]. *)
let sign_cell_atoms dirs signs =
  List.map2_exn dirs signs ~f:(fun (a, c) pos ->
      if pos then (a, Z.neg c) else (List.map a ~f:Z.neg, Z.(c - one)))

(* The feasibility answers [sign_cell_ranking] got from Z3, per domain and
   for the whole process, keyed by a region's rows (with any cell rows
   appended): the same rows always have the same rational points, so a
   decided answer is the answer every later asking would get; an undecided
   one is not kept.  Regions recur across the refinements of a run (the
   stored regions are asked again with the new ones), and this is what keeps
   their questions from being asked again. *)
let sign_feasible_memo_key : ((Z.t list * Z.t) list, bool) Hashtbl.Poly.t Stdlib.Domain.DLS.key =
  Stdlib.Domain.DLS.new_key (fun () -> Hashtbl.Poly.create ())

let sign_feasible_memo () = Stdlib.Domain.DLS.get sign_feasible_memo_key

(* With COAR_DUMP_SIGN_CELLS=<file> set, each [sign_cell_ranking] question set
   is appended to <file> as one line, read back by the replay of
   [test/sign_cell_prune.exe]: [n is_int | region ; region ...], [is_int] one
   [0]/[1] per position, a region being its rows [k1,k2,..:b] separated by
   spaces.  Without the variable nothing is written. *)
let dump_sign_cell_question ~n ~is_int regions =
  match Sys.getenv "COAR_DUMP_SIGN_CELLS" with
  | None | Some "" -> ()
  | Some file -> (
      try
        let row (ks, b) =
          String.concat ~sep:"," (List.map ks ~f:Z.to_string) ^ ":" ^ Z.to_string b
        in
        let region rows = String.concat ~sep:" " (List.map rows ~f:row) in
        let line =
          sprintf "%d %s | %s\n" n
            (String.concat (List.init n ~f:(fun p -> if is_int p then "1" else "0")))
            (String.concat ~sep:" ; " (List.map regions ~f:region))
        in
        Out_channel.with_file ~append:true file ~f:(fun oc ->
            Out_channel.output_string oc line)
      with exn when not (Common.Timer.is_async exn) -> ())

(* [sign_cell_ranking ~n ~is_int regions]: a piecewise ranking whose pieces
   are the sign cells of up to [max_split] discriminators (two by default):
   for discriminators [d_1 .. d_m] read off the regions ([sign_directions],
   the first [max_directions] of them), a cell is one choice of
   [d_l(s) >= 0] or [d_l(s) <= -1] per [l] -- [2^m] cells that partition the
   integer states -- and each cell [i] has one affine component [f_i].  The
   demand, for every region (as [region_rows]) and every cell [i] the earlier
   state may be in and cell [j] the later state may be in:
     [f_i(x) >= 0  /\  f_i(x) >= f_j(y) + 1]  on the region within [i] at x and [j] at y,
   which is [piecewise_ranking]'s demand with [2^m] pieces.  A Manhattan
   distance [|x - tx| + |y - ty|] to a target is such a ranking with two
   discriminators and four cells, which no single linear function, no
   lexicographic order and no split on one fixed position gives.

   The cells a region may occupy are decided per discriminator and per state
   (one feasibility question over the rationals each, by evaluation for a
   region that is one integer point; an undecided question counts as
   feasible), so a cell combination that is empty only jointly still gets
   demands, which Farkas' lemma may then fail to certify: a lost candidate,
   never a wrong one.  With [prune_empty] a combination is dropped when it is
   empty for a reason one more feasibility question per region and
   discriminator shows: the state would cross a threshold in a direction the
   region never moves the discriminator (see [jointly_empty]); a dropped
   combination's demand is vacuous, so the query asks the same of every
   non-empty piece and can only answer [sat] more often.  Splits are tried smallest first -- each single
   discriminator, then each pair, in [sign_directions]' order -- one linear
   query each through [farkas_rows] ([rational] and [direct_points] as in
   [lex_ranking]; the rational form's components are scaled by one common
   factor, which keeps every demand since all of them are homogeneous but the
   decrease by 1).

   Answers [Some pieces], [template_order_pieces]' pieces [(atoms, [f_i])]
   in a fixed cell order, for the first split whose query is satisfiable;
   [None] when none is, when a region's rows have fewer than [2 n] columns, or
   when a question raises.

   What an answer is worth: [template_order_pieces] on these pieces is
   well-founded whatever the components and discriminators are (see there),
   so a wrong model costs at most a candidate that fails the caller's
   independent containment check. *)
let sign_cell_ranking ?(id = None) ?(timeout_ms = 1000) ?(rational = false)
    ?(direct_points = false) ?(max_directions = 6) ?(max_split = 2)
    ?(prune_empty = false) ?(prune_mutant = false) ~n ~is_int regions =
  let num = if rational then Num.real_num else Num.int_num in
  let farkas_rows = farkas_rows ~num ~direct_points in
  let open LogicOld in
  dump_sign_cell_question ~n ~is_int regions;
  Common.PhaseTime.with_phase "sign-cells" @@ fun () ->
  try
    if
      List.is_empty regions || n = 0
      || List.exists regions
           ~f:(List.exists ~f:(fun (ks, _) -> List.length ks < 2 * n))
    then None
    else
      let width rows =
        List.fold rows ~init:(2 * n) ~f:(fun w (ks, _) -> max w (List.length ks))
      in
      (* the atom [cs . s + c0 >= 0] on the earlier ([later = false]) or the
         later state, as a row [k . z <= b] of [w] columns *)
      let atom_row ~w ~later (cs, c0) =
        ( List.init w ~f:(fun col ->
              let p = if later then col - n else col in
              if p >= 0 && p < n && (if later then col >= n else col < n) then
                Z.neg (List.nth_exn cs p)
              else Z.zero),
          c0 )
      in
      (* whether the rows have a rational point (an integer point region by
         evaluation); undecided counts as feasible *)
      let feasible rows =
        match integer_point ~n rows with
        | Some _ -> true
        | None -> (
            match Hashtbl.find (sign_feasible_memo ()) rows with
            | Some answer -> answer
            | None ->
            let w = width rows in
            let zs =
              List.init w ~f:(fun _ ->
                  Term.mk_var
                    (Ident.mk_fresh_tvar ~prefix:(Some "RF_") ())
                    T_real.SReal)
            in
            let phi =
              Formula.and_of
                (List.map rows ~f:(fun (ks, b) ->
                     Formula.leq
                       (T_real.mk_rsum (T_real.rzero ())
                          (List.map2_exn ks (List.take zs (List.length ks))
                             ~f:(fun k z ->
                               T_real.mk_rmul (T_real.mk_real (Q.of_bigint k)) z)))
                       (T_real.mk_real (Q.of_bigint b))))
            in
            match
              (* only satisfiability is read *)
              Z3Smt.Z3interface.with_model_unread (fun () ->
                  Z3Smt.Z3interface.check_sat ~timeout:(Some timeout_ms) ~id
                    (get_fenv ()) [ phi ])
            with
            | `Unsat ->
                Hashtbl.set (sign_feasible_memo ()) ~key:rows ~data:false;
                false
            | `Sat _ ->
                Hashtbl.set (sign_feasible_memo ()) ~key:rows ~data:true;
                true
            | _ -> true)
      in
      (* a point region with the row added: feasible when the point satisfies
         it; [integer_point] answers [None] for a point the row excludes, so
         that case is read off the point of the region alone *)
      let feasible_with rows extra =
        match integer_point ~n rows with
        | Some p ->
            List.for_all extra ~f:(fun (ks, b) ->
                Z.leq
                  (List.foldi ks ~init:Z.zero ~f:(fun col acc k ->
                       if col < List.length p then Z.(acc + (k * List.nth_exn p col))
                       else acc))
                  b)
        | None -> feasible (rows @ extra)
      in
      (* Each direction's threshold, and the order directions are tried in.
         A region where [a . s] increases (proved by the infeasibility of
         [a . y <= a . x] on it) lies, for a V-shaped ranking split at [c],
         below the split ([a . x <= c - 1]), and one where it decreases lies
         above it ([a . x >= c]); the threshold taken is the first of the
         direction's thresholds (most frequent first) consistent with every
         such region, or the most frequent when none is.  Directions with
         regions on both sides -- the ones a split is needed for -- come
         first, the rest after, each group in [sign_directions]' order. *)
      let along a ~by =
        (* the row [by (a . y - a . x) <= 0] *)
        List.init (2 * n) ~f:(fun col ->
            if col < n then Z.mul (Z.neg by) (List.nth_exn a col)
            else Z.mul by (List.nth_exn a (col - n)))
      in
      let pad w ks = ks @ List.init (w - List.length ks) ~f:(fun _ -> Z.zero) in
      let dirs =
        List.map (sign_directions ~n ~is_int regions) ~f:(fun (a, cs) ->
            let inc, dec =
              List.partition_map
                (List.filter_map regions ~f:(fun rows ->
                     let w = width rows in
                     if not (feasible_with rows [ (pad w (along a ~by:Z.one), Z.zero) ])
                     then Some (Either.First rows)
                     else if
                       not (feasible_with rows [ (pad w (along a ~by:Z.minus_one), Z.zero) ])
                     then Some (Either.Second rows)
                     else None))
                ~f:Fn.id
            in
            let consistent c =
              List.for_all inc ~f:(fun rows ->
                  let w = width rows in
                  not (feasible_with rows [ atom_row ~w ~later:false (a, Z.neg c) ]))
              && List.for_all dec ~f:(fun rows ->
                     let w = width rows in
                     not
                       (feasible_with rows
                          [ atom_row ~w ~later:false (List.map a ~f:Z.neg, Z.(c - one)) ]))
            in
            let c =
              Option.value ~default:(List.hd_exn cs) (List.find cs ~f:consistent)
            in
            ((not (List.is_empty inc)) && not (List.is_empty dec), (a, c)))
        |> List.stable_sort ~compare:(fun (f1, _) (f2, _) -> Bool.compare f2 f1)
        |> List.map ~f:snd
        |> Fn.flip List.take max_directions
      in
      let regions = Array.of_list regions in
      (* [signs.(r).(d).(later)]: the signs the state may take on [dirs.(d)]
         in region [r] *)
      let sign_memo = Hashtbl.Poly.create () in
      let signs r d later =
        Hashtbl.find_or_add sign_memo (r, d, later) ~default:(fun () ->
            let rows = regions.(r) in
            let w = width rows in
            List.filter [ true; false ] ~f:(fun pos ->
                feasible_with rows
                  [ atom_row ~w ~later (List.hd_exn (sign_cell_atoms [ List.nth_exn dirs d ] [ pos ])) ]))
      in
      (* [prune_empty]: [never_crosses r d ~down] is [true] when the region
         [r] has no transition whose discriminator [d] falls by at least 1
         ([~down:true]: [a . y - a . x <= -1] infeasible) or rises by at
         least 1 ([~down:false]); one feasibility question each, decided as
         [feasible] decides (an undecided one is not a proof, so nothing is
         pruned on it) *)
      let cross_memo = Hashtbl.Poly.create () in
      let never_crosses r d ~down =
        Hashtbl.find_or_add cross_memo (r, d, down) ~default:(fun () ->
            let rows = regions.(r) in
            let w = width rows in
            let a = fst (List.nth_exn dirs d) in
            not
              (feasible_with rows
                 [ (pad w (along a ~by:(if down then Z.one else Z.minus_one)), Z.minus_one) ]))
      in
      (* the earlier cell [ci] and the later cell [cj] of the split [split] are
         jointly empty on region [r] when for some discriminator the state
         would have to cross its threshold in a direction the region never
         moves it: from [d >= c] to [d <= c - 1] needs a fall of at least 1,
         from [d <= c - 1] to [d >= c] a rise of at least 1.  The mutant
         ([prune_mutant], a test's only) also prunes a pair that stays in the
         same cell, which is not empty. *)
      let jointly_empty r split ci cj =
        prune_empty
        && (List.exists (List.zip_exn split (List.zip_exn ci cj))
              ~f:(fun (d, (pi, pj)) ->
                (pi && (not pj) && never_crosses r d ~down:true)
                || ((not pi) && pj && never_crosses r d ~down:false))
           || (prune_mutant && Stdlib.( = ) ci cj && r % 3 = 0))
      in
      let splits =
        let k = List.length dirs in
        let singles = List.init k ~f:(fun d -> [ d ]) in
        let pairs =
          if max_split < 2 then []
          else
            List.concat_map (List.init k ~f:Fn.id) ~f:(fun d1 ->
                List.filter_map (List.init k ~f:Fn.id) ~f:(fun d2 ->
                    if d1 < d2 then Some [ d1; d2 ] else None))
        in
        if max_split < 1 then [] else singles @ pairs
      in
      let rec cells m =
        if m = 0 then [ [] ]
        else
          List.concat_map (cells (m - 1)) ~f:(fun c -> [ true :: c; false :: c ])
      in
      let product choices =
        List.fold_right choices ~init:[ [] ] ~f:(fun opts acc ->
            List.concat_map opts ~f:(fun o -> List.map acc ~f:(fun rest -> o :: rest)))
      in
      List.find_map splits ~f:(fun split ->
          let sdirs = List.map split ~f:(List.nth_exn dirs) in
          let cs = cells (List.length split) in
          let index cell =
            fst (List.findi_exn cs ~f:(fun _ c -> Stdlib.( = ) c cell))
          in
          let fresh () = Ident.mk_fresh_tvar ~prefix:(Some "RS_") () in
          let comps =
            List.map cs ~f:(fun _ -> (List.init n ~f:(fun _ -> fresh ()), fresh ()))
          in
          let c i j = Term.mk_var (List.nth_exn (fst (List.nth_exn comps i)) j) num.sort in
          let k i = Term.mk_var (snd (List.nth_exn comps i)) num.sort in
          let zero = Num.zero num in
          let constraints =
            Common.PhaseTime.with_phase "lp-build" @@ fun () ->
            List.concat
            @@ List.init (Array.length regions) ~f:(fun r ->
                   let rows = regions.(r) in
                   let w = width rows in
                   let earlier = product (List.map split ~f:(fun d -> signs r d false)) in
                   let later = product (List.map split ~f:(fun d -> signs r d true)) in
                   List.concat_map earlier ~f:(fun ci ->
                       let i = index ci in
                       let xrows =
                         List.map (sign_cell_atoms sdirs ci) ~f:(atom_row ~w ~later:false)
                       in
                       List.concat_map later ~f:(fun cj ->
                           if jointly_empty r split ci cj then []
                           else
                           let j = index cj in
                           let yrows =
                             List.map (sign_cell_atoms sdirs cj) ~f:(atom_row ~w ~later:true)
                           in
                           let rows = rows @ xrows @ yrows in
                           farkas_rows ~n rows
                             (fun col -> if col < n then num.neg (c i col) else zero)
                             (k i)
                           @ farkas_rows ~n rows
                               (fun col ->
                                 if col < n then num.neg (c i col) else c j (col - n))
                               (num.sub (num.sub (k i) (k j)) (num.of_z Z.one)))))
          in
          let all_vars = List.concat_map comps ~f:(fun (cs, c0) -> c0 :: cs) in
          let model =
            Common.PhaseTime.with_phase "lp-ask" @@ fun () ->
            if rational then
              Option.map (rat_model ~id ~timeout_ms constraints) ~f:(fun m ->
                  let l =
                    List.fold all_vars ~init:Z.one ~f:(fun l v -> Z.lcm l (Q.den (m v)))
                  in
                  fun v -> Q.num Q.(m v * of_bigint l))
            else int_model ~id ~timeout_ms constraints
          in
          Option.map model ~f:(fun m ->
              List.map2_exn cs comps ~f:(fun cell (vs, v0) ->
                  (sign_cell_atoms sdirs cell, [ (List.map vs ~f:m, m v0) ]))))
  with exn when not (Common.Timer.is_async exn) -> None

(* [str_of_sign_cells pieces]: a sign-cell ranking for a trace, one
   [discriminator: component] per cell. *)
let str_of_sign_cells pieces =
  let atom (cs, c0) = str_of_components [ (cs, c0) ] ^ " >= 0" in
  String.concat_map_list ~sep:" | " pieces ~f:(fun (atoms, fs) ->
      String.concat_map_list ~sep:" /\\ " atoms ~f:atom
      ^ ": " ^ str_of_components fs)

(* [multi_location_llrf ~dims transitions]: whether the transitions have a
   lexicographic linear ranking function with one tuple of affine functions
   per location, read over the rationals.

   Input.  [dims loc] is the number of numeric state positions of location
   [loc]; each transition is [(src, dst, regions)], [regions] a list of
   [region_rows_over]' rows over the columns [x @ y @ e], [x] the source
   state ([dims src] columns), [y] the target state ([dims dst] columns) and
   [e] further variables, read existentially (a region is one polyhedron;
   the transition is their union, and each region is ranked on its own);
   [strict] says whether the transition must be ranked or need only not
   increase (a weak transition).

   The class.  A lexicographic linear ranking function of dimension [d]
   assigns to every location [l] affine functions [f_l^1 .. f_l^d] such that
   every region [P] of a strict transition [(l, r)] has an index [i] with,
   for every rational point [(x, y, e)] of [P]: [f_l^j x - f_r^j y >= 0] for
   [j < i], [f_l^i x - f_r^i y >= 1] and [f_l^i x >= 0], and every region of
   a weak transition has such an index or satisfies [f_l^j x - f_r^j y >= 0]
   for every [j].  Without weak transitions that is the lexicographic linear
   ranking function of Ben-Amram and Genaim, "Ranking functions for
   linear-constraint loops", J. ACM 61(4), 2014, extended to several
   locations; it implies that no infinite run takes the strict transitions
   infinitely often.

   The procedure (the greedy one): keep the set [T] of regions not yet
   ranked, starting from the rationally non-empty ones; a region [P] of [T]
   is rankable now when some functions are non-increasing on every region of
   [T] and decrease by at least one and are non-negative on [P]; remove every
   rankable region and repeat.  [`Exists k] when no region of a strict
   transition is left after [k] rounds; [`None_exists m] when a round finds
   no rankable region while [m] regions of strict transitions remain.  Both
   answers are exact for the class: each region removed supplies its own
   component (non-increasing on everything still left, the weak regions
   left at the end included), and if a ranking exists, its least index at
   which some region of [T] is ranked gives a component non-increasing on
   all of [T] that ranks that region, so a round never comes up empty while
   a strict region remains.

   Each question is a linear program over the rationals: each implication
   [P => a . z <= b] goes through the affine form of Farkas' lemma with
   real multipliers, which is exact for a non-empty [P], and every region is first checked to be rationally non-empty.  So
   every question is quantifier-free linear real arithmetic, which Z3's
   simplex decides; no budget is passed.  [`Undecided reason] when Z3 answers
   anything but sat or unsat, or a row is malformed.

   At most [r (r + 1) / 2] ranking questions for [r] regions, plus [r]
   emptiness questions.  The questions of one round share their conjuncts
   but for the candidate region's: the non-increase of every remaining
   region (the round's base) is converted to Z3 and asserted once per round
   in a solver of the test's own, and each question asserts only its own
   conjuncts in a scope ([Z3interface.base_session_check]), so a round costs
   one conversion of the base instead of one per remaining region.  Each
   question is the same conjunction either way and an answer other than sat
   or unsat from the session is asked again in a solver of its own, so the
   verdict is the one the questions asked separately give; quantifier-free
   linear real arithmetic is decided in Z3's incremental core as well.
   [~session:false] asks every question on its own, as a reference. *)
(* the ranking questions [multi_location_llrf] answered from a round's session *)
let multi_location_session_asks = ref 0

let multi_location_llrf ?(id = None) ?(session = true) ~dims transitions =
  let open LogicOld in
  let num = Num.real_num in
  let zero = Num.zero num in
  let ask phis =
    match
      Z3Smt.Z3interface.with_model_unread (fun () ->
          Z3Smt.Z3interface.check_sat ~timeout:None ~id (get_fenv ())
            [ Formula.and_of phis ])
    with
    | `Sat _ -> Ok true
    | `Unsat -> Ok false
    | _ -> Error "the solver did not decide a linear program"
  in
  let exception Undecided of string in
  let ok = function Ok b -> b | Error r -> raise (Undecided r) in
  try
    let coeffs = Hashtbl.Poly.create () in
    let coeffs_of loc =
      Hashtbl.Poly.find_or_add coeffs loc ~default:(fun () ->
          let v () =
            Term.mk_var (Ident.mk_fresh_tvar ~prefix:(Some "LLRF_") ()) num.sort
          in
          (List.init (dims loc) ~f:(fun _ -> v ()), v ()))
    in
    (* every region with its source and target *)
    let regions =
      List.concat_map transitions ~f:(fun (src, dst, strict, rs) ->
          List.map rs ~f:(fun rows -> (strict, (src, dst, rows))))
    in
    let width (src, dst, rows) =
      List.fold rows ~init:(dims src + dims dst) ~f:(fun w (ks, _) ->
          max w (List.length ks))
    in
    List.iter regions ~f:(fun (_, ((_, _, rows) as r)) ->
        let w = width r in
        if List.exists rows ~f:(fun (ks, _) -> List.length ks <> w) then
          raise (Undecided "rows of unequal width"));
    let nonempty (_, _, rows) =
      match rows with
      | [] -> true
      | (ks, _) :: _ ->
          let zs =
            List.map ks ~f:(fun _ ->
                Term.mk_var (Ident.mk_fresh_tvar ~prefix:(Some "LLRF_z") ())
                  num.sort)
          in
          ok
          @@ ask
               (List.map rows ~f:(fun (ks, b) ->
                    Formula.leq
                      (num.sum (List.map2_exn ks zs ~f:num.mul))
                      (num.of_z b)))
    in
    let regions = List.filter regions ~f:(snd >> nonempty) in
    (* [a . z <= beta] over a region of [src -> dst], through Farkas *)
    let implies (src, dst, rows) ~coef_x ~coef_y beta =
      let w = width (src, dst, rows) in
      let ns = dims src and nd = dims dst in
      let a col =
        if col < ns then coef_x col
        else if col < ns + nd then coef_y (col - ns)
        else zero
      in
      (* the affine form of Farkas' lemma: non-negative multipliers, one per
         row, with [ls . A = a] and [ls . b <= beta] *)
      let c = Farkas.combination ~num ~prefix:"LLRF_l" rows in
      (Formula.leq c.bound beta :: c.nonneg)
      @ List.init w ~f:(fun col -> Formula.eq (c.column col) (a col))
    in
    (* [f_src x - f_dst y >= k], as [-(a_src) . x + a_dst . y <= b_src - b_dst - k] *)
    let decrease ((src, dst, _) as r) k =
      let a_s, b_s = coeffs_of src and a_d, b_d = coeffs_of dst in
      implies r
        ~coef_x:(fun j -> num.neg (List.nth_exn a_s j))
        ~coef_y:(fun j -> List.nth_exn a_d j)
        (num.sub (num.sub b_s b_d) (num.of_z k))
    in
    (* [f_src x >= 0], as [-(a_src) . x <= b_src] *)
    let bounded ((src, _, _) as r) =
      let a_s, b_s = coeffs_of src in
      implies r ~coef_x:(fun j -> num.neg (List.nth_exn a_s j))
        ~coef_y:(fun _ -> zero) b_s
    in
    let use_session = session in
    let session = lazy (Z3Smt.Z3interface.base_session_create ~id ()) in
    let fenv = get_fenv () in
    let rec round k remaining =
      let strict_left = List.count remaining ~f:fst in
      if strict_left = 0 then `Exists k
      else
        let base =
          List.concat_map remaining ~f:(fun (_, r) -> decrease r Z.zero)
        in
        let in_session =
          if not use_session then None
          else
            let s = Lazy.force session in
            if Z3Smt.Z3interface.base_session_set ~id s fenv base then Some s
            else None
        in
        let rankable, rest =
          List.partition_tf remaining ~f:(fun (_, r) ->
              let ext = decrease r Z.one @ bounded r in
              match
                Option.map in_session ~f:(fun s ->
                    Z3Smt.Z3interface.base_session_check ~read_model:false ~id
                      s ~timeout:None fenv (Formula.and_of ext))
              with
              | Some (`Sat _) ->
                  incr multi_location_session_asks;
                  true
              | Some `Unsat ->
                  incr multi_location_session_asks;
                  false
              | Some `Unknown | None -> ok @@ ask (base @ ext))
        in
        if List.is_empty rankable then `None_exists strict_left
        else round (k + 1) rest
    in
    round 0 regions
  with
  | Undecided reason -> `Undecided reason
  | exn when not (Common.Timer.is_async exn) ->
      `Undecided ("raised " ^ Exn.to_string exn)
