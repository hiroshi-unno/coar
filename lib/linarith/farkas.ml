(* Farkas' lemma over rows of integers ([Rows]), in the two forms the tree's
   solvers use, and the Farkas interpolant read off a refutation.

   - The affine (implication) form [farkas_rows]: for rows [K z <= b] with a
     rational solution, [K z <= b] implies [a . z <= beta] exactly when some
     [lambda >= 0] has [lambda K = a] and [lambda . b <= beta].  Stated over
     fresh multipliers it is linear in the multipliers and in the caller's
     unknown [a] and [beta] jointly, which is how ranking functions and
     template instances are synthesised over regions.
   - The refutation form [refute]: rows [K z <= b] and strict rows
     [K' z < b'] have no rational solution exactly when some [lambda >= 0]
     cancels every column and either combines the bounds to a negative
     number, or to zero with positive weight on a strict row (Motzkin's
     transposition theorem).  [refute] finds such a [lambda] by one linear
     program and checks it in exact rational arithmetic before returning it.
   - The interpolant [interpolant_row]: when the rows are split into an [A]
     part and a [B] part and [lambda] refutes them all, the [A] part of the
     combination, [(lambda_A K_A) z <= lambda_A b_A] (strict when a strict
     row of [A] has positive weight), is implied by [A], is inconsistent with
     [B], and mentions only columns that occur in both: a column only [A]
     has is zero in [K_B], so its [A]-sum is minus its [B]-sum, which is 0
     (McMillan, "An interpolating theorem prover", Theoretical Computer
     Science 345(1), 2005).

   Sources: Farkas' lemma and Motzkin's transposition theorem as in
   Schrijver, "Theory of Linear and Integer Programming", Wiley, 1986.  Over
   the integers both forms are sound and incomplete: a rational certificate
   is one for the integer points too, but rows with no integer solution may
   have a rational one ([z = 2 x], [z = 2 y + 1]), and then no certificate
   exists and an interpolant needs divisibility atoms. *)

open Core
open Common.Ext
open Ast

(* The arithmetic the Farkas statements are written in.  [int_num] declares
   every unknown (multipliers, coefficients, constants) an integer, so Z3
   answers an integer linear program; [real_num] declares them reals, so a
   question is a linear program over the rationals (QF_LRA), where Farkas'
   lemma is exact and Z3's simplex decides it.  The row entries are integers
   either way.  [int_num]'s builders are the ones these functions always
   used, so a caller that does not ask for [real_num] gets the same terms. *)
module Num = struct
  type t = {
    sort : LogicOld.Sort.t;
    of_z : Z.t -> LogicOld.Term.t;
    mul : Z.t -> LogicOld.Term.t -> LogicOld.Term.t;
        (** [mul k t] is [k * t] *)
    sum : LogicOld.Term.t list -> LogicOld.Term.t;  (** [0 + t1 + ...] *)
    neg : LogicOld.Term.t -> LogicOld.Term.t;
    add : LogicOld.Term.t -> LogicOld.Term.t -> LogicOld.Term.t;
    sub : LogicOld.Term.t -> LogicOld.Term.t -> LogicOld.Term.t;
  }

  let int_num =
    let open LogicOld in
    {
      sort = T_int.SInt;
      of_z = T_int.mk_int;
      mul = (fun k t -> T_int.mk_mul (T_int.mk_int k) t);
      sum = (fun ts -> T_int.mk_sum (T_int.zero ()) ts);
      neg = T_int.mk_neg;
      add = T_int.mk_add;
      sub = T_int.mk_sub;
    }

  let real_num =
    let open LogicOld in
    let of_z z = T_real.mk_real (Q.of_bigint z) in
    {
      sort = T_real.SReal;
      of_z;
      mul = (fun k t -> T_real.mk_rmul (of_z k) t);
      sum = (fun ts -> T_real.mk_rsum (T_real.rzero ()) ts);
      neg = T_real.mk_rneg;
      add = T_real.mk_radd;
      sub = T_real.mk_rsub;
    }

  let zero num = num.of_z Z.zero
end

(* [combination ~num ~prefix rows]: fresh multipliers [ls] (one per row,
   named with [prefix], of [num]'s sort), the combination [column col] =
   [sum_i ls_i * k_i(col)] of each column, the combined bound [bound] =
   [sum_i ls_i * b_i], and [nonneg] = [ls_i >= 0] for every [i], in row order.
   Every Farkas statement in this library is assembled from these pieces.
   [taken] reserves the surrounding variable namespace, and every multiplier
   is reserved before the next draw. Without a collision the fresh names and
   counter advances remain unchanged. [column col] raises when a row has no
   column [col]. *)
type combination = {
  multipliers : LogicOld.Term.t list;
  column : int -> LogicOld.Term.t;
  bound : LogicOld.Term.t;
  nonneg : LogicOld.Formula.t list;
}

let combination ?(num = Num.int_num) ?(taken = Set.Poly.empty) ~prefix rows =
  let open LogicOld in
  let reserved = ref taken in
  let ls =
    List.map rows ~f:(fun _ ->
        let variable =
          Ident.mk_fresh_tvar_avoiding ~prefix ~taken:(Set.mem !reserved) ()
        in
        reserved := Set.add !reserved variable;
        Term.mk_var variable num.sort)
  in
  let column col =
    num.sum
      (List.map2_exn ls rows ~f:(fun l (ks, _) ->
           num.mul (List.nth_exn ks col) l))
  in
  let bound =
    num.sum (List.map2_exn ls rows ~f:(fun l (_, b) -> num.mul b l))
  in
  let zero = Num.zero num in
  {
    multipliers = ls;
    column;
    bound;
    nonneg = List.map ls ~f:(fun l -> Formula.geq l zero);
  }

(* [farkas_rows ~n rows a beta]: linear constraints over fresh non-negative
   integer multipliers, one per row, whose satisfaction implies
   [rows => a . z <= beta] for [z = x @ y] of length [2 n], where [rows] are
   [region_rows]' inequalities [k . z <= b] and [a col] is the coefficient
   term of column [col] (a term over the caller's unknown coefficients).
   This is the affine form of Farkas' lemma: the multipliers combine the rows
   into [a . z <= lambda . b <= beta]. For fixed [a] and [beta], the
   converse on a non-empty rational region needs rational multipliers:
   [2 z <= 2] implies [z <= 1], but its multiplier is [1/2], not an integer.
   A caller's joint synthesis can recover integral witnesses by common scaling
   only when its constraints admit that scaling. Empty regions can also lack
   a certificate for a vacuous implication. Both omissions cost candidates.
   Every constraint is linear in the multipliers and
   the coefficients jointly as long as [a] and [beta] are linear.
   With [direct_points], a region that is one integer point ([integer_point])
   gets the single constraint [a . p <= beta] instead, which has the same
   solutions in the coefficients ([a] integer-valued). *)
let farkas_rows ?(num = Num.int_num) ?(direct_points = false) ~n rows a beta =
  let open LogicOld in
  match if direct_points then Rows.integer_point ~n rows else None with
  | Some p ->
      (* the region is the one integer point [p]: the implication holds
         exactly when [a . p <= beta] (see [integer_point]) *)
      [
        Formula.leq
          (num.sum (List.mapi p ~f:(fun col v -> num.mul v (a col))))
          beta;
      ]
  | None ->
      (* rows wider than [2 n] carry extra columns (an example's parameters,
     existential in the region): the implication's coefficient there is 0, so
     the multipliers must cancel those columns, which states containment of
     the region's projection on [z] without computing it.  Rows of exactly
     [2 n] columns give the constraints they always gave. *)
      let zero = Num.zero num in
      let width =
        List.fold rows ~init:(2 * n) ~f:(fun w (ks, _) ->
            max w (List.length ks))
      in
      let a col = if col < 2 * n then a col else zero in
      let c = combination ~num ~prefix:"RL_" rows in
      (Formula.leq c.bound beta :: c.nonneg)
      @ List.init width ~f:(fun col -> Formula.eq (c.column col) (a col))

(* [is_refutation rows lambda]: whether [lambda] (one rational per row)
   certifies, by Motzkin's transposition theorem, that [rows] have no
   rational solution: every multiplier is non-negative, the combination of
   every column is 0, and the combined bound is negative, or zero with a
   positive multiplier on a strict row.  Decided in exact rational
   arithmetic; [false] on rows of unequal width or a list of the wrong
   length. *)
let is_refutation (rows : Rows.row list) lambda =
  match List.zip rows lambda with
  | Unequal_lengths -> false
  | Ok pairs -> (
      match rows with
      | [] -> false
      | r0 :: _ ->
          let width = List.length r0.coeffs in
          List.for_all rows ~f:(fun r -> List.length r.coeffs = width)
          && List.for_all lambda ~f:(fun l -> Q.geq l Q.zero)
          && List.for_all (List.init width ~f:Fn.id) ~f:(fun col ->
              Q.equal Q.zero
                (List.fold pairs ~init:Q.zero ~f:(fun acc (r, l) ->
                     Q.(acc + (l * of_bigint (List.nth_exn r.coeffs col))))))
          &&
          let bound =
            List.fold pairs ~init:Q.zero ~f:(fun acc (r, l) ->
                Q.(acc + (l * of_bigint r.bound)))
          in
          Q.lt bound Q.zero
          || Q.equal bound Q.zero
             && List.exists pairs ~f:(fun (r, l) -> r.strict && Q.gt l Q.zero))

type refutation =
  | Refuted of Q.t list
      (** multipliers, one per row, checked by [is_refutation] *)
  | Feasible  (** the rows have a rational solution: no certificate exists *)
  | Undecided of string
      (** Z3 did not decide, or its multipliers failed the exact check *)

(* [refute ?id rows]: a Motzkin certificate that [rows] (all of one width)
   have no rational solution.  The question is one linear program over the
   rationals -- multipliers [ls >= 0] (fresh reals named [FK_]) with every
   column cancelled and [ls . b <= -1], or [ls . b <= 0] with the strict
   rows' multipliers summing to at least 1 (both normalised by scaling) --
   which Z3's simplex decides, so no budget is passed.
   Post: [Refuted l] only when [is_refutation rows l]; [Feasible] only when
   Z3 answered unsat, i.e. the rows have a rational (and real) solution;
   [Undecided] otherwise.  An empty list of rows is [Feasible]. *)
let refute ?(id = None) (rows : Rows.row list) =
  let open LogicOld in
  match rows with
  | [] -> Feasible
  | r0 :: _ -> (
      let width = List.length r0.coeffs in
      if List.exists rows ~f:(fun r -> List.length r.coeffs <> width) then
        Undecided "rows of unequal width"
      else
        let num = Num.real_num in
        let c =
          combination ~num ~prefix:"FK_"
            (List.map rows ~f:(fun r -> (r.coeffs, r.bound)))
        in
        let strict_weight =
          num.sum
            (List.filter_map (List.zip_exn rows c.multipliers) ~f:(fun (r, l) ->
                 if r.strict then Some l else None))
        in
        let phi =
          Formula.and_of
            (c.nonneg
            @ List.init width ~f:(fun col ->
                Formula.eq (c.column col) (Num.zero num))
            @ [
                Formula.or_of
                  [
                    Formula.leq c.bound (num.of_z Z.minus_one);
                    Formula.and_of
                      [
                        Formula.leq c.bound (Num.zero num);
                        Formula.geq strict_weight (num.of_z Z.one);
                      ];
                  ];
              ])
        in
        match
          Z3Smt.Z3interface.check_sat ~timeout:None ~id (get_fenv ()) [ phi ]
        with
        | `Sat model -> (
            (* read by name and sort: an entry a pooled context holds at
               another sort says nothing about this multiplier *)
            let value l =
              let (v, s), _ = Term.let_var l in
              match model_find model (v, s) with
              | Some t ->
                  Value.cast_real_of
                    (Evaluator.eval_term (snd (remove_dontcare_elem ((v, s), t))))
              | None -> Q.zero
            in
            match List.map c.multipliers ~f:value with
            | lambda when is_refutation rows lambda -> Refuted lambda
            | _ -> Undecided "the multipliers failed the exact check"
            | exception exn when not (Common.Timer.is_async exn) ->
                Undecided ("reading the model raised " ^ Exn.to_string exn))
        | `Unsat -> Feasible
        | _ -> Undecided "the solver did not decide the linear program")

(* [interpolant_row a_rows b_rows lambda]: the combination of [a_rows]
   weighted by the first [|a_rows|] multipliers of [lambda]: rational
   coefficients per column, the rational bound, and whether it is strict
   (some strict row of [a_rows] has a positive multiplier).
   Pre: [is_refutation (a_rows @ b_rows) lambda].
   Post (McMillan's construction): [a_rows] imply the result over the
   rationals; the result and [b_rows] have no rational solution together; a
   column on which every row of [b_rows] is zero, or every row of [a_rows],
   has coefficient 0 in the result. *)
let interpolant_row (a_rows : Rows.row list) (_b_rows : Rows.row list) lambda =
  let pairs = List.zip_exn a_rows (List.take lambda (List.length a_rows)) in
  let width =
    match a_rows @ _b_rows with r :: _ -> List.length r.coeffs | [] -> 0
  in
  let coeffs =
    List.init width ~f:(fun col ->
        List.fold pairs ~init:Q.zero ~f:(fun acc (r, l) ->
            Q.(acc + (l * of_bigint (List.nth_exn r.coeffs col)))))
  in
  let bound =
    List.fold pairs ~init:Q.zero ~f:(fun acc (r, l) ->
        Q.(acc + (l * of_bigint r.bound)))
  in
  let strict = List.exists pairs ~f:(fun (r, l) -> r.strict && Q.gt l Q.zero) in
  (coeffs, bound, strict)
