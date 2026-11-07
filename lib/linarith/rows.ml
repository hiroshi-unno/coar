(* Linear constraints read as rows of integers.  A region -- a conjunction of
   linear comparisons over integer or real columns -- becomes rows
   [k . z <= b] ([region_rows_over], which weakens or rounds strict
   comparisons) or rows that keep their strictness ([cube_rows_over]).  The
   Farkas statements over these rows are [Farkas]'s. *)

open Core
open Common.Ext
open Ast

(* The affine reading of numeric terms over the columns [zs], in order.
   Every accepted constructor preserves the returned rational affine form.
   Unsupported terms are declined, even when algebraic simplification could
   turn them into an affine term; no finite set of evaluations certifies
   that a term is affine. *)
let affine_over zs t =
  let open LogicOld in
  let zero = List.map zs ~f:(fun _ -> Q.zero) in
  let constant c = (zero, c) in
  let scale q (ks, c) = (List.map ks ~f:(fun k -> Q.(q * k)), Q.(q * c)) in
  let add (ks, c) (ls, d) = (List.map2_exn ks ls ~f:Q.( + ), Q.(c + d)) in
  let is_constant (ks, _) = List.for_all ks ~f:(fun k -> Q.equal k Q.zero) in
  let both a b f =
    Option.bind a ~f:(fun a -> Option.bind b ~f:(fun b -> f a b))
  in
  let rec read = function
    | Term.Var (v, s, _) ->
        Option.bind
          (List.findi zs ~f:(fun _ (w, _) -> Stdlib.(v = w)))
          ~f:(fun (i, (_, expected)) ->
            if Stdlib.(s = expected) then
              Some
                ( List.mapi zs ~f:(fun j _ -> if i = j then Q.one else Q.zero),
                  Q.zero )
            else None)
    | Term.FunApp (T_int.Int n, [], _) -> Some (constant (Q.of_bigint n))
    | Term.FunApp (T_real.Real q, [], _) ->
        if Z.equal (Q.den q) Z.zero then None else Some (constant q)
    | Term.FunApp ((T_int.Neg | T_real.RNeg), [ a ], _) ->
        Option.map (read a) ~f:(scale Q.minus_one)
    | Term.FunApp ((T_int.Nop | T_irb.IntToReal), [ a ], _) -> read a
    | Term.FunApp ((T_int.Abs | T_real.RAbs), [ a ], _) ->
        Option.bind (read a) ~f:(fun a ->
            if is_constant a then Some (constant (Q.abs (snd a))) else None)
    | Term.FunApp ((T_int.Add | T_real.RAdd), [ a; b ], _) ->
        both (read a) (read b) (fun a b -> Some (add a b))
    | Term.FunApp ((T_int.Sub | T_real.RSub), [ a; b ], _) ->
        both (read a) (read b) (fun a b -> Some (add a (scale Q.minus_one b)))
    | Term.FunApp ((T_int.Mul | T_real.RMul), [ a; b ], _) ->
        both (read a) (read b) (fun a b ->
            if is_constant a then Some (scale (snd a) b)
            else if is_constant b then Some (scale (snd b) a)
            else None)
    | Term.FunApp (T_real.RDiv, [ a; b ], _) ->
        both (read a) (read b) (fun a b ->
            if is_constant b && not (Q.equal (snd b) Q.zero) then
              Some (scale Q.(one / snd b) a)
            else None)
    | Term.FunApp (T_int.Div mode, [ a; b ], _) ->
        read_integer_quotient (Value.div_of mode) a b
    | Term.FunApp (T_int.Rem (Value.Euclidean as mode), [ a; b ], _)
    | Term.FunApp (T_int.Rem (Value.Truncated as mode), [ a; b ], _) ->
        read_integer_quotient (Value.rem_of mode) a b
    | _ -> None
  and read_integer_quotient op a b =
    both (read a) (read b) (fun a b ->
        if
          is_constant a && is_constant b
          && Z.equal (Q.den (snd a)) Z.one
          && Z.equal (Q.den (snd b)) Z.one
          && not (Q.equal (snd b) Q.zero)
        then Some (constant (Q.of_bigint (op (Q.num (snd a)) (Q.num (snd b)))))
        else None)
  in
  if
    List.exists zs ~f:(fun (_, s) ->
        not (Term.is_int_sort s || Term.is_real_sort s))
    || List.contains_dup (List.map zs ~f:fst) ~compare:Stdlib.compare
  then None
  else read t

(* [scale_to_integers (ks, k0)]: [d = ks . z + k0] multiplied by the least
   common multiple of the denominators, a positive factor, so every entry is
   an integer and the sign of [d] at every point is kept. *)
let scale_to_integers (ks, k0) =
  let l = List.fold (k0 :: ks) ~init:Z.one ~f:(fun l q -> Z.lcm l (Q.den q)) in
  let int_of q = Q.num Q.(q * of_bigint l) in
  (List.map ks ~f:int_of, int_of k0)

(* [integral_over zs (ks, k0)]: [d = ks . z + k0] takes only integer values on
   integer points of the integer columns: the constant is an integer and
   every non-zero coefficient is an integer on an integer column. *)
let integral_over zs (ks, k0) =
  let open LogicOld in
  Z.equal (Q.den k0) Z.one
  && List.for_all2_exn ks zs ~f:(fun k (_, s) ->
         Q.equal k Q.zero || (Term.is_int_sort s && Z.equal (Q.den k) Z.one))

(* [comparison_of zs phi]: an atom [t1 op t2] with [op] one of [<=], [<],
   [>=], [>], [=] over integers or reals and both sides affine over [zs], as
   [`Le d], [`Lt d] or [`Eq d] with [d = t1 - t2] (for [>=] and [>],
   [d = t2 - t1]); [None] for any other formula or unsupported term. *)
let comparison_of zs phi =
  let open LogicOld in
  if not (Formula.is_atom phi) then None
  else
    match fst (Formula.let_atom phi) with
    | Atom.App (Predicate.Psym sym, [ t1; t2 ], _) -> (
        match (affine_over zs t1, affine_over zs t2) with
        | Some (ks1, c1), Some (ks2, c2) ->
            let d = (List.map2_exn ks1 ks2 ~f:Q.( - ), Q.(c1 - c2)) in
            let neg (ks, k0) = (List.map ks ~f:Q.neg, Q.neg k0) in
            if Stdlib.(sym = T_int.Leq || sym = T_real.RLeq) then Some (`Le d)
            else if Stdlib.(sym = T_int.Lt || sym = T_real.RLt) then
              Some (`Lt d)
            else if Stdlib.(sym = T_int.Geq || sym = T_real.RGeq) then
              Some (`Le (neg d))
            else if Stdlib.(sym = T_int.Gt || sym = T_real.RGt) then
              Some (`Lt (neg d))
            else if Stdlib.( = ) sym T_bool.Eq then Some (`Eq d)
            else None
        | _ -> None)
    | _ -> None

(* [region_rows_over zs region]: the region as rows [(a, b)], each the
   inequality [a . z <= b] over the columns [zs] (in order) with integer [a]
   and [b], read over the rationals; [None] when a column is neither an
   integer nor a real, when a conjunct of the region is not a linear
   comparison, or when reading raises -- which includes a region mentioning a
   variable outside [zs] or using an unsupported term constructor.
   Post: every point of the region (integer states at integer values, real
   states at real values) satisfies every row; the rows may describe a larger
   set, because a strict comparison that is not integral is weakened to a
   non-strict one (see below). *)
let region_rows_over zs region =
  let open LogicOld in
  try
    if
      List.exists zs ~f:(fun (_, s) ->
          not (Term.is_int_sort s || Term.is_real_sort s))
    then None
    else
      (* The region as rows [a . z <= b] with integer [a] and [b], read over
         the rationals: each conjunct a linear comparison ([affine_over]), a
         row with rational entries scaled by the least common multiple of
         their denominators, which keeps it.

         A strict comparison [d < 0] is [d <= -1] when it reads only integer
         states with integer entries (before scaling, [integral_over]);
         otherwise it is weakened to [d <= 0], which only enlarges the
         region, so a test below that finds no ranking may then drop a
         region that has one -- a lost region, never a lost answer. *)
      let rows_of phi =
        if Formula.is_true phi then Some []
        else
          match comparison_of zs phi with
          | None -> None
          | Some cmp ->
              let d = match cmp with `Le d | `Lt d | `Eq d -> d in
              let strict_shift = if integral_over zs d then Z.one else Z.zero in
              let ks, k0 = scale_to_integers d in
              let neg = List.map ks ~f:Z.neg in
              (* d = ks . z + k0 *)
              let le = (ks, Z.neg k0) and ge = (neg, k0) in
              Some
                (match cmp with
                | `Le _ -> [ le ]
                | `Lt _ -> [ (ks, Z.(neg k0 - strict_shift)) ]
                | `Eq _ -> [ le; ge ])
      in
      Option.map ~f:List.concat
        (Option.all (List.map (Formula.conjuncts_list_of region) ~f:rows_of))
  with exn when not (Common.Timer.is_async exn) -> None

(* [region_rows xs ys region]: [region_rows_over (xs @ ys) region] when the two
   state lists have the same length, [None] otherwise. *)
let region_rows xs ys region =
  if List.length xs <> List.length ys then None
  else region_rows_over (xs @ ys) region

(* [integer_point ~n rows]: [Some p] when the rows (over [2 n] columns)
   describe exactly the one integer point [p]: every column [col] has rows
   [z_col <= v] and [-z_col <= -v] of its own (unit coefficient, nothing
   else), and every row holds at [p]; [None] otherwise, including when the
   unit rows fix the point but another row excludes it (an empty region).

   Why it matters to [Farkas.farkas_rows]: for such a region and an integer
   coefficient vector [a], the integer multipliers of Farkas' lemma prove
   [a . z <= beta] exactly when [a . p <= beta] -- one direction is the
   lemma's soundness, and for the other the multipliers [max(a_col, 0)] on
   [z_col <= p_col] and [max(-a_col, 0)] on [-z_col <= -p_col] combine to
   [a . z <= a . p].  So stating [a . p <= beta] directly leaves the
   coefficients' feasible set as it was, while a ground chain pair read as a
   region costs [2 (2 n)] multipliers and [2 n + 1] constraints per
   implication through the lemma, one inequality directly. *)
let integer_point ~n rows =
  let unit_at col sign (ks, _) =
    List.for_alli ks ~f:(fun j k ->
        if j = col then Z.equal k sign else Z.equal k Z.zero)
  in
  if List.exists rows ~f:(fun (ks, _) -> List.length ks <> 2 * n) then None
  else
    let p =
      List.init (2 * n) ~f:(fun col ->
          List.find_map rows ~f:(fun ((_, b) as row) ->
              if
                unit_at col Z.one row
                && List.exists rows ~f:(fun ((_, b') as row') ->
                       unit_at col Z.minus_one row' && Z.equal b' (Z.neg b))
              then Some b
              else None))
    in
    if List.exists p ~f:Option.is_none then None
    else
      let p = List.filter_opt p in
      if
        List.for_all rows ~f:(fun (ks, b) ->
            Z.leq (List.fold2_exn ks p ~init:Z.zero ~f:(fun acc k v -> Z.(acc + (k * v)))) b)
      then Some p
      else None

(* A row that keeps its comparison: [coeffs . z <= bound], or [< bound] when
   [strict].  Entries are integers, read over the rationals. *)
type row = { coeffs : Z.t list; bound : Z.t; strict : bool }

(* [cube_rows_over zs cube]: the conjunction [cube] as rows over the columns
   [zs] (in order), each conjunct a linear comparison ([comparison_of]) whose
   strictness is kept and whose entries are scaled to integers by a positive
   factor; an equation is two non-strict rows, [true] no row, [false] the row
   [0 <= -1].  [None] under the conditions of [region_rows_over].
   Post: over the rationals (and over the reals), a point satisfies [cube]
   exactly when it satisfies every row -- no comparison is weakened or
   rounded, unlike [region_rows_over]. *)
let cube_rows_over zs cube =
  let open LogicOld in
  try
    if
      List.exists zs ~f:(fun (_, s) ->
          not (Term.is_int_sort s || Term.is_real_sort s))
    then None
    else
      let rows_of phi =
        if Formula.is_true phi then Some []
        else if Formula.is_false phi then
          Some
            [
              {
                coeffs = List.map zs ~f:(fun _ -> Z.zero);
                bound = Z.minus_one;
                strict = false;
              };
            ]
        else
          match comparison_of zs phi with
          | None -> None
          | Some cmp ->
              let d = match cmp with `Le d | `Lt d | `Eq d -> d in
              let ks, k0 = scale_to_integers d in
              let le = { coeffs = ks; bound = Z.neg k0; strict = false } in
              Some
                (match cmp with
                | `Le _ -> [ le ]
                | `Lt _ -> [ { le with strict = true } ]
                | `Eq _ ->
                    [
                      le;
                      { coeffs = List.map ks ~f:Z.neg; bound = k0; strict = false };
                    ])
      in
      Option.map ~f:List.concat
        (Option.all (List.map (Formula.conjuncts_list_of cube) ~f:rows_of))
  with exn when not (Common.Timer.is_async exn) -> None

(* [tighten_integer zs row]: when every column with a non-zero coefficient is
   an integer column, the row rounded to an equivalent one over the integers:
   a strict row [k . z < b] becomes [k . z <= b - 1] (the left side takes
   integer values), and then [k . z <= b'] becomes [(k / g) . z <= floor (b'
   / g)] for [g] the gcd of the coefficients (a single-row Chvatal-Gomory
   cut).  Any other row is returned unchanged.
   Post: the result has exactly the integer points of [row] (on integer
   columns) and is never strict when it was rounded; over the rationals it
   may be strictly stronger, which is the point: [2 x = 1] becomes the
   rationally infeasible pair [x <= 0], [-x <= -1].  It is no complete
   method for integer infeasibility ([z = 2 x], [z = 2 y + 1] stay
   rationally feasible). *)
let tighten_integer zs row =
  let open LogicOld in
  if
    not
      (List.for_all2_exn row.coeffs zs ~f:(fun k (_, s) ->
           Z.equal k Z.zero || Term.is_int_sort s))
  then row
  else
    let b = if row.strict then Z.(row.bound - one) else row.bound in
    let g = List.fold row.coeffs ~init:Z.zero ~f:Z.gcd in
    if Z.equal g Z.zero then { row with bound = b; strict = false }
    else
      {
        coeffs = List.map row.coeffs ~f:(fun k -> Z.divexact k g);
        bound = Z.fdiv b g;
        strict = false;
      }
