(* Continued fractions over arbitrary-precision integers, and
   [approximate_ratio], which replaces a vector of non-negative integers
   (the coefficients of a learned hyperplane) by one with smaller entries
   and roughly the same ratios.

   [approximate_ratio v level]: each level divides every entry by the
   smallest nonzero one (the first on ties) and recurses on the remainders,
   combining as the convergent recurrence of an ordinary continued fraction
   does.  Pre: entries are non-negative (callers pass absolute values and
   restore signs).  Post: zero entries stay zero; only the ratios are
   approximated, not the scale.  With two entries the result is exactly the
   ordinary convergent of their ratio at that depth.  With three or more it
   is a multidimensional generalisation: deep enough it returns the exact
   ratios divided by their gcd, but a deeper level is not always closer and
   no best-approximation property holds, so a caller tests each level against
   what it needs (as the SVM code does with the training examples) rather
   than assume that deeper is better.

   [continued_fraction_expansion_of_q] expands the absolute value; the sign
   is restored by [continued_fraction_to_q ~neg].

   The second method, [Per_coordinate] below, approximates each entry by its
   own convergents over a common denominator: its error is bounded and does
   not increase with the denominator bound, coordinate by coordinate, and it
   ends at the exact ratio, but nothing bounds the common denominator except
   the product of the separate ones.  [approximate_bw] is the search both
   callers use, with either method. *)
open Core

let rec continued_fraction_expansion n d =
  let open Z in
  let open Z.Compare in
  let r = n mod d in
  (n / d) :: (if r = zero then [] else continued_fraction_expansion d r)

let continued_fraction_expansion_of_q q =
  let n = Q.num q in
  let d = Q.den q in
  let open Z.Compare in
  if Z.(n = zero) then [ Z.zero ]
  else if Z.(n > zero) then continued_fraction_expansion n d
  else continued_fraction_expansion Z.(~-n) d

let rec continued_fraction =
  let open Z in
  function
  | [] -> (one, zero)
  | x :: l ->
      let n, d = continued_fraction l in
      ((x * n) + d, n)

let continued_fraction_to_q ?(neg = false) cf =
  let n, d = continued_fraction cf in
  if neg then Q.make Z.(~-n) d else Q.make n d

(* ratio: a list of non-negative integers *)
let rec approximate_ratio ratio level =
  if List.count ratio ~f:(fun n -> Z.Compare.(n <> Z.zero)) <= 1 then ratio
  else
    let m =
      List.mapi ratio ~f:(fun i n -> (i, n))
      |> List.filter ~f:(fun (_, n) -> Z.Compare.(n <> Z.zero))
      |> List.min_elt ~compare:(fun (_, n) (_, n') -> Z.compare n n')
    in
    let min_index, min_num = Option.value_exn m in
    let approx = List.map ~f:(fun n -> Z.(n / min_num)) ratio in
    if level <= 1 then approx
    else
      let remain =
        List.mapi
          ~f:(fun i n -> if i = min_index then n else Z.(n mod min_num))
          ratio
      in
      let approx_remain = approximate_ratio remain (level - 1) in
      let approx_remain_min_index = List.nth_exn approx_remain min_index in
      List.zip_exn approx approx_remain
      |> List.mapi ~f:(fun i (a, r) ->
             if i = min_index then r else Z.((a * approx_remain_min_index) + r))

(* How a floating-point coefficient vector, made exact and integral, is turned
   into a vector of small integers.  [Ratio_recursion] is
   [approximate_ratio] above, searched over its depth; [Per_coordinate]
   replaces each entry, after dividing by the largest absolute value of the
   non-constant entries, by its last continued-fraction convergent with
   denominator at most [d] and multiplies by the lcm of the denominators,
   searched over [d]. *)
type rational_approximation = Ratio_recursion | Per_coordinate
[@@deriving yojson]

let string_of_rational_approximation = function
  | Ratio_recursion -> "ratio_recursion"
  | Per_coordinate -> "per_coordinate"

(* The convergents [p_k / q_k] of [|q|], in order: [q_0 = 1] and the
   denominators strictly increase from [k = 1] on; the last is [|q|]
   itself, reduced. *)
let convergents_of_q q =
  let _, _, acc =
    List.fold (continued_fraction_expansion_of_q q)
      ~init:((Z.one, Z.zero), (Z.zero, Z.one), [])
      ~f:(fun ((h1, k1), (h2, k2), acc) a ->
        let h = Z.((a * h1) + h2) and k = Z.((a * k1) + k2) in
        ((h, k), (h1, k1), (h, k) :: acc))
  in
  List.rev acc

(* [best_convergent ~max_den q]: the last convergent of [|q|] whose
   denominator is at most [max_den], with the sign of [q].  Pre:
   [max_den >= 1].  Post: with [p/r] the result and [r'] the denominator of
   the next convergent (if any), [|q - p/r| <= 1/(r r') < 1/(r max_den)];
   the error does not increase with [max_den]; the result is [q] once
   [max_den >= den q]; [0] stays [0]. *)
let best_convergent ~max_den q =
  let p, r =
    List.fold (convergents_of_q q) ~init:(Z.zero, Z.one) ~f:(fun acc (p, r) ->
        if Z.Compare.(r <= max_den) then (p, r) else acc)
  in
  let p = if Q.sign q < 0 then Z.neg p else p in
  Q.make p r

(* [approximate_per_coordinate xs max_den]: each [x] of [xs] replaced by
   [best_convergent ~max_den x], all multiplied by the lcm [l] of the
   denominators.  Post: entry [j] is [l * best_convergent ~max_den x_j]
   exactly, so signs and zeros are kept and the ratios between entries are
   those of the approximations.  Nothing bounds [l] but the product of the
   distinct denominators (each at most [max_den]). *)
let approximate_per_coordinate xs max_den =
  let approx = List.map xs ~f:(best_convergent ~max_den) in
  let l = List.fold approx ~init:Z.one ~f:(fun l x -> Z.lcm l (Q.den x)) in
  List.map approx ~f:(fun x -> Q.(x * of_bigint l) |> Q.num)

(* The entries of an integer vector [b :: w] scaled so that the largest
   absolute value among [w] is 1 (among all entries when [w] is zero).
   [None] for the zero vector.  The scale is positive, so the halfspace
   [w . x + b >= 0] is unchanged. *)
let normalized_of_bw bw =
  let max_abs l = List.fold l ~init:Z.zero ~f:(fun m n -> Z.max m (Z.abs n)) in
  let s =
    let s = max_abs (List.tl_exn bw) in
    if Z.Compare.(s = Z.zero) then max_abs bw else s
  in
  if Z.Compare.(s = Z.zero) then None
  else Some (List.map bw ~f:(fun n -> Q.make n s))

(* The denominators at which [approximate_per_coordinate] can change for the
   normalised vector: every convergent denominator of every entry, sorted,
   distinct.  Its last element is the largest denominator of the entries,
   where the approximation is exact. *)
let per_coordinate_schedule xs =
  List.concat_map xs ~f:(fun x -> List.map (convergents_of_q x) ~f:snd)
  |> List.dedup_and_sort ~compare:Z.compare

let signed_ratio_recursion exact_bw level =
  let abs_approx = approximate_ratio (List.map ~f:Z.abs exact_bw) level in
  List.zip_exn abs_approx exact_bw
  |> List.map ~f:(fun (a, s) -> if Z.Compare.(s < Z.zero) then Z.(~-a) else a)

let log_enabled () =
  match Sys.getenv "COAR_RATAPX_LOG" with
  | Some s -> not (String.is_empty s)
  | None -> false

let log_result method_ steps param bw =
  if log_enabled () then
    let max_abs = List.fold bw ~init:Z.zero ~f:(fun m n -> Z.max m (Z.abs n)) in
    let sum_abs = List.fold bw ~init:Z.zero ~f:(fun m n -> Z.(m + abs n)) in
    Stdlib.prerr_endline
      (Printf.sprintf "ratapx method=%s dim=%d steps=%d param=%s maxabs=%s sumabs=%s"
         (string_of_rational_approximation method_)
         (List.length bw) steps param (Z.to_string max_abs)
         (Z.to_string sum_abs))

(* [approximate_bw ~method_ ~level ~accept exact_bw]: the integer vector
   [b :: w] that replaces the exact integer hyperplane [exact_bw].
   With [level > 0] the given depth ([Ratio_recursion]) or denominator bound
   ([Per_coordinate]) is used and [accept] is not called.  With [level <= 0]
   the first candidate [accept] takes is returned:
   - [Ratio_recursion]: depth 1, 2, ...; at each depth the entries below the
     k-th smallest absolute value are first set to 0, k from the largest
     down, then none (the search of the qualifier and classifier code it
     replaces, unchanged).  It does not stop if [accept] rejects every
     depth, including the exact ratio.
   - [Per_coordinate]: the denominator bounds of [per_coordinate_schedule]
     in increasing order; the last is the exact ratio divided by its gcd,
     returned whether or not [accept] takes it, so the search stops. *)
let approximate_bw ~method_ ~level ~accept exact_bw =
  match method_ with
  | Ratio_recursion ->
      if level > 0 then (
        let r = signed_ratio_recursion exact_bw level in
        log_result method_ 0 (string_of_int level) r;
        r)
      else
        let abs_exact_bw = List.map ~f:Z.abs exact_bw in
        let sorted = List.sort ~compare:Z.compare abs_exact_bw in
        let len = List.length exact_bw - 1 in
        let rec loop steps level cut =
          let lb = List.nth_exn sorted cut in
          let abs' =
            List.map abs_exact_bw ~f:(fun n ->
                if Z.Compare.(n >= lb) then n else Z.zero)
          in
          let r =
            List.zip_exn (approximate_ratio abs' level) exact_bw
            |> List.map ~f:(fun (a, s) ->
                   if Z.Compare.(s < Z.zero) then Z.(~-a) else a)
          in
          if accept r then (
            log_result method_ steps
              (Printf.sprintf "%d/cut%d" level cut)
              r;
            r)
          else if cut <= 0 then loop (steps + 1) (level + 1) len
          else loop (steps + 1) level (cut - 1)
        in
        loop 1 1 len
  | Per_coordinate -> (
      match normalized_of_bw exact_bw with
      | None -> exact_bw
      | Some xs ->
          if level > 0 then (
            let r = approximate_per_coordinate xs (Z.of_int level) in
            log_result method_ 0 (string_of_int level) r;
            r)
          else
            let rec loop steps = function
              | [] -> assert false
              | [ d ] ->
                  let r = approximate_per_coordinate xs d in
                  log_result method_ steps (Z.to_string d) r;
                  r
              | d :: ds ->
                  let r = approximate_per_coordinate xs d in
                  if accept r then (
                    log_result method_ steps (Z.to_string d) r;
                    r)
                  else loop (steps + 1) ds
            in
            loop 1 (per_coordinate_schedule xs))
