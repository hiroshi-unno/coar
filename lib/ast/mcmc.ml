(* Sampling from the distributions of a probabilistic binder ([Rand.t]), for
   the sampling-based probabilistic quantified-satisfiability procedure
   ([MuCyc.Sqsat]), which estimates a probability as the share of samples
   satisfying a formula.  [samp] evaluates the distribution's parameters
   (they must be ground) and returns a fixed number of draws: uniform over a
   real or integer interval, or Gaussian with the given mean and variance by
   a Metropolis-style rejection step (the first draws discarded as burn-in).
   Draws use the global [Random] state. *)
open Core
open LogicOld.Rand

let uniform_samp r1 r2 =
  let f1 = Q.to_float r1 in
  let f2 = Q.to_float r2 in
  Set.Poly.of_increasing_iterator_unchecked ~len:1000 ~f:(fun _ ->
      Q.of_float @@ Random.float_range f1 f2)

let gauss_samp r1 r2 =
  let mu = Q.to_float r1 in
  let sigma2 = Q.to_float r2 in
  let invariant x =
    let y = Q.to_float x in
    let f1 = Float.int_pow (y -. mu) 2 in
    let f2 = -2.0 *. sigma2 in
    let f = exp (f1 /. f2) in
    Q.of_float f
  in
  let next x dx =
    let r = Q.of_float @@ Random.float_range (-0.5) 0.5 in
    Q.(x + (dx * r))
  in
  let state = Q.zero in
  let dx = Q.of_int 10 in
  let set =
    Set.Poly.of_increasing_iterator_unchecked ~len:1100 ~f:(fun i ->
        let nextstate = next state dx in
        let dist = Q.(invariant nextstate / invariant state) in
        if Q.(Q.one <= dist) then
          let state = nextstate in
          (i, state)
        else
          (* accept with probability [dist] < 1.  [dist] is a ratio of float
             values whose denominator can exceed a native int; an exact draw
             below it is taken where it fits, a float draw otherwise *)
          let den = Q.den dist in
          let accept =
            if Z.fits_int den then
              Random.int (Z.to_int den) < Z.to_int (Q.num dist)
            else Float.(Random.float 1.0 < Q.to_float dist)
          in
          if accept then
            let state = nextstate in
            (i, state)
          else (i, state))
  in
  let set =
    Set.Poly.filter_map set ~f:(fun (i, r) -> if i < 100 then None else Some r)
  in
  set

(* A uniform draw from [0, r] for [r >= 0] of any size: rejection sampling
   over integers of [Z.numbits r] random bits, 30 bits per [Random.bits]. *)
let z_random_upto r =
  let nbits = Z.numbits r in
  let rec draw () =
    let rec bits acc k =
      if k <= 0 then acc
      else
        let b = Int.min k 30 in
        let chunk = Random.bits () land ((1 lsl b) - 1) in
        bits Z.(logor (shift_left acc b) (of_int chunk)) (k - b)
    in
    let z = bits Z.zero nbits in
    if Z.leq z r then z else draw ()
  in
  draw ()

(* Uniform integers in [n1, n2]: the bounds are a term's values, so a pair that
   does not fit native ints is drawn in [Z]; a pair that fits is drawn as
   before. *)
let int_uniform_samp n1 n2 =
  if Z.fits_int n1 && Z.fits_int n2 then
    let i1 = Z.to_int n1 in
    let i2 = Z.to_int n2 in
    Set.Poly.of_increasing_iterator_unchecked ~len:1000 ~f:(fun _ ->
        Z.of_int @@ Random.int_incl i1 i2)
  else if Z.gt n1 n2 then invalid_arg "Mcmc.int_uniform_samp: empty range"
  else
    Set.Poly.of_increasing_iterator_unchecked ~len:1000 ~f:(fun _ ->
        Z.(n1 + z_random_upto (n2 - n1)))

let samp = function
  | Uniform (t1, t2) -> (
      match (Evaluator.eval_term t1, Evaluator.eval_term t2) with
      | Real r1, Real r2 -> uniform_samp r1 r2
      | Int n1, Int n2 -> uniform_samp (Q.of_bigint n1) (Q.of_bigint n2)
      | _ -> assert false)
  | Gauss (t1, t2) -> (
      match (Evaluator.eval_term t1, Evaluator.eval_term t2) with
      | Real r1, Real r2 -> gauss_samp r1 r2
      | Int n1, Int n2 -> gauss_samp (Q.of_bigint n1) (Q.of_bigint n2)
      | _ -> assert false)
  (* [int_uniform_samp] above draws these and had no caller: this case was
     missing, so an integer-uniform distribution reached a catch-all
     [assert false] here the first time the sampling solver was ever entered.
     The consumer builds a term from each element, so the draws are carried as
     rationals.  Note that mapping rebuilds the set by comparison and therefore
     keeps one copy of each distinct draw, where the two cases above hand on
     every draw including repeats; over a finite uniform support that turns the
     consumer's ratio of satisfying samples into a proportion of distinct
     values, which is the exact probability rather than an estimate of it. *)
  | IntUniform (t1, t2) -> (
      match (Evaluator.eval_term t1, Evaluator.eval_term t2) with
      | Int n1, Int n2 -> Set.Poly.map (int_uniform_samp n1 n2) ~f:Q.of_bigint
      | _ -> assert false)
