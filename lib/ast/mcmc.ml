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
          let j = Random.int (Z.to_int (Q.den dist)) in
          if j < Z.to_int (Q.num dist) then
            let state = nextstate in
            (i, state)
          else (i, state))
  in
  let set =
    Set.Poly.filter_map set ~f:(fun (i, r) -> if i < 100 then None else Some r)
  in
  set

let int_uniform_samp n1 n2 =
  let i1 = Z.to_int n1 in
  let i2 = Z.to_int n2 in
  Set.Poly.of_increasing_iterator_unchecked ~len:1000 ~f:(fun _ ->
      Z.of_int @@ Random.int_incl i1 i2)

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
  | _ -> assert false
