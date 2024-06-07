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
