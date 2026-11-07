(* Note: This program is not included in the benchmark set
         used in [Unno et al. CAV'17] *)

let rec minus n m =
  if n <= m then 0
  else n - m

let main i j k =
  if i >= 0 && j >= 0 && k >= 0 then
    assert(minus (minus i j) k = minus i (minus j k))
  else ()
