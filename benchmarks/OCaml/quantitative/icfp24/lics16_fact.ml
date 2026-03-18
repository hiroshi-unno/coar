[@@@mode "hfl_prop_as_expectation"]

let rec fact x k =
  let p = 5.0 /. 6.0 in
  if x <= 0 then k 1
  else
    1.0 +. p *. fact (x - 1) (fun y -> k (y * x)) +. (1.0 -. p) *. fact (x - 2) (fun y -> k (y * x))

[@@@assert "typeof(fact) <: (x:{ x:int | x >= 0 }) -> (int -> { r : prop | r = 0.0 }) -> { ret : prop | 0.0 <= ret && ret <= 1.0 + float_of_int x / (2.0 - 5.0 / 6.0) }"]
