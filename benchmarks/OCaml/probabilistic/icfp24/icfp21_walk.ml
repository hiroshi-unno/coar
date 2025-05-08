[@@@mode "hfl_prop_as_expectation"]

let rec walk p f n k =
  p n (fun b -> if b then k n else 1.0 +. f n (fun m -> walk p f m k))

let geo = walk (fun _ k -> 0.5 *. k true +. 0.5 *. k false) (fun n k -> k (n + 1))

[@@@assert "typeof(geo) <: int -> (int -> { r : prop | r = 0.0 }) -> { ret : prop | 0.0 <= ret && ret <= 1.0 }"]

let p = 2.0 /. 3.0
let randomWalk = walk (fun n k -> k (n <= 0)) (fun n k -> p *. k (n - 1) +. (1.0 -. p) *. k (n + 1))

[@@@assert "typeof(randomWalk) <: (n:int) -> (int -> { r : prop | r = 0.0 }) -> { ret : prop | 0.0 <= ret && ret <= 3.0 * float_of_int (abs n) }"]
