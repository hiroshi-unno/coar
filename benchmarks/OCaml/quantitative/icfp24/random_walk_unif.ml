[@@@mode "hfl_prop_as_expectation"]

external unif : (float -> float) -> float = "unknown"
let rec rw x k =
  if x >= 0.0 then
    unif (fun y ->
        let l = -2.0 in
        let r = 1.0 in
        1.0 +. rw (x +. (r -. l) *. y +. l) k)
  else k ()

[@@@assert "typeof(rw) <: { x:float | x = 1.0 } -> (unit -> { r:prop | r = 0.0 }) -> { ret : prop | 0.0 <= ret && ret <= 6.0 }"]
