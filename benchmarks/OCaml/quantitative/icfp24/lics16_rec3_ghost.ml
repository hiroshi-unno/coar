[@@@mode "hfl_prop_as_expectation"]

let rec rec3 (*ghost*)x k =
  let p = 0.5 in
  p *. k () +. (1.0 -. p) *. rec3 ((2.0 /. 3.0) *. (2.0 /. 3.0) *. x) (fun () -> rec3 ((2.0 /. 3.0) *. x) (fun () -> rec3 x (fun () -> k ())))

[@@@assert "typeof(rec3) <: { x : prop | x = 1.0 } -> (unit -> { r : prop | r = 1.0 }) -> { ret : prop | 0.0 <= ret && ret <= 2.0 / 3.0 }"]
