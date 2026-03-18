[@@@mode "hfl_prop_as_expectation"]

let rec rec3 k =
  let p = 0.5 in
  p *. k () +. (1.0 -. p) *. rec3 (fun () -> rec3 (fun () -> rec3 (fun () -> k ())))

[@@@assert "typeof(rec3) <: (unit -> { r : prop | r = 1.0 }) -> { ret : prop | 0.0 <= ret && ret <= (2.236068 - 1.0) / 2.0 }"]
