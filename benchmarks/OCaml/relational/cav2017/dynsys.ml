let rec dyn_sys vc =
  let fa = 0.5418 *. vc *. vc in (* the force control *)
  let fr = 1000. -. fa in
  let ac = 0.0005 *. fr in
  let vc' = vc +. ac in
  assert (vc' < 49.61); (* the safety velocity *)
  dyn_sys vc'
let main () = dyn_sys 0. (* the initial velocity *)
