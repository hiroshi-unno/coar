[@@@mode "hfl_prop_as_expectation"]

let rec rw0 x f k = if x >= 0.0 then 0.5 *. rw1 (f (x +. 2.0)) (fun z -> f z -. 1.0) k +. 0.5 *. rw0 (f (x -. 2.0)) (fun z -> f z -. 1.0) k else k false
and rw1 x f k = if x >= 0.0 then 0.5 *. rw2 (f (x +. 2.0)) (fun z -> f z -. 1.0) k +. 0.5 *. rw1 (f (x -. 2.0)) (fun z -> f z -. 1.0) k else k false
and rw2 x f k = if x >= 0.0 then 0.5 *. rw2 (f (x +. 2.0)) (fun z -> f z -. 1.0) k +. 0.5 *. rw2 (f (x -. 2.0)) (fun z -> f z -. 1.0) k else k true

[@@@assert "typeof(rw0) <: { x : real | x = 1.0 } -> ((x : real) -> { y : real | y = x }) -> ((ac : bool) -> { r : prop | ac () && r = 1.0 || not ac () && r = 0.0 }) -> { ret : prop | 0.0 <= ret && ret <= 0.64 }"]
