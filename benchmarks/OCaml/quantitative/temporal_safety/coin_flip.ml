[@@@mode "hfl_prop_as_expectation"]

let rec coin0 k = 0.25 *. (0.5 *. coin1 k +. 0.5 *. coin0 k) +. 0.75 *. k false
and coin1 k = 0.25 *. (0.5 *. coin1 k +. 0.5 *. coin1 k) +. 0.75 *. k true

[@@@assert "typeof(coin0) <: ((ac : bool) -> { r : prop | ac () && r = 1.0 || not ac () && r = 0.0 }) -> { ret : prop | 0.0 <= ret && ret <= 1.0 / 7.0 }"]
