[@@@mode "hfl_prop_as_liberal_probability"]

(* A loop that fails with probability 1/4, succeeds with probability 1/4 and
   repeats with probability 1/2: the probability of not failing is the
   solution of x = 1/4 * 0 + 1/4 * 1 + 1/2 * x, which is 1/2.  The lower bound
   1/2 holds; in the liberal-probability mode the recursive result is refined
   by an admissible lower bound, which an upper-bound reading cannot give. *)
let rec loop k = 0.25 *. 0.0 +. 0.25 *. k () +. 0.5 *. loop k

[@@@assert "typeof(loop) <: (unit -> { r : prop | r = 1.0 }) -> { ret : prop | ret >= 0.5 }"]
