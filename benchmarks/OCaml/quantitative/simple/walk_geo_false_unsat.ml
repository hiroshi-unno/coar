[@@@mode "hfl_prop_as_expectation"]

(* icfp24/icfp21_walk.ml's [geo] with a false bound: an expected value over
   the non-negative reals is never below -1.  [walk]'s result is a type
   variable, refined at the instance by a fresh unknown conjoined into the
   return refinement; unless that unknown is admissible too, its least
   solution is empty and every bound holds vacuously (this input was
   answered sat).  icfp21_walk.ml, whose bounds are true, is the control. *)

let rec walk p f n k =
  p n (fun b -> if b then k n else 1.0 +. f n (fun m -> walk p f m k))

let geo = walk (fun _ k -> 0.5 *. k true +. 0.5 *. k false) (fun n k -> k (n + 1))

[@@@assert "typeof(geo) <: int -> (int -> { r : prop | r = 0.0 }) -> { ret : prop | ret <= -1.0 }"]
