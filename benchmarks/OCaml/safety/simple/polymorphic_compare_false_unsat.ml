(* The false twin of [polymorphic_compare_true_sat.ml]: [a + 1 <= a] never
   holds, so no refinement typing of [main] exists. *)
let le x y = x <= y

let main (a:int) = assert (le (a + 1) a)

[@@@assert "typeof(main) <: int -> unit"]
