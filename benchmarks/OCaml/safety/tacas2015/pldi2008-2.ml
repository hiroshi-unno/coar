(* @from Program analysis as constraint solving
         Sumit Gulwani, Saurabh Srivastava, and Ramarathnam Venkatesan
         PLDI 2008 *)

(* neceassary invariant: (0 <= x <= 51 /\ x = y) \/ (x >= 51 /\ y >= 0 /\ x + y = 102 *)
let rec f x y =
  if x <= 50 then
    (* y >= 0 /\ x <= 50 /\ x = y *)
    g x (y + 1)
  else
    (* y >= 0 /\ x >= 50 /\ x + y = 102 *)
    g x (y - 1)
and g x y =
  if y < 0 then
    assert (x == 102)
  else
    f (x + 1) y
and main y = f 0 0

[@@@assert "typeof(main) <: int -> unit"]
