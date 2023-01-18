(* @require disjunctive invariant
   @from Program analysis as constraint solving
         Sumit Gulwani, Saurabh Srivastava, and Ramarathnam Venkatesan
         PLDI 2008 *)

(* necessary invariant: x < 0 \/ y > 0 *)
let rec f x y =
  if x >= 0 then
    assert (y > 0)
  else
    f (x + y) (y + 1)
and main y = f (-50) y

[@@@assert "typeof(main) <: int -> unit"]
