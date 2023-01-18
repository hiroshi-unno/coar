(* @from Program verification as probabilistic inference
         Sumit Gulwani and Nebojsa Jojic
         POPL 2007 *)

let rec f x y =
  if x < 100 then
    if x < 50 then
      f (x + 1) y
    else
      f (x + 1) (y + 1)
  else
    assert (y <= 100 && 100 <= y)
and main () = f 0 50

[@@@assert "typeof(main) <: unit -> unit"]
