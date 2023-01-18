(*
USED: PEPM2013 as fold_fun_list
*)

let rec make_list n =
  if n <= 0
  then []
  else (fun m -> n + m) :: make_list (n-1)

let rec fold_right f xs init =
  match xs with
      [] -> init
    | x::xs' -> f x (fold_right f xs' init)

let compose f g x = f (g x)

let main n =
  let xs = make_list n in
  let f = fold_right compose xs (fun x -> x) in
    assert (f 0 >= 0)

[@@@assert "typeof(main) <: int -> unit"]
