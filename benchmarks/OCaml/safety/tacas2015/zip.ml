(*
USED: PEPM2013 as zip
*)

let rec zip (xs:int list) (ys:int list) =
  match xs with
      [] ->
        begin
          match ys with
              [] -> []
            | _ -> assert false
        end
    | x::xs' ->
        match ys with
            [] -> assert false
          | y::ys' -> (x,y)::zip xs' ys'

let rec make_list n =
  if n < 0
  then []
  else n :: make_list (n-1)

let main n =
  let xs = make_list n in
    zip xs xs

[@@@assert "typeof(main) <: int -> (int * int) list"]
