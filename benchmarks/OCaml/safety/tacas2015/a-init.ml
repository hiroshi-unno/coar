(*
USED: PLDI2011 as a-init
*)

let make_array n i = assert (0 <= i && i < n); 0
let update i a x j :int= if j > i-1 && j <= i then x else a (j)
let rec init i n a =
  if i >= n then a else init (i + 1) n (update i a 1)
let main k n i =
  if k >= 0 && k <= 0 then
    let x = init k n (make_array n) in
      if 0 <= i && i < n then
        assert (x i >= 1)

[@@@assert "typeof(main) <: int -> int -> int -> unit"]
