(* @require support of higher-order functions *)
let comp f g x = f (g x)
let rec pow f n =
  if n <= 0 then
    f
  else
    let f2 = pow f (n - 1) in
    comp f2 f2
let inc x = x + 1
let main x n = assert (pow inc n x >= x)

[@@@assert "typeof(main) <: int -> int -> unit"]
