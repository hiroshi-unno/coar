let rec abs_sum l =
  match l with
  | [] -> 0
  | x :: xs ->
    if x < 0 then abs_sum xs - x
    else abs_sum xs + x

let main l = assert (abs_sum l >= 0)

[@@@assert "typeof(main) <: int list -> unit"]
