let rec fold_left f accu l =
  match l with
    [] -> accu
  | a::l' -> fold_left f (f accu a) l'

let main l = fold_left (fun x y -> x + if y < 0 then -y else y) 0 l

[@@@assert "typeof(main) <: int list -> {z: int | z >= 0}"]
