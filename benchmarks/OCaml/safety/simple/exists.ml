let rec exists e l = match l with
| [] -> false
| x::xs -> if x = e then true else exists e xs

let test e' e l = exists e (e' :: e :: l)
[@@@assert "typeof(test) <: int -> int -> int list -> {z: bool | z = true}"]
