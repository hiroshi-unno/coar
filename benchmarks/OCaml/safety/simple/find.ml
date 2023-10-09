let rec find e = function
| [] -> 999
| x :: xs -> if e = x then x else find e xs

let main () = find 1 [1]

[@@@assert "typeof(main) <: unit -> {z: int | z = 1}"]
[@@@assert "typeof(main) <: unit -> {z: int | z = 2}"]
[@@@assert "typeof(main) <: unit -> {z: int | z = 999}"]
