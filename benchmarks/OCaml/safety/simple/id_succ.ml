let id x = x
let succ x = x + 1

let main () = id succ

[@@@assert "typeof(main) <: unit -> (n:int) -> {z: int | z = n + 1}"]
