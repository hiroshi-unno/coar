let hd_opt = function
| [] -> None
| x :: _xs -> Some (x: int)

[@@@assert "typeof(hd_opt) <: {z: int list | z <> []} -> {z: int option | z = None}"]
