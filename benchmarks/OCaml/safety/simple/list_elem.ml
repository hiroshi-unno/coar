let rec map f = function
| [] -> []
| x :: xs -> f x :: map f xs

let rec fold_right f l init =
  match l with
  | [] -> init
  | x :: xs -> f x (fold_right f xs init)

[@@@assert "typeof(map) <: ((x:int) -> {y:int | y=x+1}) -> {v:int | v>=0} list -> {v:int | v>=0} list"]
[@@@assert "typeof(map) <: ((x:int) -> {y:int | y=x+1}) -> {v:int | v>=0} list -> {v:int | v>=1} list"]
[@@@assert "typeof(map) <: ((x:int) -> {y:int | y=x+1}) -> {v:int | v>=0} list -> {v:int | v>=2} list"]

[@@@assert "typeof(fold_right) <: ((x:int) -> (y:int) -> {z:int | z=x+y}) -> {v:int | v>=0} list -> {v:int | v>=0} -> {v:int | v>=0}"]
