type nat = Zero | Succ of nat 

let rec fold f g = function
  | Zero -> f Zero
  | Succ a -> g (fold f g a)

[@@@assert "typeof(fold) <: (f:(nat -> {r : int | r = 0})) ->
                            (g:((x:int) -> {r : int | r = x + 1})) ->
                            {x:nat | x <> Zero} -> {r : int | r > 0}"]

