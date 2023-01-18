let rec m x k =
  if x > 100
  then k (x-10)
  else m (x+11) (fun r -> m r k)

let main n =
  let k r = if n <= 101 then assert (r = 91) in
  m n k

[@@@assert "typeof(main) <: int -> unit"]
