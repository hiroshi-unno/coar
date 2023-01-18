
let update a i x j = if j=i then x else a j

let rec dotprod v1 v2 n i sum =
  if i > n
  then sum
  else
    begin
      assert (0<=i && i<=n);
      dotprod v1 v2 n (i+1) (sum + v1 i * v2 i)
    end

let main i n =
  let v1 (i : int) = 0 in
  let v2 (i : int) = 0 in
  dotprod v1 v2 n 0 0; ()

[@@@assert "typeof(main) <: int -> int -> unit"]
