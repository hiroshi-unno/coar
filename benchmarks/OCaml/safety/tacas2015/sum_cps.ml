let rec cps_sum n k : unit =
  if n <= 0 then
    k 0
  else
    cps_sum (n-1) (fun x -> k (x+n))
let main n = cps_sum n (fun x -> assert (x >= n))

[@@@assert "typeof(main) <: int -> unit"]
