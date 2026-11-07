(* Aliases over a tuple component and over a list tail: [q] is [(a, b)] and
   [r] is the tail [y :: _], so both functions return what the assertion
   states. *)
let f p =
  match p with ((a, b) as q), c -> ( match q with x, y -> x + y + c - a - b)

let g l =
  match l with
  | x :: (_ :: _ as r) -> ( match r with y :: _ -> x + y | [] -> 0)
  | _ -> 0

let main n = assert (f ((n, n), n) = n && g [ n; n ] = n + n && g [ n ] = 0)

[@@@assert "typeof(main) <: int -> unit"]
