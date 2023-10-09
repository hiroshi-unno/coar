type 'a exn =
| MyExn : int -> 'b exn

external raise : 'a exn -> 'b = "unknown"

let raise_exn () = raise (MyExn 1)

[@@@assert "typeof(raise_exn) <: unit -> (
  {MyExn: int -> (float -> bool) -> bool} |> float / bool => bool
)"]
[@@@assert "typeof(raise_exn) <: unit -> (
  {MyExn: {z: int | z = 2} -> (float -> bool) -> bool} |> float / bool => bool
)"]
