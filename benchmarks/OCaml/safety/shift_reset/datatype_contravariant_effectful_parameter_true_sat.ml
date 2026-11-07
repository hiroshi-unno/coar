(* As alg_eff/simple/datatype_contravariant_effectful_parameter_true_sat.ml with shift/reset: the stored function's parameter must be typed with the control effect of shift. *)
external shift : (('a -> 'b) -> 'c) -> 'd = "unknown"
external reset : (unit -> 'a) -> 'b = "unknown"
type 'a sink = Sink of ('a -> int)

let main () =
  reset (fun () ->
    let s = Sink (fun k -> k () + 10) in
    match s with Sink g -> g (fun () -> shift (fun c -> c 1 + c 2)))
[@@@assert "typeof(main) <: unit -> {z: int | z = 23}"]
