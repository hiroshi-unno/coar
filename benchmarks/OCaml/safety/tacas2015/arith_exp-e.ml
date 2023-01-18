external nondet_bool : unit -> bool = "unknown"
[@@@rtype "nondet_bool::unit -> bool"]

external nondet_int : int -> int = "unknown"
[@@@rtype "nondet_int::(x:int) -> {r:int | 0 <= r && r < x}"]

type exp = Const of int | Add of exp * exp

let rec eval e =
  match e with
      Const n -> n
    | Add(e1,e2) -> eval e1 + eval e2

let rec make_exp () =
  if nondet_bool ()
  then Const (nondet_int 21 - 10)
  else Add(make_exp (), make_exp ())

let rec map f e =
  match e with
      Const n -> Const (f n)
    | Add(e1,e2) -> Add(map f e1, map f e2)

let abs x = if x <= 0 then x else -x

let main () =
  let e = make_exp () in
  let e' = map abs e in
    assert (eval e' >= 0)

[@@@assert "typeof(main) <: unit -> unit"]
