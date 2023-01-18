type t =
    Empty
  | Node of t * int * int * t * int

[@@@rtype "Node :: (t1:t) -> (t2:int) -> (t3:int) -> (t4:t) -> (t5: {h1: int | h1 >= 1}) -> {ret: t | ret = Node(t1, t2, t3, t4, t5)}"]

let ord_compare (n1:int) (n2:int) =
  if n1 > n2 then 1 else if n1 < n2 then -1 else 0

let height t =
  match t with
    Empty -> 0
  | Node(_,_,_,_,h) -> h

let create l x d r =
  let hl = height l and hr = height r in
  Node(l, x, d, r, (if hl >= hr then hl + 1 else hr + 1))

let bal l x d r =
  let hl = match l with Empty -> 0 | Node(_,_,_,_,h) -> h in
  let hr = match r with Empty -> 0 | Node(_,_,_,_,h) -> h in
  if hl > hr + 2 then begin
    match l with
      Empty -> assert false
    | Node(ll, lv, ld, lr, _) ->
      if height ll >= height lr then
        create ll lv ld (create lr x d r)
      else begin
        match lr with
          Empty -> assert false
        | Node(lrl, lrv, lrd, lrr, _)->
          create (create ll lv ld lrl) lrv lrd (create lrr x d r)
      end
  end else if hr > hl + 2 then begin
    match r with
      Empty -> assert false
    | Node(rl, rv, rd, rr, _) ->
      if height rr >= height rl then
        create (create l x d rl) rv rd rr
      else begin
        match rl with
          Empty -> assert false
        | Node(rll, rlv, rld, rlr, _) ->
          create (create l x d rll) rlv rld (create rlr rv rd rr)
      end
  end else
    Node(l, x, d, r, (if hl >= hr then hl + 1 else hr + 1))

let rec add x data t =
  match t with
    Empty ->
    Node(Empty, x, data, Empty, 1)
  | Node(l, v, d, r, h) ->
    let c = ord_compare x v in
    if c = 0 then
      Node(l, x, data, r, h)
    else if c < 0 then
      bal (add x data l) v d r
    else
      bal l v d (add x data r)

let main x data t = assert (height (add x data t) >= 0)

[@@@assert "typeof(main) <: int -> int -> t -> unit"]

let main x data t = assert (height (add x data t) > 1)

[@@@assert "typeof(main) <: int -> int -> t -> unit"]

let main x data t = assert (height (add x data t) = height t)

[@@@assert "typeof(main) <:  int -> int -> t -> unit"]

let main x data t = if t = Empty then assert (height (add x data t) > height t)

[@@@assert "typeof(main) <:  int -> int -> t -> unit"]
