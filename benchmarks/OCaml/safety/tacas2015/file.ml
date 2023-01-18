(*
USED: PLDI2011 as r-file
USED: PEPM2013 as r-file
KEYWORD: resource
*)

let rec loop x : unit = loop ()
let init = 0
let opened = 1
let closed = 2
let ignore = 3
let readit st =
  if st = opened then opened else (if st = ignore then st else assert false)
let read_ x st =
  if x then readit st else st
let closeit st =
  if st = opened then closed else (if st = ignore then st else (loop (); 0))
let close_ x st =
  if x then closeit st else st
let rec f x y st : unit =
  close_ y (close_ x st); f x y (read_ y (read_ x st))
let next st = if st=init then opened else ignore
let g b3 x st = if b3 > 0 then f x true (next st) else f x false st
let main b2 b3 = (if b2 > 0 then g b3 true opened else g b3 false init); ()

[@@@assert "typeof(main) <: int -> int -> unit"]
