(* [nondet_int ()] is an arbitrary integer.  The program as published wrote
   [Random.int 0] for it, the convention of the MoCHi-style benchmarks; in
   OCaml (and in RCaml) [Random.int 0] returns no value, under which [randpos]
   would never return and the assertion would hold vacuously. *)
external nondet_int : unit -> int = "unknown"
[@@@rtype "nondet_int::unit -> int"]

let rec randpos (x:int) =
  let n = nondet_int () in
  if n > 0 then n else randpos x

let rec sum_fun f n =
  if n = 0 then f 0
  else f n + sum_fun f (n - 1)

let main n = assert (sum_fun randpos n > 0)
