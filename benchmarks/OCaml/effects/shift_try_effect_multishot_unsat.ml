(* Delimited control from a handler written with OCaml 5.3's effect cases
   in a try ([try e with effect Op x, k -> ...]) against the Effect module
   itself; it mirrors popl24/arm/shift-UNSAT.ml, which declares the effect
   interface by hand: the assertion is refuted under the multi-shot reading.

   The continuation is resumed three times.  The translation reads
   continuations as multi-shot, as the calculus it implements does, and the
   verdict is about that reading; OCaml's continuations are one-shot, so the
   compiled program raises [Effect.Continuation_already_resumed] at the
   second resumption and never returns. *)

type _ Effect.t += Shift : ((int -> int) -> int) -> int Effect.t

(* from https://github.com/matijapretnar/eff/blob/master/examples/delimited.eff *)

let[@annot_MB "
  int -> (unit -> ({Shift: s} |> int / int => int)) -> int
"] rec reset_ (_ctx: int) body =
  try body () with
  | effect (Shift f), k -> reset_ _ctx (fun () -> f (Effect.Deep.continue k))

let main n = reset_ n (fun () ->
  let s = Effect.perform (Shift (fun k -> k (k (k n)))) in s * 2 + 1
)
[@@@assert "typeof(main) <: (n:int) -> {z:int|z = 4 * n + 3}"]
