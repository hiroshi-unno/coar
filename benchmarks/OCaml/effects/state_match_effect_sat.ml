(* A state handler written with OCaml 5.3's effect cases in a match
   ([match e with v -> ... | effect Op x, k -> ...]) against the Effect
   module itself; it mirrors popl24/arm/state-SAT.ml, which declares the
   effect interface by hand.  The ghost [ctx] arguments of the operations
   carry the context the refinement annotations mention. *)

type _ Effect.t +=
  | Lookup : int(*ctx*) -> int Effect.t
  | Update : int(*ctx*) * int -> unit Effect.t

(* from Andrej Bauer and Matija Pretnar. Programming with algebraic effects and handlers. 2015. *)

let[@annot_MB "
  int -> (unit -> ({Lookup: s1, Update: s2} |> int / s => s)) -> int
"] state x (main : unit -> int) =
  (match main () with
   | y -> (fun s -> y)
   | effect (Lookup ctx), k ->
       fun (s : int) -> (Effect.Deep.continue k s s)[@annot "{z: int | z = ctx + s}"]
   | effect (Update (ctx2, s')), k ->
       fun (_s : int) -> (Effect.Deep.continue k () s')[@annot "{z: int | z = ctx2 + 1 + s'}"])
  x


(*****************)

(* from https://github.com/daanx/effect-bench/blob/main/src/mstate.ml *)

let main init =
  state init (fun () ->
    let rec counter c =
      let i = Effect.perform (Lookup c(*dummy*)) in
      if i = 0 then c
      else (Effect.perform (Update (c(*dummy*), i - 1)); counter (c + 1))
    in
    counter 0
  )

[@@@assert "typeof(main) <: (init: {z: int | z >= 0}) -> {z: int | z = init}"]
