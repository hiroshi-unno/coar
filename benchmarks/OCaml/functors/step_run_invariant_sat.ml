(* A functor verified once against a refinement-typed signature: for every
   module X with an abstract type t, a start state, a step function and a
   predicate good such that good holds initially and is preserved by step,
   running the step any number of times ends in a good state.  The loop
   invariant of [run] may depend only on X's members (good s is one).
   expected: sat *)
module type STEP = sig
  type t
  val init : t
  val step : t -> t
  val good : t -> bool
end
[@@contract "(and (good init) (forall ((s t)) (=> (good s) (good (step s)))))"]

module Run (X : STEP) = struct
  let rec run n s = if n <= 0 then s else run (n - 1) (X.step s)
  let main n = assert (X.good (run n X.init))

  [@@@assert "typeof(main) <: int -> unit"]
end
