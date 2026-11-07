(* An unsat twin of step_run_invariant_sat.ml: the contract states that step
   preserves good but no longer that good holds initially, so a module whose
   initial state is not good makes the assertion fail with no step taken.
   expected: unsat *)
module type STEP = sig
  type t
  val init : t
  val step : t -> t
  val good : t -> bool
end
[@@contract "(forall ((s t)) (=> (good s) (good (step s))))"]

module Run (X : STEP) = struct
  let rec run n s = if n <= 0 then s else run (n - 1) (X.step s)
  let main n = assert (X.good (run n X.init))

  [@@@assert "typeof(main) <: int -> unit"]
end
