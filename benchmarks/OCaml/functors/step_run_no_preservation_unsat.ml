(* The unsat twin of step_run_invariant_sat.ml: the contract states that good
   holds initially but no longer that step preserves it, so some module
   satisfying the signature (good init, and step leaving good) makes the
   assertion fail after one step.  The functor is not verified.
   expected: unsat *)
module type STEP = sig
  type t
  val init : t
  val step : t -> t
  val good : t -> bool
end
[@@contract "(good init)"]

module Run (X : STEP) = struct
  let rec run n s = if n <= 0 then s else run (n - 1) (X.step s)
  let main n = assert (X.good (run n X.init))

  [@@@assert "typeof(main) <: int -> unit"]
end
