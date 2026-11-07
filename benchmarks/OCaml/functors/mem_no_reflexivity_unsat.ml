(* The unsat twin of mem_reflexive_sat.ml: without the reflexivity contract,
   a module whose eq is never true makes the singleton membership fail.
   expected: unsat *)
module type EQ = sig
  type t
  val eq : t -> t -> bool
end

module Mem (X : EQ) = struct
  let rec mem x l = match l with
    | [] -> false
    | y :: ys -> if X.eq x y then true else mem x ys
  let main x = assert (mem x [x])

  [@@@assert "typeof(main) <: t -> unit"]
end
