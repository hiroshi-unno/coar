(* A functor over an equality on an abstract type: when the signature's
   contract makes eq reflexive, every element is a member of the singleton
   list holding it.  The membership test's invariant depends on eq only.
   expected: sat *)
module type EQ = sig
  type t
  val eq : t -> t -> bool
end
[@@contract "(forall ((a t)) (eq a a))"]

module Mem (X : EQ) = struct
  let rec mem x l = match l with
    | [] -> false
    | y :: ys -> if X.eq x y then true else mem x ys
  let main x = assert (mem x [x])

  [@@@assert "typeof(main) <: t -> unit"]
end
