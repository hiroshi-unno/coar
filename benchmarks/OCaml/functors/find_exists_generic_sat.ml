(* A functor whose specification states an existential over an unknown: for
   every element type t, if find answers true on a list then some element
   satisfies the closure's refinement pp.  The element type is a universally
   quantified sort and the existential's witness is a functional predicate,
   so the problem is dependency-quantified with an existential
   (DQpfwCSP).
   expected: sat *)
module type ELT = sig
  type t
end

module Find (X : ELT) = struct
  let rec find p l = match l with
    | [] -> false
    | x :: xs -> if p x then true else find p xs

  [@@@assert "typeof(find) <: (p:(x:t) -> {b:bool | b = pp(x)}) -> (l:t list) -> {r:bool | r = true => _exists y:t. pp(y)}"]
end
