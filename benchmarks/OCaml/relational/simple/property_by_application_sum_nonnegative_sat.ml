(* A property stated by application ([@@@property]): every value [sum n]
   returns is non-negative.  The equation [sum n = r] in the premise says that
   [sum n] can evaluate to [r]; RCaml replaces it by its own predicate for
   the graph of [sum].  Expected: sat. *)
let rec sum n = if n <= 0 then 0 else n + sum (n - 1)

[@@@property "forall n r. sum n = r => r >= 0"]
