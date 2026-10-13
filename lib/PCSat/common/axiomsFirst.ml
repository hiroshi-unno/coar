(* The order in which the zero-unknown verdict asks a validity question that
   mentions a sequence: the sequence-axiom encoding first, and the native
   question only when that does not prove it.

   Contract of [ask ~enabled ~applies ~prove ~native phi]:
   - [enabled = false] or [applies phi = false]: the result is [native phi],
     and [prove] is not called;
   - otherwise [prove phi] is called first; when it returns [true] the result
     is [`Valid] and [native] is not called, and when it returns [false] the
     result is [native phi].
   So a [`Valid] comes either from [native] or from a proof by [prove], and no
   other answer ever comes from [prove].  When [prove] only returns [true] on a
   proof of [phi] (the axiomatised form proving the clause), the answer
   [ask] returns is one [native] could have returned, and the switch changes
   when an answer is reached, never which one: a caller that reads only
   [`Valid] from these questions, as the zero-unknown ladder does, gains or
   loses time only. *)
let ask ~enabled ~applies ~prove ~native phi =
  if enabled && applies phi && prove phi then `Valid else native phi
