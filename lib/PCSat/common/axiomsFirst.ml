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

(* The switch [zero_unknown.axioms.first_after_fallback_proof]: [ask]'s
   [enabled] decided per verdict from what that verdict's earlier questions
   showed.  One value per verdict ([create]); [note] is told how each
   fresh-context question went, and [enabled t ~fresh] is what the next
   question passes to [ask] as [enabled], [fresh] being the configured
   [axioms.first.fresh].

   Contract:
   - [enabled t ~fresh] is [fresh] until [note] has been told, with [on] set,
     of a question that was asked natively, whose native question ran out of
     its budget, and which the sequence-axiom fallback then proved; from then
     on it is [true] for this value ([armed]), and [note] returns [true]
     exactly once, at that question;
   - with [on] false, [enabled t ~fresh] is always [fresh] and [note] never
     returns [true], so the questions are asked exactly as without the
     switch.
   Since [ask] reads only a proof from the axiomatised form whatever
   [enabled] is, the switch changes when an answer is reached, never which
   answer is right. *)
module After_fallback_proof = struct
  type t = { on : bool; mutable armed : bool }

  let create ~on = { on; armed = false }
  let armed t = t.armed
  let enabled t ~fresh = fresh || t.armed

  let note t ~asked_natively ~native_ran_out ~fallback_proved =
    if t.on && (not t.armed) && asked_natively && native_ran_out
       && fallback_proved
    then (
      t.armed <- true;
      true)
    else false
end
