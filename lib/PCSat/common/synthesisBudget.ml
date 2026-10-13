open Core

(* The Z3 budget of the template synthesizer's query, in milliseconds, and
   how it moves between one query and the next.

   A synthesis query that times out answers "nothing learnt, every predicate
   labelled TimeOut".  Every template module ignores that label, so the shape
   stays as it was; the caller then regenerates the templates (fresh parameter
   names, the same shape, the same examples) and renews every solver instance,
   and renewal puts the configured budget back.  So, left alone, the doubling
   done at the timeout is never read, and the same query is asked again at the
   same budget until the run ends.

   [keep] (the [keep_timeout_budget_across_rebuild] switch) lets the doubled
   budget survive exactly that rebuild, capped so that one round cannot take
   the whole run.  Any other rebuild -- a changed shape, new qualifiers, a new
   call with new examples -- returns to the configured budget.

   All three functions are total and leave a [None] budget (no Z3 timeout) as
   [None]. *)

type rebuild_reason =
  | Timeout_only
      (** the previous synthesis query timed out and nothing else changed *)
  | Other  (** anything else: shape, qualifiers or examples may have changed *)

(* The cap: the stated maximum, or four times the configured budget when none
   is stated, and never below the configured budget itself. *)
let cap_of ~configured ~max_timeout =
  match configured with
  | None -> None
  | Some c ->
      let m = match max_timeout with Some m -> m | None -> 4 * c in
      Some (Int.max c m)

(* The budget after a timeout.  With [keep] off this is the doubling as it has
   always been written, uncapped (it is reset before it is read). *)
let after_timeout ~keep ~cap current =
  match current with
  | None -> None
  | Some x -> (
      let doubled = x * 2 in
      if not keep then Some doubled
      else
        match cap with
        | Some c -> Some (Int.min doubled c)
        | None -> Some doubled)

(* The budget a renewed solver instance starts with. *)
let on_rebuild ~keep ~configured ~cap ~current reason =
  match (keep, reason) with
  | true, Timeout_only -> (
      match (current, cap) with
      | Some x, Some c -> Some (Int.min x c)
      | _ -> current)
  | _ -> configured

(* Asking the synthesis query again, unchanged, after a timeout
   ([reask_on_timeout_without_rebuild]).

   Contract: [ask ~again] asks one question; [ask ~again:false] is the first
   ask and [ask ~again:true] asks exactly the same question again -- the same
   solver, the same assertions, the same temporary constraints -- so the
   candidates it admits are the same, and only the budget it is asked under
   may differ.  [budget ()] reads that budget.  The first ask is made once.
   A re-ask is made when [reask] is on, the last answer satisfies
   [timeout_only] (a timeout that taught nothing), the last ask raised the
   budget (the doubling at a timeout, capped: a budget already at its cap, or
   an answer that is not a timeout, leaves it where it was) and [expired ()]
   is false.  Otherwise the last answer is returned and the caller goes on
   as it would have, with the budget the last ask left.  So the number of
   re-asks is bounded by the doublings that fit under the cap, and [reask]
   off makes exactly one ask, the behaviour before the switch.

   Why: a timeout labels every predicate [TimeOut], which no template module
   reads, so the rebuild that follows regenerates the same templates (fresh
   parameter names) and the same example constraints -- 11 to 40 s per round
   on large array inputs -- only to ask the same question, at the configured
   budget unless [keep_timeout_budget_across_rebuild] is on. *)
let ask_reasking ~reask ~timeout_only ~budget ~expired ask =
  let raised before after =
    match (before, after) with
    | Some b, Some a -> a > b
    | _ -> false
  in
  let rec go ~again =
    let before = budget () in
    let r = ask ~again in
    if reask && timeout_only r && raised before (budget ()) && not (expired ())
    then go ~again:true
    else r
  in
  go ~again:false

(* The blame a failed round grows its shape from, when the qualifier-learning
   attempts all came back without a qualifier.  [last] is the last attempt's
   label map (or the union of all attempts', as configured) and [earlier] the
   maps seen before it, newest first, ending with the core of the failed
   candidate search itself.  Contract: with [prefer_informative] off, [last];
   on, the first of [last :: earlier] for which [informative] holds, and
   [last] when none does.  So the result is always one of the given maps, and
   it differs from [last] only when [last] is not informative.

   Why: a learning attempt that times out labels every predicate [TimeOut],
   which no template module acts on, and when it is the last attempt its map
   replaces the cores the earlier attempts and the candidate search found.
   The shape then never grows: the round rebuilds the same templates, the
   candidate search is unsatisfiable again, the same attempt times out again,
   and the run ends inside that cycle.  Growing from the latest core that did
   blame something is what the round would have done had that attempt not
   been tried; which shape is searched is a search policy, so any choice among
   the maps admits only candidates the template family admits. *)
let blame_after_learning ~prefer_informative ~informative ~last ~earlier =
  if not prefer_informative then last
  else
    match List.find (last :: earlier) ~f:informative with
    | Some m -> m
    | None -> last
