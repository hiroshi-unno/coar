(* How many times an example has been pushed through a self-loop clause.

   The resolver can resolve every decided example one step against the
   problem's own clauses and keep the resolvents as examples.  Through a
   self-loop clause [P(x) /\ c -> P(x')] a decided example of [P] yields
   another decided example of [P], which the next round pushes again: a loop
   whose step is total in the direction of the push (a counter decremented
   backwards from an error state, or incremented forwards from the initial one)
   is unrolled one step per round and never stops, every point new.  Each
   example the validator returns starts such a chain, so the examples added per
   round grow with the number of rounds and the example set quadratically,
   whether the points are ground or parametric.

   This module bounds that unrolling.  Each example has a DEPTH: the number of
   self-loop steps that derived it from an example obtained some other way.  An
   example that was never recorded has depth 0.  A step at level [d] resolves
   only from sources of depth exactly [d] and records every example it added at
   depth [d + 1]; levels run from 0 to [bound - 1], so no example of depth
   [bound] is ever a source and each chain contributes at most [bound] examples.

   Contract of [unroll]:
   - the sources of the step at level [d] are the elements of [sources] whose
     recorded depth is [d]; [sources] is fixed for the whole call, so an example
     added at one level is not a source at the next level of the same call (at
     most one self-loop step per chain per call);
   - [step] returns the state and the elements it ADDED, i.e. that were not
     present before; each of these is recorded at depth [d + 1] unless it is
     already recorded at a smaller depth, which it keeps (a depth only
     decreases);
   - the depth of an element never exceeds [bound] as a result of this call.
   With [bound_of], the bound is per source: a source [e] is resolved at level
   [d] only when [d < bound_of e], and the levels run to the largest bound any
   source has (and at least to [bound]); an element added at level [d] is
   recorded at [d + 1] as before, so its depth never exceeds the bound of the
   source it was derived from.  Without [bound_of] every source has [bound],
   and the call is the one above step for step.
   The bookkeeping says nothing about which examples a step derives; that is
   the caller's resolution. *)

open Core

type 'k t = ('k, int) Map.Poly.t

let empty : 'k t = Map.Poly.empty
let depth (t : 'k t) k = Option.value ~default:0 (Map.Poly.find t k)

let record (t : 'k t) ~level keys =
  Set.fold keys ~init:t ~f:(fun t k ->
      let d = level + 1 in
      match Map.Poly.find t k with
      | Some d' when d' <= d -> t
      | _ -> Map.Poly.set t ~key:k ~data:d)

(* the number of [sources] the bound withholds: those already at [bound] or
   deeper *)
let withheld ?bound_of ~bound ~key (t : 'k t) sources =
  let bound_of = Option.value bound_of ~default:(fun _ -> bound) in
  Set.count sources ~f:(fun e -> depth t (key e) >= bound_of e)

let unroll ?bound_of ~bound ~key
    ~(step : 's -> 'e Set.Poly.t -> 's * 'e Set.Poly.t) (t : 'k t)
    (sources : 'e Set.Poly.t) (state : 's) =
  let top, below =
    match bound_of with
    | None -> (bound, fun _ _ -> true)
    | Some bound_of ->
        ( Set.fold sources ~init:bound ~f:(fun m e -> max m (bound_of e)),
          fun e level -> level < bound_of e )
  in
  List.fold
    (List.range 0 (max top 0))
    ~init:(state, t)
    ~f:(fun (state, t') level ->
      let srcs =
        Set.filter sources ~f:(fun e ->
            depth t (key e) = level && below e level)
      in
      if Set.is_empty srcs then (state, t')
      else
        let state, added = step state srcs in
        (state, record t' ~level (Set.Poly.map added ~f:key)))
