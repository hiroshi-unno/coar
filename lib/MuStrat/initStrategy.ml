(* The initial Skolem strategy of one side of a game, bounded in size.

   Each functional key of a side starts from a set of candidate terms, and a
   clause mentioning several keys is checked against the product of their
   sets.  [bound_candidate_sets ~bound ~default sets] returns [(sets', fired)]:
   - [bound = None]: [sets' = sets] and [fired = false];
   - [bound = Some n] and the product of the set sizes over all keys is at
     most [n]: [sets' = sets] and [fired = false];
   - [bound = Some n] and that product exceeds [n]: every key keeps its first
     component ([params]) and its set becomes [{default params}], and
     [fired = true].
   The keys are never changed.  The product is compared with [n] without being
   formed once it would exceed [n], so it cannot overflow.  The product
   is over the whole side, not per clause, so it over-approximates what any one
   clause multiplies. *)
open Core

let bound_candidate_sets ~bound ~default sets =
  match bound with
  | None -> (sets, false)
  | Some n ->
      (* [None] once the running product is known to exceed [n]: before
         multiplying by [k > 0], [a > n / k] is [a * k > n] without forming
         [a * k] *)
      let exceeds =
        match
          Map.Poly.fold sets ~init:(Some 1) ~f:(fun ~key:_ ~data:(_, ts) acc ->
              match acc with
              | None -> None
              | Some a ->
                  let k = Set.length ts in
                  if k > 0 && a > n / k then None else Some (a * k))
        with
        | None -> true
        | Some product -> product > n
      in
      if not exceeds then (sets, false)
      else
        ( Map.Poly.map sets ~f:(fun (params, _) ->
              (params, Set.Poly.singleton (default params))),
          true )
