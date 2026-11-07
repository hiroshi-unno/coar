(* Standalone metadata for a scalar uniform integral association. This does
   not introduce sampling constraints or certify a solver answer. *)
open Core

module S = LogicOld

type t = {
  integrand : Ident.pvar;
  integral : Ident.pvar;
  integrand_sorts : S.Sort.t list;
  integral_sorts : S.Sort.t list;
  sample_position : int;
  result_position : int;
  surviving_positions : int list;
}

type table = t list

let endpoints pairs =
  Set.Poly.of_list
    (List.concat_map pairs ~f:(fun p -> [ p.integrand; p.integral ]))

let validate p =
  let n = List.length p.integrand_sorts in
  if Ident.pvar_equal p.integrand p.integral then Error "integral endpoints coincide"
  else if n < 2 || p.sample_position < 0 || p.sample_position >= n
          || p.result_position <> n - 1 || p.sample_position = p.result_position
  then Error "invalid sample or scalar result position"
  else if not (S.Term.is_real_sort (List.nth_exn p.integrand_sorts p.sample_position))
          || not (S.Term.is_real_sort (List.nth_exn p.integrand_sorts p.result_position))
  then Error "sample and scalar result must have Real sort"
  else
    let survivors = List.filter (List.init n ~f:Fn.id)
        ~f:(fun i -> i <> p.sample_position) in
    if not (Poly.equal survivors p.surviving_positions) then
      Error "integral argument positions must remove only the sample in order"
    else
      (* Extensible context sorts may contain comparator-bearing sets. An
         exact structural comparison must refuse that unsupported payload,
         rather than turn an invalid metadata boundary into an exception. *)
      match
        try
          Ok (Poly.equal p.integral_sorts
                (List.map survivors ~f:(List.nth_exn p.integrand_sorts)))
        with Invalid_argument msg when String.equal msg "compare: functional value" ->
          Error "unsupported context sort comparison"
      with
      | Error e -> Error e
      | Ok false -> Error "integral signature disagrees with surviving arguments"
      | Ok true -> Ok ()

let validate_table pairs =
  let rec loop seen = function
    | [] -> Ok ()
    | p :: rest -> (
        match validate p with
        | Error _ as e -> e
        | Ok () ->
            if Set.mem seen p.integrand || Set.mem seen p.integral then
              Error "endpoint belongs to more than one integral association"
            else loop (Set.add (Set.add seen p.integrand) p.integral) rest)
  in
  loop Set.Poly.empty pairs

let make ~integrand ~integral ~integrand_sorts ~integral_sorts
    ~sample_position ~result_position ~surviving_positions =
  let p = { integrand; integral; integrand_sorts; integral_sorts;
            sample_position; result_position; surviving_positions } in
  match validate p with Ok () -> Ok p | Error e -> Error e

let add pairs p =
  let next = pairs @ [ p ] in
  match validate_table next with Ok () -> Ok next | Error e -> Error e

(* The caller supplies all occupied predicate names, not just this table's
   endpoints. A partial map is acceptable only for whole associations. *)
let transport ~clone ~occupied ~renaming pairs =
  match validate_table pairs with
  | Error e -> Error e
  | Ok () ->
      let sources = endpoints pairs in
      if not (Set.is_subset (Map.key_set renaming) ~of_:sources) then
        Error "renaming contains an endpoint outside the association table"
      else
        let targets = Map.Poly.data renaming in
        if List.length targets <> Set.length (Set.Poly.of_list targets) then
          Error "endpoint renaming is not injective"
        else
          let forbidden =
            if clone then Set.union occupied sources
            else Set.diff (Set.union occupied sources) (Map.key_set renaming)
          in
          if List.exists targets ~f:(Set.mem forbidden) then
            Error "endpoint target collides with an occupied predicate"
          else
            let rec loop acc = function
              | [] ->
                  let next = if clone then pairs @ List.rev acc else List.rev acc in
                  (match validate_table next with Ok () -> Ok next | Error e -> Error e)
              | p :: rest -> (
                  match Map.Poly.find renaming p.integrand,
                        Map.Poly.find renaming p.integral with
                  | None, None -> loop (if clone then acc else p :: acc) rest
                  | Some integrand, Some integral ->
                      loop ({ p with integrand; integral } :: acc) rest
                  | _ -> Error "both integral endpoints must be transported together")
            in
            loop [] pairs

let clone ~occupied ~renaming pairs = transport ~clone:true ~occupied ~renaming pairs
let rename ~occupied ~renaming pairs = transport ~clone:false ~occupied ~renaming pairs

let refuse_removal ~removed pairs =
  match validate_table pairs with
  | Error e -> Error e
  | Ok () ->
      if Set.are_disjoint removed (endpoints pairs) then Ok pairs
      else Error "integral endpoint removal has no checked transfer rule"

let refuse_argument_erasure ~predicate ~positions pairs =
  match validate_table pairs with
  | Error e -> Error e
  | Ok () ->
      if List.is_empty positions || not (Set.mem (endpoints pairs) predicate) then Ok pairs
      else Error "integral argument erasure has no checked transfer rule"
