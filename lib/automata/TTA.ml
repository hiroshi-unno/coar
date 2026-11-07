(* Trivial Tree Automata *)

open Core
open Common.Ext

type dest = string list

let pr_dest ppf (dest : dest) =
  Format.fprintf ppf "%s" @@ String.concat ~sep:" " dest
(*List.pr pr_id " "*)

type pre_trs = (string * (string * dest)) list

let pr_pre ppf (trs : pre_trs) =
  (*List.sort ~compare:(fun (q1, _) (q2, _) -> String.compare q1 q2)*)
  List.iter trs ~f:(fun (q, (a, qs)) ->
      Format.fprintf ppf "%s %s -> %a.@\n" q a pr_dest qs)

let states (trs : pre_trs) =
  List.dedup_keep_last @@ List.concat_map trs ~f:(fun (q, (_a, qs)) -> q :: qs)

(* [add_br_transitions ~br trs] gives every state [q] the transition
   [q br -> q q], for the terminal [br] that marks a nondeterministic branch;
   [br] must be a terminal [trs] does not read. *)
let add_br_transitions ~br (trs : pre_trs) =
  trs @ List.map (states trs) ~f:(fun q -> (q, (br, [ q; q ])))

(* [add_success_transitions ~success trs] lets every state accept the
   nullary terminal [success], which [trs] must not read. *)
let add_success_transitions ~success (trs : pre_trs) =
  trs @ List.map (states trs) ~f:(fun q -> (q, (success, [])))

let add_check_transitions (trs : pre_trs) cs =
  trs
  @ List.concat_map (states trs) ~f:(fun q ->
        List.map cs ~f:(fun q' -> (q, ("check__" ^ q', [ q' ]))))

(* A node labelled [prefix ^ q'] has two children: an argument handed to an
   unknown function of an EHMTT's main type, which must be accepted from
   [q'], and the function's result, which continues the tree in place of the
   node.  [add_arg_check_transitions ~prefix trs qs'] adds, for every state
   [q] of [trs] and every [q'] of [qs'], the transition reading such a node
   from [q] into [q'] for the first child and [q] for the second; the
   transitions already in [trs] are kept, first.  [prefix ^ q'] must be a
   terminal [trs] does not read. *)
let add_arg_check_transitions ~prefix (trs : pre_trs) qs' =
  trs
  @ List.concat_map (states trs) ~f:(fun q ->
        List.map qs' ~f:(fun q' -> (q, (prefix ^ q', [ q'; q ]))))

type body = (string, dest) Base.List.Assoc.t

let next_ids_body (body : body) = List.concat_map body ~f:snd

type trs = (string, body) Base.List.Assoc.t

let rec make (trs : pre_trs) : trs =
  match trs with
  | [] -> []
  | (id, x) :: xs' ->
      let t, f =
        List.partition_map xs' ~f:(fun (id', x') ->
            if Stdlib.(id = id') then First x' else Second (id', x'))
      in
      (id, x :: t) :: make f

(* [nondeterministic_pair trs] is the first [(q, a)] for which state [q]
   has two transitions on terminal [a] -- the first such state in the order
   of [trs], and of its terminals the one whose second transition comes
   first -- and
   [None] when [trs] is deterministic (a run is then determined by the tree
   it reads).  [make] groups the transitions by state, so a state occurs
   once in [trs]. *)
let nondeterministic_pair (trs : trs) =
  let rec second_occurrence seen = function
    | [] -> None
    | (a, _) :: rest ->
        if List.mem seen a ~equal:String.equal then Some a
        else second_occurrence (a :: seen) rest
  in
  List.find_map trs ~f:(fun (q, body) ->
      Option.map (second_occurrence [] body) ~f:(fun a -> (q, a)))

let pr pr_id ppf (trs : trs) =
  List.iter trs ~f:(fun (q, xs) ->
      List.iter xs ~f:(fun (a, qs) ->
          Format.fprintf ppf "%a %a -> %a.@\n" pr_id q pr_id a pr_dest qs))
