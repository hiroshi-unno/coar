(* Regular Tree Automata *)

open Core
open Common.Ext

(** Tree automata *)

type ('lab, 'sym) body =
  | Leaf
  | Label of 'sym * 'lab * 'lab
  | Alter of ('lab, 'sym) body * ('lab, 'sym) body
  | Emp

let rec pr_body pr_id ppf = function
  | Leaf -> Format.fprintf ppf "()"
  | Label (id1, id2, id3) ->
      Format.fprintf ppf "%a(%a, %a)" pr_id id1 pr_id id2 pr_id id3
  | Alter (u1, u2) ->
      Format.fprintf ppf "(%a | %a)" (pr_body pr_id) u1 (pr_body pr_id) u2
  | Emp -> ()

let rec rename_body rn = function
  | Leaf -> Leaf
  | Label (id1, id2, id3) ->
      Label
        ( id1,
          (match List.Assoc.find ~equal:Stdlib.( = ) rn id2 with
          | Some r -> r
          | None -> id2),
          match List.Assoc.find ~equal:Stdlib.( = ) rn id3 with
          | Some r -> r
          | None -> id3 )
  | Alter (u1, u2) -> Alter (rename_body rn u1, rename_body rn u2)
  | Emp -> Emp

(** [canonize_body u] flattens the alternatives of [u] into one sorted,
    duplicate-free list and rebuilds a left-nested [Alter] from it; an [Emp]
    alternative, at any depth, is dropped.  The result accepts the same trees
    as [u], and two bodies that differ only in the order, nesting or
    repetition of their alternatives canonize to the same value.  Both matter
    downstream: [minimize] compares bodies structurally, so a non-canonical
    body keeps apart states that should merge, and an [Emp] left inside an
    [Alter] makes [tta_body_of] fail.  Each element of the flattening is the
    matched subterm itself, not [u].  Raises [Failure] when every alternative
    is [Emp]. *)
let canonize_body u =
  let rec aux = function
    | (Leaf | Label (_, _, _)) as u' -> [ u' ]
    | Alter (u1, u2) ->
        let x = aux u1 @ aux u2 in
        let x' = List.dedup_keep_last x in
        (*let _ = assert (x = x') in*)
        x'
    | Emp -> []
  in
  match List.sort ~compare:Stdlib.compare @@ aux u with
  | [] -> failwith "canonize_body"
  | [ x ] -> x
  | x :: xs -> List.fold_left ~init:x xs ~f:(fun x y -> Alter (x, y))

let rec next_ids_body = function
  | Leaf -> []
  | Label (_id1, id2, id3) -> [ id2; id3 ]
  | Alter (u1, u2) ->
      (*List.dedup_keep_last*) next_ids_body u1 @ next_ids_body u2
  | Emp -> []

let rec tta_body_of (body : ('lab, 'sym) body) : TTA.body =
  match body with
  | Leaf -> [ ("leaf", []) ]
  | Label (id1, id2, id3) -> [ (id1, [ id2; id3 ]) ]
  | Alter (u1, u2) -> tta_body_of u1 @ tta_body_of u2
  | Emp -> failwith "RTA.table_of_body"

type ('lab, 'sym) trs = ('lab, ('lab, 'sym) body) List.Assoc.t

let pr pr_id ppf (trs : ('lab, 'sym) trs) =
  List.iter trs ~f:(fun (id, u) ->
      Format.fprintf ppf "%a -> %a.@\n" pr_id id (pr_body pr_id) u)

(** [minimize_with_merges trs] merges two states whenever their bodies
    coincide once the two are identified, repeatedly to a fixed point, and
    returns the remaining transitions together with the merges made: every
    state of [trs] that no longer has transitions is paired with the state
    that now stands for it (never with another merged state).  Of two merged
    states the one listed earlier survives, so the result keeps the order of
    [trs] restricted to the survivors, and a state that precedes every state
    it is equivalent to is never merged away.  Merging only identifies states
    whose transitions agree, so every surviving state accepts the language it
    accepted in [trs], and a merged state the language of its stand-in. *)
let minimize_with_merges (trs : ('lab, 'sym) trs) =
  let rec f nece merges = function
    | [] -> (nece, merges)
    | (id, u) :: rs -> (
        match
          List.find nece ~f:(fun (id', u') ->
              Stdlib.(rename_body [ (id, id') ] u = rename_body [ (id, id') ] u'))
        with
        | Some (id', _) ->
            let rn = [ (id, id') ] in
            let merges =
              (id, id')
              :: List.map merges ~f:(fun (x, r) ->
                     (x, if Stdlib.(r = id) then id' else r))
            in
            f
              (List.map nece ~f:(fun (id, u) -> (id, rename_body rn u)))
              merges
              (List.map rs ~f:(fun (id, u) -> (id, rename_body rn u)))
        | None -> f ((id, u) :: nece) merges rs)
  in
  let rec loop trs merges =
    let nece, merges = f [] merges trs in
    let trs' = List.rev nece in
    if List.length trs' < List.length trs then loop trs' merges
    else (trs', merges)
  in
  loop trs []

(** [minimize trs] is the transitions of [minimize_with_merges trs]. *)
let minimize (trs : ('lab, 'sym) trs) = fst (minimize_with_merges trs)

let tta_of (trs : ('lab, 'sym) trs) : TTA.trs =
  List.map trs ~f:(fun (id, u) -> (id, tta_body_of u))
