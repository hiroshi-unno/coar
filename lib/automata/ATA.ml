(* Alternating Tree Automata *)

open Core
open Common.Ext
open Common.Combinator

type dest = (int * string) list list

let pr_dest ppf (dest : dest) =
  Format.fprintf ppf "%s"
  @@
  if List.is_empty dest then "false"
  else
    String.concat_map_list ~sep:" \\/ " dest ~f:(fun conj ->
        if List.is_empty conj then "true"
        else
          String.concat_map_list ~sep:" /\\ " conj ~f:(fun (i, s) ->
              "(" ^ string_of_int i ^ "," ^ s ^ ")"))
(*List.pr (List.pr (Pair.pr Int.pp pr_id) " /\\ ") " \\/ "*)

type arity = (string, int) List.Assoc.t

let pr_arity pr_id ppf (arity : arity) =
  List.iter arity ~f:(fun (id, ar) ->
      Format.fprintf ppf "%a -> %d.@\n" pr_id id ar)

type pre_trs = (string * (string * dest)) list

let pr_pre ppf (trs : pre_trs) =
  (*List.sort ~compare:(fun (q1, _) (q2, _) -> String.compare q1 q2)*)
  List.iter trs ~f:(fun (q, (a, qss)) ->
      Format.fprintf ppf "%s %s -> %a.@\n" q a pr_dest qss)

let states (trs : pre_trs) =
  List.dedup_keep_last
  @@ List.concat_map trs ~f:(fun (q, (_a, qss)) ->
         q :: List.concat_map qss ~f:(List.map ~f:snd))

type body = (string, dest) Base.List.Assoc.t

let next_ids_body (body : body) =
  List.concat_map body ~f:(snd >> List.concat_map ~f:(List.map ~f:snd))

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

(* [merge_duplicates trs] is [trs] with, for each state, all transitions on
   one terminal joined into one whose formula is the disjunction of theirs
   (the transitions' DNFs concatenated, in order), placed where the first of
   them was; it also answers the [(q, a)] pairs that had more than one
   transition.  The automaton accepts the same trees: a run at a node picks
   one transition for its state and terminal, which is picking one disjunct
   of the joined formula, and [false] (the empty DNF) is the unit of the
   join.  A checker that reads only the first transition for a pair needs
   this form. *)
let merge_duplicates (trs : trs) : trs * (string * string) list =
  let merged = ref [] in
  let trs =
    List.map trs ~f:(fun (q, body) ->
        let rec go = function
          | [] -> []
          | (a, dest) :: rest ->
              let same, others =
                List.partition_tf rest ~f:(fun (a', _) -> String.equal a a')
              in
              if not (List.is_empty same) then merged := (q, a) :: !merged;
              (a, dest @ List.concat_map same ~f:snd) :: go others
        in
        (q, go body))
  in
  (trs, List.rev !merged)

let pr pr_id ppf (trs : trs) =
  List.iter trs ~f:(fun (q, xs) ->
      List.iter xs ~f:(fun (a, qss) ->
          Format.fprintf ppf "%a %a -> %a.@\n" pr_id q pr_id a pr_dest qss))
