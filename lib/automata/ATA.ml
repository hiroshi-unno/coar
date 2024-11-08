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
    String.concat ~sep:" \\/ "
    @@ List.map dest ~f:(fun conj ->
           if List.is_empty conj then "true"
           else
             String.concat ~sep:" /\\ "
             @@ List.map conj ~f:(fun (i, s) ->
                    "(" ^ string_of_int i ^ "," ^ s ^ ")"))
(*List.pr (List.pr (Pair.pr Integer.pr pr_id) " /\\ ") " \\/ "*)

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
  List.unique
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

let pr pr_id ppf (trs : trs) =
  List.iter trs ~f:(fun (q, xs) ->
      List.iter xs ~f:(fun (a, qss) ->
          Format.fprintf ppf "%a %a -> %a.@\n" pr_id q pr_id a pr_dest qss))
