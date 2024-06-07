open Core
open Common.Ext

(** Regular expressions *)

type 'a t =
  | Empty
  | Epsilon
  | Symbol of 'a
  | Concat of 'a t (* must be finite *) * 'a t
  | Alter of 'a t * 'a t
  | Repeat of 'a t
  | RepeatInf of 'a t (* must be non-epsilon *)

let rec match_regex p xs =
  match p with
  | Empty -> false
  | Epsilon -> List.is_empty xs
  | Symbol y -> Stdlib.(xs = [ y ])
  | Concat (q, r) ->
      let rec iter ys zs =
        if match_regex q ys && match_regex r zs then true
        else if List.is_empty zs then false
        else iter (ys @ [ List.hd_exn zs ]) (List.tl_exn zs)
      in
      iter [] xs
  | Alter (q, r) -> match_regex q xs || match_regex r xs
  | Repeat q ->
      let rec iter ys zs =
        if match_regex q ys then
          if List.is_empty zs then true
          else if iter [] zs then true
          else iter (ys @ [ List.hd_exn zs ]) (List.tl_exn zs)
        else if List.is_empty zs then false
        else iter (ys @ [ List.hd_exn zs ]) (List.tl_exn zs)
      in
      iter [] xs
  | RepeatInf _ -> failwith "unimplementedz"

let rec str_of str_of_symbol = function
  | Empty -> "bot"
  | Epsilon -> "eps"
  | Symbol y -> str_of_symbol y
  | Concat (q, r) ->
      sprintf "%s %s"
        (String.paren @@ str_of str_of_symbol q)
        (String.paren @@ str_of str_of_symbol r)
  | Alter (q, r) ->
      String.paren
      @@ sprintf "%s | %s" (str_of str_of_symbol q) (str_of str_of_symbol r)
  | Repeat q -> sprintf "%s*" (String.paren @@ str_of str_of_symbol q)
  | RepeatInf q -> sprintf "%s!" (String.paren @@ str_of str_of_symbol q)

(*
(** @test simple *)
let test () =
  match_regex
    (Repeat (Alter (Concat (Symbol 1, Symbol 2), Symbol 3)))
    [1; 2; 3; 2; 3; 3; 1; 2]
*)
