open Core
open Common.Ext

type quant = (string list, string list * string list option) Either.t

let rec exhaust inp =
  try
    ignore @@ inp ();
    exhaust inp
  with End_of_file -> ()

let elim_last_zero cl line =
  match List.rest_last_opt cl with
  | None -> failwith @@ "each line must end with 0: " ^ line
  | Some (literals, last) ->
      if String.(last = "0") then literals
      else failwith @@ "each line must end with 0: " ^ line

let rec parse ?(no_quant = false) uqbs quants clauses inp =
  try
    match inp () with
    | line -> (
        String.split line ~on:' ' |> List.filter ~f:(Stdlib.( <> ) "")
        |> function
        | [] | "c" :: _ | "p" :: _ -> parse ~no_quant uqbs quants clauses inp
        | "%" :: _ ->
            exhaust inp;
            raise End_of_file
        | "a" :: ns ->
            let ns = elim_last_zero ns line in
            if no_quant then failwith @@ "quantifiers not allowed: " ^ line
            else if List.exists ns ~f:(fun l -> Stdlib.(String.get l 0 = '-'))
            then failwith @@ "illegal quantification: " ^ line
            else parse ~no_quant (ns @ uqbs) (First ns :: quants) clauses inp
        | "e" :: ns ->
            let ns = elim_last_zero ns line in
            if no_quant then failwith @@ "quantifiers not allowed: " ^ line
            else if List.exists ns ~f:(fun l -> Stdlib.(String.get l 0 = '-'))
            then failwith @@ "illegal quantification: " ^ line
            else
              parse ~no_quant uqbs
                (Second (ns, None (*Some uqbs*)) :: quants)
                clauses inp
        | "d" :: n :: ns ->
            let ns = elim_last_zero ns line in
            if no_quant then failwith @@ "quantifiers not allowed: " ^ line
            else if
              (not @@ List.is_empty @@ List.diff ns uqbs)
              || List.exists (n :: ns) ~f:(fun l ->
                     Stdlib.(String.get l 0 = '-'))
            then failwith @@ "illegal dependency quantification: " ^ line
            else
              parse ~no_quant uqbs
                (Second ([ n ], Some ns) :: quants)
                clauses inp
        | ns ->
            let clause =
              elim_last_zero ns line
              |> List.partition_tf ~f:(fun literal ->
                     Stdlib.(String.get literal 0 = '-'))
              |> fun (negatives, positives) ->
              ( List.map negatives ~f:(fun literal ->
                    String.sub literal ~pos:1 ~len:(String.length literal - 1)),
                positives )
            in
            parse ~no_quant:true uqbs quants (clause :: clauses) inp)
  with End_of_file -> (List.rev quants, List.rev clauses)
