open Core

let rec parse clauses in_channel  =
  try 
    match In_channel.input_line_exn in_channel with
    |line ->
      String.split line ~on:' '
      |> List.filter ~f:(Stdlib.(<>) "")
      |> function
      | [] | "c" :: _ | "p" :: _ ->
        parse clauses in_channel
      | "%" :: _ ->
        let rec exhaust () =
          try
            ignore @@ In_channel.input_line_exn in_channel;
            exhaust ()
          with End_of_file -> () in
        exhaust (); clauses
      | literals ->
        let literals =
          match List.rev literals with
          | "0" :: literals' -> literals'
          | _ -> failwith "clause must end with 0" in
        let clause =
          List.partition_tf ~f:(fun literal ->
              Stdlib.(=) (String.get literal 0) '-') literals
          |> fun (negatives, positives) ->
          (List.map ~f:(fun literal ->
               String.sub literal ~pos:1 ~len:(String.length literal - 1)) negatives, positives) in
        parse (clause::clauses) in_channel
  with End_of_file -> clauses

let from_dimacs_file file =
  file
  |> In_channel.create ~binary:false
  |> parse []
  |> Problem.of_list
