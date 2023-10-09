let rec ( @ ) l1 l2 = match l1 with [] -> l2 | hd :: tl -> hd :: (tl @ l2)

let push (x: unit -> int) q = q := !q @ [x]
let pop_opt (q: (unit -> int) list ref) =
  match !q with
  | [] -> None
  | x :: xs -> q := xs; Some x

let main () =
  let q = ref [] in
  push (fun () -> 1) q;
  push (fun () -> 2) q;
  match pop_opt q with
  | None -> 0
  | Some f -> f ()

[@@@assert "typeof(main) <: unit -> {z: int | z >= 0}"]