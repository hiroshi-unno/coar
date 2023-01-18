let rec coincidence l1 l2 =
  match l1 with
  | [] -> []
  | a :: l1' ->
    begin
      match l2 with
      | [] -> []
      | b :: l2' ->
        if a = b then a :: coincidence l1' l2' else if a < b then coincidence l1' l2 else coincidence l1 l2'
    end
(*
  require : ordered l1 and ordered l2
  ensure : elements (coincidence l1 l2) = (elements l1) /\ (elements l2)
 *)
[@@@assert "typeof(coincidence) <: int list -> int list -> int list"]
