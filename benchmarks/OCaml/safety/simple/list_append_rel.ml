let rec ( @ ) l1 l2 =
  match l1 with
    [] -> l2
  | hd :: tl -> hd :: (tl @ l2)

let append l1 l2 = (@) l1 l2

(* relational verification *)

let rec length = function
  | [] -> 0
  | _ :: tl -> 1 + length tl

(*
[@@@smtlib2
"(define-fun-rec defined_length ((x mylist)) Int
   (ite ((_ is Nil) x) 0 (+ 1 (defined_length (Cons#1 x)))))
 (set-info defined_length
   (forall ((x mylist)) (or ((_ is Nil) x) (> (defined_length x) 0))))"]
*)

let main l1 l2 = assert (length (append l1 l2) > 0)

[@@@assert "typeof(main) <: (l1:int list) -> (l2:{l:int list | l <> [] }) -> unit"]

let main l1 l2 = assert (length l1 + length l2 = length (append l1 l2))

[@@@assert "typeof(main) <: int list -> int list -> unit"]

let main l1 l2 = assert (length l1 < length (append l1 l2))

[@@@assert "typeof(main) <: int list -> int list -> unit"]

let main l1 l2 = assert (length (append l2 l1) = length (append l1 l2))

[@@@assert "typeof(main) <: int list -> int list -> unit"]


let assoc l1 l2 l3 = assert (append l1 (append l2 l3) = append (append l1 l2) l3)

[@@@assert "typeof(assoc) <: int list -> int list -> int list -> unit"]

let comm l1 l2 = assert (append l2 l1 = append l1 l2)

[@@@assert "typeof(comm) <: int list -> int list -> unit"]

let det l1 l2 l3 =  
  if l2 = l3 then assert (append l1 l2 = append l1 l3)

[@@@assert "typeof(det) <: int list -> int list -> int list -> unit"]
