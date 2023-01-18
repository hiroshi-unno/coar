type term_t = Var of string | Lam of string * term_t | App of term_t * term_t

external gensym : unit -> string = "unknown"
external shift : (('a (*T*) -> 'b (*C1*)) -> 'c (*C2*)) -> 'd (*T*) = "unknown"
external reset : (unit -> 'a (*T*)) -> 'b (*C*) = "unknown"

let rec a_normal term =
  match term with
  | Var x ->
    Var x
  | Lam (x, t) ->
    Lam (x, reset(*(unit -> term_t (*T*)) -> term_t (*C*)*) (fun () -> a_normal t))
  | App (t1, t2) ->
    shift(*((term_t (*T*) -> term_t (*C1*)) -> term_t (*C2*)) -> term_t (*T*) = "unknown"*)
      (fun k ->
         let x = gensym () in
         App (Lam (x, k (Var x)), App (a_normal t1, a_normal t2)))
