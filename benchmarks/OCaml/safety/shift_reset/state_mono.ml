external shift : (('a (*T*) -> 'b (*C1*)) -> 'c (*C2*)) -> 'd (*T*) = "unknown"
external reset : (unit -> 'a (*T*)) -> 'b (*C*) = "unknown"

let get () : int = shift(*((int (*T*) -> (int -> int) (*C1*)) -> (int -> int) (*C2*)) -> int (*T*)*)
    (fun k (state:int) -> (k state state : int))
let tick () : unit = shift(*((unit (*T*) -> (int -> int) (*C1*)) -> (int -> int) (*C2*)) -> unit (*T*)*)
    (fun k (state:int) -> (k () (state + 1) : int))

let thunk () =
  tick ();
  tick ();
  let a = get () in
  tick ();
  get () - a

let main () =
  reset(*(unit -> (int -> int) (*T*)) -> (int -> int) (*C*)*)
    (fun () ->
       let result = thunk () in
       fun _state -> result)
    0

[@@@assert "typeof(main) <: unit -> { ret : int | ret = 1 }"]
