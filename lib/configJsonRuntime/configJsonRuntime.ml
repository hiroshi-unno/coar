let mutex = Mutex.create ()
let depths : (int, int) Hashtbl.t = Hashtbl.create 8
let active = Atomic.make false

let locked f =
  Mutex.lock mutex;
  Fun.protect f ~finally:(fun () -> Mutex.unlock mutex)

let is_full () =
  if not (Atomic.get active) then false
  else locked (fun () -> Hashtbl.mem depths (Thread.id (Thread.self ())))

let with_full f =
  let id = Thread.id (Thread.self ()) in
  locked (fun () ->
      let depth = Option.value (Hashtbl.find_opt depths id) ~default:0 in
      Hashtbl.replace depths id (depth + 1);
      Atomic.set active true);
  Fun.protect f ~finally:(fun () ->
      locked (fun () ->
          let depth = Hashtbl.find depths id in
          if depth = 1 then Hashtbl.remove depths id
          else Hashtbl.replace depths id (depth - 1);
          Atomic.set active (Hashtbl.length depths <> 0)))
