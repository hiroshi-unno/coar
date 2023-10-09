external shift0 : (('a (*T*) -> 'b (*C1*)) -> 'c (*C2*)) -> 'a (*T*) = "unknown"
external reset : (unit -> 'a (*T*)) -> 'b (*C*) = "unknown"

let[@annot_MB "unit -> (int / bool => bool)"] test1 () = 1


let[@annot_MB "(unit -> (int / int => bool)) -> (int / int => bool)"] test2 body = body ()
let test3 () = test2 (fun () -> shift0 (fun k -> k 1 = 2))
