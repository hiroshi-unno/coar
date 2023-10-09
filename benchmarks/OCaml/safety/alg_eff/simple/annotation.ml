let test1 () = 1[@annot_MB "(int / int => int)"]

[@@@assert "typeof(test1) <: unit -> ({z: int | z = 1} / (_forall x. {z:int| z = x}) => int)"]


let test2 () = 1[@annot_MB "(int / int => int)"][@annot_rty "(int / {z: int | z > 10} => {z: int | z > 0})"]

[@@@assert "typeof(test2) <: unit -> (int / {z: int | z = 20} => int)"]
[@@@assert "typeof(test2) <: unit -> (int / {z: int | z = 5} => int)"] (* should be unsat *)


let test3 () =
  let a = 2 in
  1[@annot "{z: int | z = a - 1}"]

[@@@assert "typeof(test3) <: unit -> {z: int | z = 1}"]


let test4 = (fun k -> (k 1: int))[@annot "((y:int) -> {z: int | pp(z, y)}) -> {z: int | pp(z, 1)}"]

[@@@assert "typeof(test4) <: ((y:int) -> {z: int | z = y}) -> {z: int | z = 1}"]


(* let test5 = (fun k -> 3 + k 1)[@annot "((y:int) -> {z: int | pp(z, y)}) -> {z: int | _forall r:int. z = 3 + r && pp(r, 1)}"]

[@@@assert "typeof(test5) <: ((y:int) -> {z: int | z = y}) -> {z: int | z = 4}"] *)
