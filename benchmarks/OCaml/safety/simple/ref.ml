let main () =
  let r = ref 0 in
  r := !r + 1;
  !r

[@@@assert "typeof(main) <: unit -> { ret : int | ret >= 0 }"]
[@@@assert "typeof(main) <: unit -> { ret : int | ret = 1 }"]
