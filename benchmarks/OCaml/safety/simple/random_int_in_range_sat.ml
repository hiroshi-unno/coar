(* [Random.int n] is a value in [0, n). *)
let main n = if n > 0 then
    let r = Random.int n in
    assert (0 <= r && r < n)

[@@@assert "typeof(main) <: int -> unit"]
