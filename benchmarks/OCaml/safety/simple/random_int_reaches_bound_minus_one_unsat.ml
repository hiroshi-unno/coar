(* [Random.int n] can return [n - 1]. *)
let main n = if n > 1 then
    let r = Random.int n in
    assert (r < n - 1)

[@@@assert "typeof(main) <: int -> unit"]
