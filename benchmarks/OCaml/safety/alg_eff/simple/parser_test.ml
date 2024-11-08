let rec sum () x = if x <= 0 then 0 else x + sum () (x - 1)

[@@@assert "typeof(sum) <: unit -> ((x:{ x:int | true }) -> { ret : int | ret > x } / _)"]
[@@@assert "typeof(sum) <: unit -> ({} |> (x:{ x:int | true }) -> { ret : int | ret > x } / _)"]
[@@@assert "typeof(sum) <: unit -> ({} |> ((x:{ x:int | true }) -> { ret : int | ret > x } ) / _)"]
[@@@assert "typeof(sum) <: unit -> ({Return:{a:int|a>0}, Op1:{b:bool|b=true}} |> (x:{ x:int | true }) -> { ret : int | ret > x } / _)"]
[@@@assert "typeof(sum) <: unit -> ({Return : { a:int | true }, Op1 : { b:bool | true }} |> ((x:{ x:int | true }) -> { ret : int | ret > x }) / (_forall n. { z:int | z>0 }) => { w:bool | false }) "]
[@@@assert "typeof(sum) <: unit -> ({Return : { a:int | true }, Op1 : { b:bool | true }} |> ((x:{ x:int | true }) -> { ret : int | ret > x }) / { z:int | z>0 } => { w:bool | false }) "]
[@@@assert "typeof(sum) <: unit -> ({Op1 : { b:bool | true }} |> (x:{ x:int | true }) -> { ret : int | ret > x } / (_forall n. { z:int | z>0 }) => ({} |> { w:bool | false } / _)) "]
