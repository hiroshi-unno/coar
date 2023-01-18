let rec sum x = if x <= 0 then 0 else x + sum (x - 1)

[@@@assert "typeof(sum) <: (x:{ x:int | true }) -> { ret : int | ret > x }"]
[@@@assert "typeof(sum) <: (x:{ x:int | x > 1 }) -> { ret : int | ret > x }"]
[@@@assert "typeof(sum) <: (x:{ x:int | true }) -> { ret : int | ret >= x }"]
