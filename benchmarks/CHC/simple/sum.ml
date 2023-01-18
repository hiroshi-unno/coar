let rec sum x = if x <= 0 then 0 else x + sum (x - 1)
let main x = assert (sum x >= x)
