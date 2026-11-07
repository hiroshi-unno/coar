let rec mymod x y =
  if y < 0 then -mymod x (-y)
  else if x < 0 then mymod (x + y) y
  else if x < y then x
  else mymod (x - y) y

let enc x = mymod (x + 3) 26
let dec x = mymod (x - 3) 26

let main x = assert(dec (enc x) = mymod x 26)
