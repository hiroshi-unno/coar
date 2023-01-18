
let make_array n s i = assert (0 <= i && i < n); s
let update i n a x = a i; let a j = if i=j then x else a j in a

let kmpMatch slen str plen pat =
  let shiftArray0 = make_array plen (-1) in

  let rec loopShift i j shiftArray1 =
    if j = plen then shiftArray1 else
      if not (pat j = pat (i+1)) then
        if (i >= 0) then
          loopShift (shiftArray1 i) j shiftArray1
        else loopShift (-1) (j+1) shiftArray1
      else
        let shiftArray2 = if i+1 < j then update j plen shiftArray1 (i+1) else shiftArray1 in
          loopShift (shiftArray1 j) (j+1) shiftArray2
  in

  let shiftArray3 = loopShift (-1) 1 shiftArray0 in

  let rec loop s p =
    if p < plen then
      if  s < slen then
        if str s = pat p then
          loop (s+1) (p+1)
        else
          if p = 0 then
            loop (s+1) p
          else
            loop s (shiftArray3 (p-1) + 1)
        else (-1)
    else (s - plen)
  in
    loop 0 0

let main n a m b =
  let array1 = make_array n a in
  let array2 = make_array m b in
  if n>0 && m>0 then (kmpMatch n array1 m array2; ()) else ()

[@@@assert "typeof(main) <: int -> int -> int -> int -> unit"]
