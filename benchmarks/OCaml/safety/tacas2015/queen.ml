let make_array n s i = (*assert (i < n);*) s
let update i n a x = a i; let a j = if i=j then x else a j in a

let print_string s = ()
let abs x = if x < 0 then -x else x

let queen(size) =
  let queenArray = make_array size 0 in
  let assign i j (queenArray : int -> int) = update (i) size queenArray j in
  let rec dotsPrint n = if n = 0 then () else begin print_string (); dotsPrint (n-1) end in
  let queenPrint queenArray =
    let rec aux1 row = begin
        if row = size then () else
          let n = queenArray(row) in
    assert (0 <= row && row <= size);
          dotsPrint(n-1); print_string (); dotsPrint(size - n); print_string (); aux1 (row + 1)
      end
    in
    aux1(0); print_string () in
  let test j queenArray =
    let qj = queenArray(j) in
    let rec aux2 i =
      if i < j then
        let qi = queenArray(i) in
        if qi = qj then false else if abs(qj - qi) = j - i then false else aux2 (i+1)
      else true
    in aux2 0
  in
  let rec loop row queenArray =
    let next = queenArray(row) + 1 in
    if next > size then
      let queenArray = assign row 0 queenArray in
      if row = 0 then () else loop (row-1) queenArray
    else
      let queenArray = assign row next queenArray in
      if test row queenArray then
        if (row+1) = size then begin queenPrint queenArray; loop(row) queenArray end else loop(row+1) queenArray
      else loop row queenArray
  in loop(0) queenArray

let main n =
  if n>0 then (queen n; ()) else ()

[@@@assert "typeof(main) <: int -> unit"]
