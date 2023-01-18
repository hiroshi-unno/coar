(* 
FN_abs(x, y) == abs(x) = y

specification of abs(x) is:
x >= 0 /\ abs(x) = y => y = x
x < 0 /\ abs(x) = y => y = -x

encode abs into function predicate FN_abs:
x >= 0 /\ FN(x, y) => y = x
x < 0 /\ FN(x, y) => y = -x

possible solution is:
abs(x) = ITE (x >= 0, x, -x)
*)

y = x :- x >= 0, FN_abs(x,y).
y = -x :- x < 0, FN_abs(x,y).