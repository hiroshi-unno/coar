(* 
FN_f(x, y, z) == f(x, y) = z

specification of f(x, y) is:
f(x, y) = x => y = 0
x = y => f(2x, 0) = f(0, y)

encode f into function predicate FN_f:
FN_f(x, y, x) => y = 0.
x = y => FN_f(2 * x, 0, z) /\ FN_f(0, y, z).

possible solution is:
f(x, y) = x + 2 * y
*)

FN_f(x,y,x) :- y = 0.
FN_f(0, y, z) :- x = y, FN_f(2 * x, 0, z).
FN_f(2 * x, 0, z) :- x = y, FN_f(0, y, z).
