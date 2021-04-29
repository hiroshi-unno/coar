(* 
FN_max(x, y, z) == max(x, y) = z

specification of max(x, y) is:
max(x, y) >= x /\ max(x, y) >= y /\ (max(x, y) = x \/ max(x, y) = y)

encode max into function predicate FN_max:
FN(x, y, z) => z >= x /\ z >= y.
FN(x, y, z) /\ z <> x /\ z <> y => false.

possible solution is:
max(x, y) = ITE (x >= y, x, y)
*)

z >= x :- FN_max(x,y,z).
z >= y :- FN_max(x,y,z).
bot :- FN_max(x,y,z), z <> x, z <> y.
