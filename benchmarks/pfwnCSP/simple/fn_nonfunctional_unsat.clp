(* FN: f(x) = x + 1 and, for x > 5, f(x) = 6 -- not functional; unsat *)
FN_f(x, y) :- y = x + 1.
FN_f(x, y) :- x > 5, y = 6.
