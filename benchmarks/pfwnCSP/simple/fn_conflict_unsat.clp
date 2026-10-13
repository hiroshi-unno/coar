(* FN: two clauses force two values of f(x); unsat by functionality *)
FN_f(x, y) :- y = x + 1.
FN_f(x, y) :- y = x + 2.
