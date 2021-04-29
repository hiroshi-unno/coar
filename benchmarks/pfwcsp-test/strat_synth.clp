(* possible solution: FN_X1(c,x1) = x1 = -c, FN_X2(c,x2) = x2 = -c - 1 *)
bot :- FN_X1(c,x1), FN_X2(c,x2), x1 <= x2.
bot :- FN_X1(c,x1), FN_X2(c,x2), x1 + c >= 0, x2 + c >= 0, x1 > x2.
bot :- FN_X1(c,x1), FN_X2(c,x2), x1 + c > 0, x2 + c < 0.
