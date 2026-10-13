(* WF: two-piece decrease; sat with a one-piece ranking (x); kind check WF 1 *)
WF_R(x, y) :- x > 0, y = x - 1.
WF_R(x, y) :- x > 100, y = x - 7.
