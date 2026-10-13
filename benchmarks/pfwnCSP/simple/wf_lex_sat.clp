(* WF: needs a lexicographic ranking over (x, x2); sat; a regression input for lexicographic ranking synthesis *)
WF_R(x, y, x2, y2) :- x > 0, y = x - 1, y2 = x2 + 5.
WF_R(x, y, x2, y2) :- x = 0, x2 > 0, y = 100, y2 = x2 - 1.
