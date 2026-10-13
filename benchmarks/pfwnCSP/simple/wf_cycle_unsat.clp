(* WF: the relation is symmetric (x -> -x -> x), so no well-founded solution; unsat *)
WF_R(x, y) :- x > 0, y = 0 - x.
WF_R(x, y) :- x < 0, y = 0 - x.
