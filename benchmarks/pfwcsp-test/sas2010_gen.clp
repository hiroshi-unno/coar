(*
I_u(x,y).
J_u(b,x,y,x,10) :- b=0,x <= 10, I_u(x,y).
I_u(z+1,w) :- w <= 1, J_u(b,x,y,z,w).
WF_I(x,y,z+1,w) :- w <= 1, b=0, J_u(b,x,y,z,w).
J_u(b,x,y,z,w-1) :- w > 1, J_u(b,x,y,z,w).
WF_J(z,w,z,w-1) :- w > 1, J_u(b,x,y,z,w).
*)

(*
I_u(x,y).
J_u(x,y,x,10) :- x <= 10, I_u(x,y).
I_u(z+1,w) :- w <= 1, J_u(x,y,z,w).
WF_I(x,y,z+1,w) :- w <= 1, J_u(x,y,z,w).
J_u(x,y,z,w-1) :- w > 1, J_u(x,y,z,w).
WF_J(z,w,z,w-1) :- w > 1, J_u(x,y,z,w).
*)

I_u(x,y).
J_u(x,y,x,2) :- x <= 2, I_u(x,y).
I_u(z+1,w) :- w <= 1, J_u(x,y,z,w).
WF_I(x,y,z+1,w) :- w <= 1, J_u(x,y,z,w).
J_u(x,y,z,w-1) :- w > 1, J_u(x,y,z,w).
(*WF_J(z,w,z,w-1) :- w > 1, J_u(x,y,z,w).*)
