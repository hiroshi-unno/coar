Loopb(10,10,r) :- Loopa(0,0,0,r).
Loopa(x,y,z,r) :- x < 10, Loopa(x+1,y+1,z-2,r).
Loopa(x,y,z,z) :- x >= 10.
Loopb(x-1,y-1,z+2) :- x > 0, Loopb(x,y,z).
z >= 0 :- x <= 0, Loopb(x,y,z).
