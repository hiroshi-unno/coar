// A break in a loop inside a case leaves the loop, not the switch: y reaches 2,
// the case adds 1 and its own break leaves the switch, so y == 3.
// expected: -p cltl valid
//@ ltl invariant a: [](AP(x == 1) ==> AP(y == 3));
int x = 0; int y = 0; int c = 0;
int main() { switch (c) { case 0: while (1) { y = y + 1; if (y == 2) break; } y = y + 1; break; case 1: y = 7; } x = 1; while (1) {} return 0; }
