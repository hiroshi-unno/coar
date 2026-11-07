// switch with fall-through: c == 1 enters at case 1, falls into case 2 and
// breaks there, so y = 2 + 3 = 5 and default is not run.
// expected: -p cltl valid
//@ ltl invariant a: [](AP(x == 1) ==> AP(y == 5));
int x = 0; int y = 0; int c = 1;
int main() { switch (c) { case 0: y = 1; case 1: y = 2; case 2: y = y + 3; break; default: y = 9; } x = 1; while (1) {} return 0; }
