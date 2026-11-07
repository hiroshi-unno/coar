// The other direction of ltl_switch_fallthrough_valid.c: y is 5, not the 2 a
// switch without fall-through would leave.
// expected: -p cltl invalid
//@ ltl invariant a: [](AP(x == 1) ==> AP(y == 2));
int x = 0; int y = 0; int c = 1;
int main() { switch (c) { case 0: y = 1; case 1: y = 2; case 2: y = y + 3; break; default: y = 9; } x = 1; while (1) {} return 0; }
